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
uint8_t lean_is_class(lean_object*, lean_object*);
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLiteral_beq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
uint8_t l_Lean_getDiag(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
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
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3;
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
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0;
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
static const lean_array_object l_Lean_Meta_LazyDiscrTree_evalNode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_evalNode___redArg___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0 = (const lean_object*)&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1;
static lean_once_cell_t l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_11_);
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
lean_dec_ref(v_t_11_);
v___x_18_ = lean_apply_2(v_k_12_, v_a_16_, v_a_17_);
return v___x_18_;
}
case 2:
{
lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_19_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_a_19_);
lean_dec_ref(v_t_11_);
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
lean_dec_ref(v_t_11_);
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
lean_dec_ref(v_x_177_);
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
lean_dec_ref(v_x_177_);
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
static uint64_t _init_l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0(void){
_start:
{
lean_object* v___x_312_; uint64_t v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1723u);
v___x_313_ = lean_uint64_of_nat(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LazyDiscrTree_Key_hash(lean_object* v_x_314_){
_start:
{
switch(lean_obj_tag(v_x_314_))
{
case 0:
{
lean_object* v_a_315_; lean_object* v_a_316_; uint64_t v___x_317_; uint64_t v___y_319_; 
v_a_315_ = lean_ctor_get(v_x_314_, 0);
v_a_316_ = lean_ctor_get(v_x_314_, 1);
v___x_317_ = 5237ULL;
if (lean_obj_tag(v_a_315_) == 0)
{
uint64_t v___x_323_; 
v___x_323_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0, &l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0);
v___y_319_ = v___x_323_;
goto v___jp_318_;
}
else
{
uint64_t v_hash_324_; 
v_hash_324_ = lean_ctor_get_uint64(v_a_315_, sizeof(void*)*2);
v___y_319_ = v_hash_324_;
goto v___jp_318_;
}
v___jp_318_:
{
uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; 
v___x_320_ = lean_uint64_of_nat(v_a_316_);
v___x_321_ = lean_uint64_mix_hash(v___y_319_, v___x_320_);
v___x_322_ = lean_uint64_mix_hash(v___x_317_, v___x_321_);
return v___x_322_;
}
}
case 1:
{
lean_object* v_a_325_; lean_object* v_a_326_; uint64_t v___x_327_; uint64_t v___x_328_; uint64_t v___x_329_; uint64_t v___x_330_; uint64_t v___x_331_; 
v_a_325_ = lean_ctor_get(v_x_314_, 0);
v_a_326_ = lean_ctor_get(v_x_314_, 1);
v___x_327_ = 3541ULL;
v___x_328_ = l_Lean_instHashableFVarId_hash(v_a_325_);
v___x_329_ = lean_uint64_of_nat(v_a_326_);
v___x_330_ = lean_uint64_mix_hash(v___x_328_, v___x_329_);
v___x_331_ = lean_uint64_mix_hash(v___x_327_, v___x_330_);
return v___x_331_;
}
case 2:
{
lean_object* v_a_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; 
v_a_332_ = lean_ctor_get(v_x_314_, 0);
v___x_333_ = 1879ULL;
v___x_334_ = l_Lean_Literal_hash(v_a_332_);
v___x_335_ = lean_uint64_mix_hash(v___x_333_, v___x_334_);
return v___x_335_;
}
case 3:
{
uint64_t v___x_336_; 
v___x_336_ = 7883ULL;
return v___x_336_;
}
case 4:
{
uint64_t v___x_337_; 
v___x_337_ = 2411ULL;
return v___x_337_;
}
case 5:
{
uint64_t v___x_338_; 
v___x_338_ = 17ULL;
return v___x_338_;
}
default: 
{
lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v_a_341_; uint64_t v___x_342_; uint64_t v___y_344_; 
v_a_339_ = lean_ctor_get(v_x_314_, 0);
v_a_340_ = lean_ctor_get(v_x_314_, 1);
v_a_341_ = lean_ctor_get(v_x_314_, 2);
v___x_342_ = lean_uint64_of_nat(v_a_341_);
if (lean_obj_tag(v_a_339_) == 0)
{
uint64_t v___x_348_; 
v___x_348_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0, &l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Key_hash___closed__0);
v___y_344_ = v___x_348_;
goto v___jp_343_;
}
else
{
uint64_t v_hash_349_; 
v_hash_349_ = lean_ctor_get_uint64(v_a_339_, sizeof(void*)*2);
v___y_344_ = v_hash_349_;
goto v___jp_343_;
}
v___jp_343_:
{
uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v___x_347_; 
v___x_345_ = lean_uint64_of_nat(v_a_340_);
v___x_346_ = lean_uint64_mix_hash(v___y_344_, v___x_345_);
v___x_347_ = lean_uint64_mix_hash(v___x_342_, v___x_346_);
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Key_hash___boxed(lean_object* v_x_350_){
_start:
{
uint64_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_x_350_);
lean_dec(v_x_350_);
v_r_352_ = lean_box_uint64(v_res_351_);
return v_r_352_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_360_ = l_Lean_mkMVar(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0, &l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar___closed__0);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(lean_object* v_a_362_, lean_object* v_i_363_, lean_object* v_infos_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_array_get_size(v_infos_364_);
v___x_371_ = lean_nat_dec_lt(v_i_363_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_isProof(v_a_362_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_372_;
}
else
{
lean_object* v_info_373_; uint8_t v_isInstance_374_; uint8_t v___y_376_; 
v_info_373_ = lean_array_fget_borrowed(v_infos_364_, v_i_363_);
v_isInstance_374_ = lean_ctor_get_uint8(v_info_373_, sizeof(void*)*1 + 4);
if (v_isInstance_374_ == 0)
{
uint8_t v___x_392_; 
v___x_392_ = l_Lean_Meta_ParamInfo_isImplicit(v_info_373_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
v___x_393_ = l_Lean_Meta_ParamInfo_isStrictImplicit(v_info_373_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_isProof(v_a_362_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_394_;
}
else
{
v___y_376_ = v___x_393_;
goto v___jp_375_;
}
}
else
{
v___y_376_ = v___x_371_;
goto v___jp_375_;
}
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref(v_a_362_);
v___x_395_ = lean_box(v___x_371_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
v___jp_375_:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_isType(v_a_362_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_391_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_391_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_391_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_391_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_unbox(v_a_378_);
lean_dec(v_a_378_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = lean_box(v___y_376_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_383_);
v___x_385_ = v___x_380_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = lean_box(v_isInstance_374_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_387_);
v___x_389_ = v___x_380_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg___boxed(lean_object* v_a_397_, lean_object* v_i_398_, lean_object* v_infos_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_a_397_, v_i_398_, v_infos_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec_ref(v_infos_399_);
lean_dec(v_i_398_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(lean_object* v_infos_406_, lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
if (lean_obj_tag(v_x_408_) == 5)
{
lean_object* v_fn_415_; lean_object* v_arg_416_; lean_object* v___x_417_; 
v_fn_415_ = lean_ctor_get(v_x_408_, 0);
lean_inc_ref(v_fn_415_);
v_arg_416_ = lean_ctor_get(v_x_408_, 1);
lean_inc_ref(v_arg_416_);
lean_dec_ref(v_x_408_);
lean_inc_ref(v_arg_416_);
v___x_417_ = l_Lean_Meta_LazyDiscrTree_MatchClone_ignoreArg(v_arg_416_, v_x_407_, v_infos_406_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; uint8_t v___x_419_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref(v___x_417_);
v___x_419_ = lean_unbox(v_a_418_);
lean_dec(v_a_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_sub(v_x_407_, v___x_420_);
lean_dec(v_x_407_);
v___x_422_ = lean_array_push(v_x_409_, v_arg_416_);
v_x_407_ = v___x_421_;
v_x_408_ = v_fn_415_;
v_x_409_ = v___x_422_;
goto _start;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec_ref(v_arg_416_);
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_sub(v_x_407_, v___x_424_);
lean_dec(v_x_407_);
v___x_426_ = l_Lean_Meta_LazyDiscrTree_MatchClone_tmpStar;
v___x_427_ = lean_array_push(v_x_409_, v___x_426_);
v_x_407_ = v___x_425_;
v_x_408_ = v_fn_415_;
v_x_409_ = v___x_427_;
goto _start;
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_arg_416_);
lean_dec_ref(v_fn_415_);
lean_dec_ref(v_x_409_);
lean_dec(v_x_407_);
v_a_429_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_417_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_417_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
else
{
lean_object* v___x_437_; 
lean_dec_ref(v_x_408_);
lean_dec(v_x_407_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v_x_409_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux___boxed(lean_object* v_infos_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_infos_438_, v_x_439_, v_x_440_, v_x_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec_ref(v_infos_438_);
return v_res_447_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(lean_object* v_e_462_){
_start:
{
uint8_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = l_Lean_Expr_isRawNatLit(v_e_462_);
v___x_464_ = 1;
if (v___x_463_ == 0)
{
lean_object* v_f_465_; uint8_t v___x_466_; 
v_f_465_ = l_Lean_Expr_getAppFn(v_e_462_);
v___x_466_ = l_Lean_Expr_isConst(v_f_465_);
if (v___x_466_ == 0)
{
lean_dec_ref(v_f_465_);
lean_dec_ref(v_e_462_);
return v___x_463_;
}
else
{
if (v___x_463_ == 0)
{
lean_object* v_fName_467_; uint8_t v___y_469_; uint8_t v___y_482_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_fName_467_ = l_Lean_Expr_constName_x21(v_f_465_);
lean_dec_ref(v_f_465_);
v___x_490_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_491_ = lean_name_eq(v_fName_467_, v___x_490_);
if (v___x_491_ == 0)
{
v___y_482_ = v___x_491_;
goto v___jp_481_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_492_ = l_Lean_Expr_getAppNumArgs(v_e_462_);
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_dec_eq(v___x_492_, v___x_493_);
lean_dec(v___x_492_);
v___y_482_ = v___x_494_;
goto v___jp_481_;
}
v___jp_468_:
{
if (v___y_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_471_ = lean_name_eq(v_fName_467_, v___x_470_);
lean_dec(v_fName_467_);
if (v___x_471_ == 0)
{
lean_dec_ref(v_e_462_);
if (v___x_471_ == 0)
{
return v___x_471_;
}
else
{
return v___x_464_;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = l_Lean_Expr_getAppNumArgs(v_e_462_);
lean_dec_ref(v_e_462_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_nat_dec_eq(v___x_472_, v___x_473_);
lean_dec(v___x_472_);
if (v___x_474_ == 0)
{
return v___x_474_;
}
else
{
return v___x_464_;
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_fName_467_);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = l_Lean_Expr_getAppNumArgs(v_e_462_);
v___x_477_ = lean_nat_sub(v___x_476_, v___x_475_);
lean_dec(v___x_476_);
v___x_478_ = lean_nat_sub(v___x_477_, v___x_475_);
lean_dec(v___x_477_);
v___x_479_ = l_Lean_Expr_getRevArg_x21(v_e_462_, v___x_478_);
lean_dec_ref(v_e_462_);
v_e_462_ = v___x_479_;
goto _start;
}
}
v___jp_481_:
{
if (v___y_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_484_ = lean_name_eq(v_fName_467_, v___x_483_);
if (v___x_484_ == 0)
{
v___y_469_ = v___x_484_;
goto v___jp_468_;
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_485_ = l_Lean_Expr_getAppNumArgs(v_e_462_);
v___x_486_ = lean_unsigned_to_nat(3u);
v___x_487_ = lean_nat_dec_eq(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
v___y_469_ = v___x_487_;
goto v___jp_468_;
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v_fName_467_);
v___x_488_ = l_Lean_Expr_appArg_x21(v_e_462_);
lean_dec_ref(v_e_462_);
v_e_462_ = v___x_488_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_f_465_);
lean_dec_ref(v_e_462_);
return v___x_463_;
}
}
}
else
{
lean_dec_ref(v_e_462_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___boxed(lean_object* v_e_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_495_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(lean_object* v_e_500_){
_start:
{
uint8_t v___y_502_; lean_object* v_f_505_; 
v_f_505_ = l_Lean_Expr_getAppFn(v_e_500_);
switch(lean_obj_tag(v_f_505_))
{
case 9:
{
lean_object* v_a_506_; 
lean_dec_ref(v_e_500_);
v_a_506_ = lean_ctor_get(v_f_505_, 0);
lean_inc_ref(v_a_506_);
lean_dec_ref(v_f_505_);
if (lean_obj_tag(v_a_506_) == 0)
{
lean_object* v_val_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_val_507_ = lean_ctor_get(v_a_506_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_a_506_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v_a_506_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_val_507_);
lean_dec(v_a_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 1);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_val_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v___x_515_; 
lean_dec_ref(v_a_506_);
v___x_515_ = lean_box(0);
return v___x_515_;
}
}
case 4:
{
lean_object* v_declName_516_; uint8_t v___y_518_; uint8_t v___y_531_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_declName_516_ = lean_ctor_get(v_f_505_, 0);
lean_inc(v_declName_516_);
lean_dec_ref(v_f_505_);
v___x_549_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_550_ = lean_name_eq(v_declName_516_, v___x_549_);
if (v___x_550_ == 0)
{
v___y_531_ = v___x_550_;
goto v___jp_530_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = l_Lean_Expr_getAppNumArgs(v_e_500_);
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = lean_nat_dec_eq(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
v___y_531_ = v___x_553_;
goto v___jp_530_;
}
v___jp_517_:
{
if (v___y_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__2));
v___x_520_ = lean_name_eq(v_declName_516_, v___x_519_);
lean_dec(v_declName_516_);
if (v___x_520_ == 0)
{
lean_dec_ref(v_e_500_);
v___y_502_ = v___x_520_;
goto v___jp_501_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_521_ = l_Lean_Expr_getAppNumArgs(v_e_500_);
lean_dec_ref(v_e_500_);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_nat_dec_eq(v___x_521_, v___x_522_);
lean_dec(v___x_521_);
v___y_502_ = v___x_523_;
goto v___jp_501_;
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_declName_516_);
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = l_Lean_Expr_getAppNumArgs(v_e_500_);
v___x_526_ = lean_nat_sub(v___x_525_, v___x_524_);
lean_dec(v___x_525_);
v___x_527_ = lean_nat_sub(v___x_526_, v___x_524_);
lean_dec(v___x_526_);
v___x_528_ = l_Lean_Expr_getRevArg_x21(v_e_500_, v___x_527_);
lean_dec_ref(v_e_500_);
v_e_500_ = v___x_528_;
goto _start;
}
}
v___jp_530_:
{
if (v___y_531_ == 0)
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__5));
v___x_533_ = lean_name_eq(v_declName_516_, v___x_532_);
if (v___x_533_ == 0)
{
v___y_518_ = v___x_533_;
goto v___jp_517_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = l_Lean_Expr_getAppNumArgs(v_e_500_);
v___x_535_ = lean_unsigned_to_nat(3u);
v___x_536_ = lean_nat_dec_eq(v___x_534_, v___x_535_);
lean_dec(v___x_534_);
v___y_518_ = v___x_536_;
goto v___jp_517_;
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_declName_516_);
v___x_537_ = l_Lean_Expr_appArg_x21(v_e_500_);
lean_dec_ref(v_e_500_);
v___x_538_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v___x_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
return v___x_538_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_548_; 
v_val_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_add(v_val_539_, v___x_543_);
lean_dec(v_val_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_554_; 
lean_dec_ref(v_f_505_);
lean_dec_ref(v_e_500_);
v___x_554_ = lean_box(0);
return v___x_554_;
}
}
v___jp_501_:
{
if (v___y_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_box(0);
return v___x_503_;
}
else
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop___closed__0));
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(lean_object* v_e_555_){
_start:
{
uint8_t v___x_556_; 
lean_inc_ref(v_e_555_);
v___x_556_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v_e_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
lean_dec_ref(v_e_555_);
v___x_557_ = lean_box(0);
return v___x_557_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f_loop(v_e_555_);
if (lean_obj_tag(v___x_558_) == 1)
{
lean_object* v_val_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_val_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_val_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v_val_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v___x_568_; 
lean_dec(v___x_558_);
v___x_568_ = lean_box(0);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(lean_object* v_e_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_577_; 
lean_inc(v_a_575_);
lean_inc_ref(v_a_574_);
lean_inc(v_a_573_);
lean_inc_ref(v_a_572_);
v___x_577_ = lean_whnf(v_e_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_588_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_588_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_588_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_582_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___closed__0));
v___x_583_ = l_Lean_Expr_isConstOf(v_a_578_, v___x_582_);
lean_dec(v_a_578_);
v___x_584_ = lean_box(v___x_583_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_584_);
v___x_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_a_589_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_577_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_577_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType___boxed(lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v_e_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(lean_object* v_fName_617_, lean_object* v_e_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
uint8_t v___y_625_; uint8_t v___y_655_; uint8_t v___y_680_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__6));
v___x_691_ = lean_name_eq(v_fName_617_, v___x_690_);
if (v___x_691_ == 0)
{
v___y_680_ = v___x_691_;
goto v___jp_679_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_692_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_693_ = lean_unsigned_to_nat(2u);
v___x_694_ = lean_nat_dec_eq(v___x_692_, v___x_693_);
lean_dec(v___x_692_);
v___y_680_ = v___x_694_;
goto v___jp_679_;
}
v___jp_624_:
{
if (v___y_625_ == 0)
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral___closed__7));
v___x_627_ = lean_name_eq(v_fName_617_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_box(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_dec_eq(v___x_630_, v___x_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_637_ = lean_nat_sub(v___x_636_, v___x_635_);
lean_dec(v___x_636_);
v___x_638_ = lean_nat_sub(v___x_637_, v___x_635_);
lean_dec(v___x_637_);
v___x_639_ = l_Lean_Expr_getRevArg_x21(v_e_618_, v___x_638_);
v___x_640_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_639_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; uint8_t v___x_642_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
v___x_642_ = lean_unbox(v_a_641_);
lean_dec(v_a_641_);
if (v___x_642_ == 0)
{
return v___x_640_;
}
else
{
lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_652_; 
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v___x_640_, 0);
lean_dec(v_unused_653_);
v___x_644_ = v___x_640_;
v_isShared_645_ = v_isSharedCheck_652_;
goto v_resetjp_643_;
}
else
{
lean_dec(v___x_640_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_652_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_646_ = l_Lean_Expr_appArg_x21(v_e_618_);
v___x_647_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_646_);
v___x_648_ = lean_box(v___x_647_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_648_);
v___x_650_ = v___x_644_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
return v___x_640_;
}
}
}
v___jp_654_:
{
if (v___y_655_ == 0)
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__2));
v___x_657_ = lean_name_eq(v_fName_617_, v___x_656_);
if (v___x_657_ == 0)
{
v___y_625_ = v___x_657_;
goto v___jp_624_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_659_ = lean_unsigned_to_nat(6u);
v___x_660_ = lean_nat_dec_eq(v___x_658_, v___x_659_);
lean_dec(v___x_658_);
v___y_625_ = v___x_660_;
goto v___jp_624_;
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_661_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = lean_nat_sub(v___x_661_, v___x_662_);
lean_dec(v___x_661_);
v___x_664_ = l_Lean_Expr_getRevArg_x21(v_e_618_, v___x_663_);
v___x_665_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatType(v___x_664_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; uint8_t v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
v___x_667_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
if (v___x_667_ == 0)
{
return v___x_665_;
}
else
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_677_; 
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v___x_665_, 0);
lean_dec(v_unused_678_);
v___x_669_ = v___x_665_;
v_isShared_670_ = v_isSharedCheck_677_;
goto v_resetjp_668_;
}
else
{
lean_dec(v___x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_677_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_671_ = l_Lean_Expr_appArg_x21(v_e_618_);
v___x_672_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_671_);
v___x_673_ = lean_box(v___x_672_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_673_);
v___x_675_ = v___x_669_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
return v___x_665_;
}
}
}
v___jp_679_:
{
if (v___y_680_ == 0)
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___closed__5));
v___x_682_ = lean_name_eq(v_fName_617_, v___x_681_);
if (v___x_682_ == 0)
{
v___y_655_ = v___x_682_;
goto v___jp_654_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_683_ = l_Lean_Expr_getAppNumArgs(v_e_618_);
v___x_684_ = lean_unsigned_to_nat(4u);
v___x_685_ = lean_nat_dec_eq(v___x_683_, v___x_684_);
lean_dec(v___x_683_);
v___y_655_ = v___x_685_;
goto v___jp_654_;
}
}
else
{
lean_object* v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = l_Lean_Expr_appArg_x21(v_e_618_);
v___x_687_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNumeral(v___x_686_);
v___x_688_ = lean_box(v___x_687_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset___boxed(lean_object* v_fName_695_, lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_695_, v_e_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec_ref(v_e_696_);
lean_dec(v_fName_695_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(lean_object* v_fName_703_, lean_object* v_e_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_fName_703_, v_e_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar___boxed(lean_object* v_fName_711_, lean_object* v_e_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Meta_LazyDiscrTree_MatchClone_shouldAddAsStar(v_fName_711_, v_e_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec_ref(v_e_712_);
lean_dec(v_fName_711_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(lean_object* v_e_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = l_Lean_Expr_hasLooseBVars(v_e_721_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_e_721_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
else
{
uint8_t v___x_728_; uint8_t v___x_729_; 
v___x_728_ = 0;
v___x_729_ = l_Lean_Expr_isHeadBetaTarget(v_e_721_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref(v_e_721_);
v___x_730_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___closed__0));
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_732_ = l_Lean_Expr_headBeta(v_e_721_);
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0___boxed(lean_object* v_e_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__0(v_e_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(lean_object* v_e_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_e_740_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1___boxed(lean_object* v_e_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___lam__1(v_e_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_750_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = l_Lean_maxRecDepthErrorMessage;
v___x_757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_759_ = l_Lean_MessageData_ofFormat(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_761_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_762_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_763_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_ref_763_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(lean_object* v_x_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___y_777_; lean_object* v_fileName_786_; lean_object* v_fileMap_787_; lean_object* v_options_788_; lean_object* v_currRecDepth_789_; lean_object* v_maxRecDepth_790_; lean_object* v_ref_791_; lean_object* v_currNamespace_792_; lean_object* v_openDecls_793_; lean_object* v_initHeartbeats_794_; lean_object* v_maxHeartbeats_795_; lean_object* v_quotContext_796_; lean_object* v_currMacroScope_797_; uint8_t v_diag_798_; lean_object* v_cancelTk_x3f_799_; uint8_t v_suppressElabErrors_800_; lean_object* v_inheritedTraceOptions_801_; uint8_t v___x_802_; 
v_fileName_786_ = lean_ctor_get(v___y_773_, 0);
lean_inc_ref(v_fileName_786_);
v_fileMap_787_ = lean_ctor_get(v___y_773_, 1);
lean_inc_ref(v_fileMap_787_);
v_options_788_ = lean_ctor_get(v___y_773_, 2);
lean_inc_ref(v_options_788_);
v_currRecDepth_789_ = lean_ctor_get(v___y_773_, 3);
lean_inc(v_currRecDepth_789_);
v_maxRecDepth_790_ = lean_ctor_get(v___y_773_, 4);
lean_inc(v_maxRecDepth_790_);
v_ref_791_ = lean_ctor_get(v___y_773_, 5);
lean_inc(v_ref_791_);
v_currNamespace_792_ = lean_ctor_get(v___y_773_, 6);
lean_inc(v_currNamespace_792_);
v_openDecls_793_ = lean_ctor_get(v___y_773_, 7);
lean_inc(v_openDecls_793_);
v_initHeartbeats_794_ = lean_ctor_get(v___y_773_, 8);
lean_inc(v_initHeartbeats_794_);
v_maxHeartbeats_795_ = lean_ctor_get(v___y_773_, 9);
lean_inc(v_maxHeartbeats_795_);
v_quotContext_796_ = lean_ctor_get(v___y_773_, 10);
lean_inc(v_quotContext_796_);
v_currMacroScope_797_ = lean_ctor_get(v___y_773_, 11);
lean_inc(v_currMacroScope_797_);
v_diag_798_ = lean_ctor_get_uint8(v___y_773_, sizeof(void*)*14);
v_cancelTk_x3f_799_ = lean_ctor_get(v___y_773_, 12);
lean_inc(v_cancelTk_x3f_799_);
v_suppressElabErrors_800_ = lean_ctor_get_uint8(v___y_773_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_801_ = lean_ctor_get(v___y_773_, 13);
lean_inc_ref(v_inheritedTraceOptions_801_);
lean_dec_ref(v___y_773_);
v___x_802_ = lean_nat_dec_eq(v_currRecDepth_789_, v_maxRecDepth_790_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_nat_add(v_currRecDepth_789_, v___x_803_);
lean_dec(v_currRecDepth_789_);
v___x_805_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_805_, 0, v_fileName_786_);
lean_ctor_set(v___x_805_, 1, v_fileMap_787_);
lean_ctor_set(v___x_805_, 2, v_options_788_);
lean_ctor_set(v___x_805_, 3, v___x_804_);
lean_ctor_set(v___x_805_, 4, v_maxRecDepth_790_);
lean_ctor_set(v___x_805_, 5, v_ref_791_);
lean_ctor_set(v___x_805_, 6, v_currNamespace_792_);
lean_ctor_set(v___x_805_, 7, v_openDecls_793_);
lean_ctor_set(v___x_805_, 8, v_initHeartbeats_794_);
lean_ctor_set(v___x_805_, 9, v_maxHeartbeats_795_);
lean_ctor_set(v___x_805_, 10, v_quotContext_796_);
lean_ctor_set(v___x_805_, 11, v_currMacroScope_797_);
lean_ctor_set(v___x_805_, 12, v_cancelTk_x3f_799_);
lean_ctor_set(v___x_805_, 13, v_inheritedTraceOptions_801_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*14, v_diag_798_);
lean_ctor_set_uint8(v___x_805_, sizeof(void*)*14 + 1, v_suppressElabErrors_800_);
lean_inc(v___y_774_);
lean_inc(v___y_772_);
v___x_806_ = lean_apply_4(v_x_771_, v___y_772_, v___x_805_, v___y_774_, lean_box(0));
v___y_777_ = v___x_806_;
goto v___jp_776_;
}
else
{
lean_object* v___x_807_; 
lean_dec_ref(v_inheritedTraceOptions_801_);
lean_dec(v_cancelTk_x3f_799_);
lean_dec(v_currMacroScope_797_);
lean_dec(v_quotContext_796_);
lean_dec(v_maxHeartbeats_795_);
lean_dec(v_initHeartbeats_794_);
lean_dec(v_openDecls_793_);
lean_dec(v_currNamespace_792_);
lean_dec(v_maxRecDepth_790_);
lean_dec(v_currRecDepth_789_);
lean_dec_ref(v_options_788_);
lean_dec_ref(v_fileMap_787_);
lean_dec_ref(v_fileName_786_);
lean_dec_ref(v_x_771_);
v___x_807_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_791_);
v___y_777_ = v___x_807_;
goto v___jp_776_;
}
v___jp_776_:
{
if (lean_obj_tag(v___y_777_) == 0)
{
return v___y_777_;
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_a_778_ = lean_ctor_get(v___y_777_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___y_777_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___y_777_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___y_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_847_, lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
uint8_t v___x_849_; 
v___x_849_ = 0;
return v___x_849_;
}
else
{
lean_object* v_key_850_; lean_object* v_tail_851_; uint8_t v___x_852_; 
v_key_850_ = lean_ctor_get(v_x_848_, 0);
v_tail_851_ = lean_ctor_get(v_x_848_, 2);
v___x_852_ = l_Lean_ExprStructEq_beq(v_key_850_, v_a_847_);
if (v___x_852_ == 0)
{
v_x_848_ = v_tail_851_;
goto _start;
}
else
{
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_854_, lean_object* v_x_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg(v_a_854_, v_x_855_);
lean_dec(v_x_855_);
lean_dec_ref(v_a_854_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
return v_x_858_;
}
else
{
lean_object* v_key_860_; lean_object* v_value_861_; lean_object* v_tail_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_885_; 
v_key_860_ = lean_ctor_get(v_x_859_, 0);
v_value_861_ = lean_ctor_get(v_x_859_, 1);
v_tail_862_ = lean_ctor_get(v_x_859_, 2);
v_isSharedCheck_885_ = !lean_is_exclusive(v_x_859_);
if (v_isSharedCheck_885_ == 0)
{
v___x_864_ = v_x_859_;
v_isShared_865_ = v_isSharedCheck_885_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_tail_862_);
lean_inc(v_value_861_);
lean_inc(v_key_860_);
lean_dec(v_x_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_885_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; uint64_t v___x_867_; uint64_t v___x_868_; uint64_t v___x_869_; uint64_t v_fold_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v___x_873_; size_t v___x_874_; size_t v___x_875_; size_t v___x_876_; size_t v___x_877_; size_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_866_ = lean_array_get_size(v_x_858_);
v___x_867_ = l_Lean_ExprStructEq_hash(v_key_860_);
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
v___x_879_ = lean_array_uget_borrowed(v_x_858_, v___x_878_);
lean_inc(v___x_879_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 2, v___x_879_);
v___x_881_ = v___x_864_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_key_860_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_value_861_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v___x_879_);
v___x_881_ = v_reuseFailAlloc_884_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; 
v___x_882_ = lean_array_uset(v_x_858_, v___x_878_, v___x_881_);
v_x_858_ = v___x_882_;
v_x_859_ = v_tail_862_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_886_, lean_object* v_source_887_, lean_object* v_target_888_){
_start:
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = lean_array_get_size(v_source_887_);
v___x_890_ = lean_nat_dec_lt(v_i_886_, v___x_889_);
if (v___x_890_ == 0)
{
lean_dec_ref(v_source_887_);
lean_dec(v_i_886_);
return v_target_888_;
}
else
{
lean_object* v_es_891_; lean_object* v___x_892_; lean_object* v_source_893_; lean_object* v_target_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_es_891_ = lean_array_fget(v_source_887_, v_i_886_);
v___x_892_ = lean_box(0);
v_source_893_ = lean_array_fset(v_source_887_, v_i_886_, v___x_892_);
v_target_894_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_888_, v_es_891_);
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = lean_nat_add(v_i_886_, v___x_895_);
lean_dec(v_i_886_);
v_i_886_ = v___x_896_;
v_source_887_ = v_source_893_;
v_target_888_ = v_target_894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_nbuckets_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_899_ = lean_array_get_size(v_data_898_);
v___x_900_ = lean_unsigned_to_nat(2u);
v_nbuckets_901_ = lean_nat_mul(v___x_899_, v___x_900_);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_box(0);
v___x_904_ = lean_mk_array(v_nbuckets_901_, v___x_903_);
v___x_905_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_902_, v_data_898_, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_906_, lean_object* v_b_907_, lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
lean_dec(v_b_907_);
lean_dec_ref(v_a_906_);
return v_x_908_;
}
else
{
lean_object* v_key_909_; lean_object* v_value_910_; lean_object* v_tail_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_923_; 
v_key_909_ = lean_ctor_get(v_x_908_, 0);
v_value_910_ = lean_ctor_get(v_x_908_, 1);
v_tail_911_ = lean_ctor_get(v_x_908_, 2);
v_isSharedCheck_923_ = !lean_is_exclusive(v_x_908_);
if (v_isSharedCheck_923_ == 0)
{
v___x_913_ = v_x_908_;
v_isShared_914_ = v_isSharedCheck_923_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_tail_911_);
lean_inc(v_value_910_);
lean_inc(v_key_909_);
lean_dec(v_x_908_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_923_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_ExprStructEq_beq(v_key_909_, v_a_906_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_a_906_, v_b_907_, v_tail_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 2, v___x_916_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_key_909_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_value_910_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
else
{
lean_object* v___x_921_; 
lean_dec(v_value_910_);
lean_dec(v_key_909_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 1, v_b_907_);
lean_ctor_set(v___x_913_, 0, v_a_906_);
v___x_921_ = v___x_913_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_906_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_b_907_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_tail_911_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(lean_object* v_m_924_, lean_object* v_a_925_, lean_object* v_b_926_){
_start:
{
lean_object* v_size_927_; lean_object* v_buckets_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_971_; 
v_size_927_ = lean_ctor_get(v_m_924_, 0);
v_buckets_928_ = lean_ctor_get(v_m_924_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_m_924_);
if (v_isSharedCheck_971_ == 0)
{
v___x_930_ = v_m_924_;
v_isShared_931_ = v_isSharedCheck_971_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_buckets_928_);
lean_inc(v_size_927_);
lean_dec(v_m_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_971_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v_fold_936_; uint64_t v___x_937_; uint64_t v___x_938_; uint64_t v___x_939_; size_t v___x_940_; size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; lean_object* v_bkt_945_; uint8_t v___x_946_; 
v___x_932_ = lean_array_get_size(v_buckets_928_);
v___x_933_ = l_Lean_ExprStructEq_hash(v_a_925_);
v___x_934_ = 32ULL;
v___x_935_ = lean_uint64_shift_right(v___x_933_, v___x_934_);
v_fold_936_ = lean_uint64_xor(v___x_933_, v___x_935_);
v___x_937_ = 16ULL;
v___x_938_ = lean_uint64_shift_right(v_fold_936_, v___x_937_);
v___x_939_ = lean_uint64_xor(v_fold_936_, v___x_938_);
v___x_940_ = lean_uint64_to_usize(v___x_939_);
v___x_941_ = lean_usize_of_nat(v___x_932_);
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_sub(v___x_941_, v___x_942_);
v___x_944_ = lean_usize_land(v___x_940_, v___x_943_);
v_bkt_945_ = lean_array_uget_borrowed(v_buckets_928_, v___x_944_);
v___x_946_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg(v_a_925_, v_bkt_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v_size_x27_948_; lean_object* v___x_949_; lean_object* v_buckets_x27_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_947_ = lean_unsigned_to_nat(1u);
v_size_x27_948_ = lean_nat_add(v_size_927_, v___x_947_);
lean_dec(v_size_927_);
lean_inc(v_bkt_945_);
v___x_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_949_, 0, v_a_925_);
lean_ctor_set(v___x_949_, 1, v_b_926_);
lean_ctor_set(v___x_949_, 2, v_bkt_945_);
v_buckets_x27_950_ = lean_array_uset(v_buckets_928_, v___x_944_, v___x_949_);
v___x_951_ = lean_unsigned_to_nat(4u);
v___x_952_ = lean_nat_mul(v_size_x27_948_, v___x_951_);
v___x_953_ = lean_unsigned_to_nat(3u);
v___x_954_ = lean_nat_div(v___x_952_, v___x_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_array_get_size(v_buckets_x27_950_);
v___x_956_ = lean_nat_dec_le(v___x_954_, v___x_955_);
lean_dec(v___x_954_);
if (v___x_956_ == 0)
{
lean_object* v_val_957_; lean_object* v___x_959_; 
v_val_957_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_950_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v_val_957_);
lean_ctor_set(v___x_930_, 0, v_size_x27_948_);
v___x_959_ = v___x_930_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_size_x27_948_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_val_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
lean_object* v___x_962_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v_buckets_x27_950_);
lean_ctor_set(v___x_930_, 0, v_size_x27_948_);
v___x_962_ = v___x_930_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_size_x27_948_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_buckets_x27_950_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
else
{
lean_object* v___x_964_; lean_object* v_buckets_x27_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
lean_inc(v_bkt_945_);
v___x_964_ = lean_box(0);
v_buckets_x27_965_ = lean_array_uset(v_buckets_928_, v___x_944_, v___x_964_);
v___x_966_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_a_925_, v_b_926_, v_bkt_945_);
v___x_967_ = lean_array_uset(v_buckets_x27_965_, v___x_944_, v___x_966_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_967_);
v___x_969_ = v___x_930_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_size_927_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(lean_object* v_a_972_, lean_object* v_e_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_976_ = lean_st_ref_take(v_a_972_);
v___x_977_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_976_, v_e_973_, v_a_974_);
v___x_978_ = lean_st_ref_set(v_a_972_, v___x_977_);
v___x_979_ = lean_box(0);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed(lean_object* v_a_980_, lean_object* v_e_981_, lean_object* v_a_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2(v_a_980_, v_e_981_, v_a_982_);
lean_dec(v_a_980_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_apply_1(v_x_986_, lean_box(0));
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(v_00_u03b1_992_, v_x_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_997_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_998_; lean_object* v_dummy_999_; 
v___x_998_ = lean_box(0);
v_dummy_999_ = l_Lean_Expr_sort___override(v___x_998_);
return v_dummy_999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(lean_object* v_pre_1000_, lean_object* v_post_1001_, size_t v_sz_1002_, size_t v_i_1003_, lean_object* v_bs_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_usize_dec_lt(v_i_1003_, v_sz_1002_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; 
lean_dec_ref(v_post_1001_);
lean_dec_ref(v_pre_1000_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_bs_1004_);
return v___x_1010_;
}
else
{
lean_object* v_v_1011_; lean_object* v___x_1012_; 
v_v_1011_ = lean_array_uget_borrowed(v_bs_1004_, v_i_1003_);
lean_inc(v_v_1011_);
lean_inc_ref(v_post_1001_);
lean_inc_ref(v_pre_1000_);
v___x_1012_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1000_, v_post_1001_, v_v_1011_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v_bs_x27_1015_; size_t v___x_1016_; size_t v___x_1017_; lean_object* v___x_1018_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = lean_unsigned_to_nat(0u);
v_bs_x27_1015_ = lean_array_uset(v_bs_1004_, v_i_1003_, v___x_1014_);
v___x_1016_ = ((size_t)1ULL);
v___x_1017_ = lean_usize_add(v_i_1003_, v___x_1016_);
v___x_1018_ = lean_array_uset(v_bs_x27_1015_, v_i_1003_, v_a_1013_);
v_i_1003_ = v___x_1017_;
v_bs_1004_ = v___x_1018_;
goto _start;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v_bs_1004_);
lean_dec_ref(v_post_1001_);
lean_dec_ref(v_pre_1000_);
v_a_1020_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1012_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1012_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(lean_object* v_pre_1028_, lean_object* v_post_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
if (lean_obj_tag(v_x_1030_) == 5)
{
lean_object* v_fn_1037_; lean_object* v_arg_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_fn_1037_ = lean_ctor_get(v_x_1030_, 0);
lean_inc_ref(v_fn_1037_);
v_arg_1038_ = lean_ctor_get(v_x_1030_, 1);
lean_inc_ref(v_arg_1038_);
lean_dec_ref(v_x_1030_);
v___x_1039_ = lean_array_set(v_x_1031_, v_x_1032_, v_arg_1038_);
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_sub(v_x_1032_, v___x_1040_);
lean_dec(v_x_1032_);
v_x_1030_ = v_fn_1037_;
v_x_1031_ = v___x_1039_;
v_x_1032_ = v___x_1041_;
goto _start;
}
else
{
lean_object* v___x_1043_; 
lean_dec(v_x_1032_);
lean_inc_ref(v_post_1029_);
lean_inc_ref(v_pre_1028_);
v___x_1043_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1028_, v_post_1029_, v_x_1030_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; size_t v_sz_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
v_sz_1045_ = lean_array_size(v_x_1031_);
v___x_1046_ = ((size_t)0ULL);
lean_inc_ref(v_post_1029_);
lean_inc_ref(v_pre_1028_);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1028_, v_post_1029_, v_sz_1045_, v___x_1046_, v_x_1031_, v___y_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = l_Lean_mkAppN(v_a_1044_, v_a_1048_);
lean_dec(v_a_1048_);
v___x_1050_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1028_, v_post_1029_, v___x_1049_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1050_;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_1044_);
lean_dec_ref(v_post_1029_);
lean_dec_ref(v_pre_1028_);
v_a_1051_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1047_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1047_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_dec_ref(v_x_1031_);
lean_dec_ref(v_post_1029_);
lean_dec_ref(v_pre_1028_);
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(lean_object* v_pre_1059_, lean_object* v_e_1060_, lean_object* v_post_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; uint8_t v___y_1074_; lean_object* v___y_1084_; lean_object* v___y_1085_; uint8_t v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; uint8_t v___y_1089_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; uint8_t v___y_1101_; uint8_t v___y_1102_; lean_object* v___x_1109_; 
lean_inc_ref(v_pre_1059_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc_ref(v_e_1060_);
v___x_1109_ = lean_apply_4(v_pre_1059_, v_e_1060_, v___y_1063_, v___y_1064_, lean_box(0));
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1199_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1199_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1199_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___y_1115_; 
switch(lean_obj_tag(v_a_1110_))
{
case 0:
{
lean_object* v_e_1189_; lean_object* v___x_1191_; 
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_e_1060_);
lean_dec_ref(v_pre_1059_);
v_e_1189_ = lean_ctor_get(v_a_1110_, 0);
lean_inc_ref(v_e_1189_);
lean_dec_ref(v_a_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v_e_1189_);
v___x_1191_ = v___x_1112_;
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
lean_del_object(v___x_1112_);
lean_dec_ref(v_e_1060_);
v_e_1193_ = lean_ctor_get(v_a_1110_, 0);
lean_inc_ref(v_e_1193_);
lean_dec_ref(v_a_1110_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1194_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_e_1193_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref(v___x_1194_);
v___x_1196_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v_a_1195_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1196_;
}
else
{
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1194_;
}
}
default: 
{
lean_object* v_e_x3f_1197_; 
lean_del_object(v___x_1112_);
v_e_x3f_1197_ = lean_ctor_get(v_a_1110_, 0);
lean_inc(v_e_x3f_1197_);
lean_dec_ref(v_a_1110_);
if (lean_obj_tag(v_e_x3f_1197_) == 0)
{
v___y_1115_ = v_e_1060_;
goto v___jp_1114_;
}
else
{
lean_object* v_val_1198_; 
lean_dec_ref(v_e_1060_);
v_val_1198_ = lean_ctor_get(v_e_x3f_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref(v_e_x3f_1197_);
v___y_1115_ = v_val_1198_;
goto v___jp_1114_;
}
}
}
v___jp_1114_:
{
switch(lean_obj_tag(v___y_1115_))
{
case 7:
{
lean_object* v_binderName_1116_; lean_object* v_binderType_1117_; lean_object* v_body_1118_; uint8_t v_binderInfo_1119_; lean_object* v___x_1120_; 
v_binderName_1116_ = lean_ctor_get(v___y_1115_, 0);
lean_inc(v_binderName_1116_);
v_binderType_1117_ = lean_ctor_get(v___y_1115_, 1);
v_body_1118_ = lean_ctor_get(v___y_1115_, 2);
v_binderInfo_1119_ = lean_ctor_get_uint8(v___y_1115_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1117_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1120_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_binderType_1117_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref(v___x_1120_);
lean_inc_ref(v_body_1118_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1122_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_body_1118_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; size_t v___x_1124_; size_t v___x_1125_; uint8_t v___x_1126_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref(v___x_1122_);
v___x_1124_ = lean_ptr_addr(v_binderType_1117_);
v___x_1125_ = lean_ptr_addr(v_a_1121_);
v___x_1126_ = lean_usize_dec_eq(v___x_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
v___y_1097_ = v___y_1115_;
v___y_1098_ = v_binderName_1116_;
v___y_1099_ = v_a_1123_;
v___y_1100_ = v_a_1121_;
v___y_1101_ = v_binderInfo_1119_;
v___y_1102_ = v___x_1126_;
goto v___jp_1096_;
}
else
{
size_t v___x_1127_; size_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_ptr_addr(v_body_1118_);
v___x_1128_ = lean_ptr_addr(v_a_1123_);
v___x_1129_ = lean_usize_dec_eq(v___x_1127_, v___x_1128_);
v___y_1097_ = v___y_1115_;
v___y_1098_ = v_binderName_1116_;
v___y_1099_ = v_a_1123_;
v___y_1100_ = v_a_1121_;
v___y_1101_ = v_binderInfo_1119_;
v___y_1102_ = v___x_1129_;
goto v___jp_1096_;
}
}
else
{
lean_dec(v_a_1121_);
lean_dec(v_binderName_1116_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1122_;
}
}
else
{
lean_dec_ref(v___y_1115_);
lean_dec(v_binderName_1116_);
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1120_;
}
}
case 6:
{
lean_object* v_binderName_1130_; lean_object* v_binderType_1131_; lean_object* v_body_1132_; uint8_t v_binderInfo_1133_; lean_object* v___x_1134_; 
v_binderName_1130_ = lean_ctor_get(v___y_1115_, 0);
lean_inc(v_binderName_1130_);
v_binderType_1131_ = lean_ctor_get(v___y_1115_, 1);
v_body_1132_ = lean_ctor_get(v___y_1115_, 2);
v_binderInfo_1133_ = lean_ctor_get_uint8(v___y_1115_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1131_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1134_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_binderType_1131_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1136_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref(v___x_1134_);
lean_inc_ref(v_body_1132_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1136_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_body_1132_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; size_t v___x_1138_; size_t v___x_1139_; uint8_t v___x_1140_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = lean_ptr_addr(v_binderType_1131_);
v___x_1139_ = lean_ptr_addr(v_a_1135_);
v___x_1140_ = lean_usize_dec_eq(v___x_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
v___y_1084_ = v_binderName_1130_;
v___y_1085_ = v___y_1115_;
v___y_1086_ = v_binderInfo_1133_;
v___y_1087_ = v_a_1137_;
v___y_1088_ = v_a_1135_;
v___y_1089_ = v___x_1140_;
goto v___jp_1083_;
}
else
{
size_t v___x_1141_; size_t v___x_1142_; uint8_t v___x_1143_; 
v___x_1141_ = lean_ptr_addr(v_body_1132_);
v___x_1142_ = lean_ptr_addr(v_a_1137_);
v___x_1143_ = lean_usize_dec_eq(v___x_1141_, v___x_1142_);
v___y_1084_ = v_binderName_1130_;
v___y_1085_ = v___y_1115_;
v___y_1086_ = v_binderInfo_1133_;
v___y_1087_ = v_a_1137_;
v___y_1088_ = v_a_1135_;
v___y_1089_ = v___x_1143_;
goto v___jp_1083_;
}
}
else
{
lean_dec(v_a_1135_);
lean_dec(v_binderName_1130_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1136_;
}
}
else
{
lean_dec(v_binderName_1130_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1134_;
}
}
case 8:
{
lean_object* v_declName_1144_; lean_object* v_type_1145_; lean_object* v_value_1146_; lean_object* v_body_1147_; uint8_t v_nondep_1148_; lean_object* v___x_1149_; 
v_declName_1144_ = lean_ctor_get(v___y_1115_, 0);
lean_inc(v_declName_1144_);
v_type_1145_ = lean_ctor_get(v___y_1115_, 1);
v_value_1146_ = lean_ctor_get(v___y_1115_, 2);
v_body_1147_ = lean_ctor_get(v___y_1115_, 3);
lean_inc_ref(v_body_1147_);
v_nondep_1148_ = lean_ctor_get_uint8(v___y_1115_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1145_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1149_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_type_1145_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref(v___x_1149_);
lean_inc_ref(v_value_1146_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1151_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_value_1146_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1153_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref(v___x_1151_);
lean_inc_ref(v_body_1147_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1153_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_body_1147_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; size_t v___x_1155_; size_t v___x_1156_; uint8_t v___x_1157_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = lean_ptr_addr(v_type_1145_);
v___x_1156_ = lean_ptr_addr(v_a_1150_);
v___x_1157_ = lean_usize_dec_eq(v___x_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
v___y_1067_ = v_declName_1144_;
v___y_1068_ = v___y_1115_;
v___y_1069_ = v_nondep_1148_;
v___y_1070_ = v_a_1152_;
v___y_1071_ = v_body_1147_;
v___y_1072_ = v_a_1154_;
v___y_1073_ = v_a_1150_;
v___y_1074_ = v___x_1157_;
goto v___jp_1066_;
}
else
{
size_t v___x_1158_; size_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1158_ = lean_ptr_addr(v_value_1146_);
v___x_1159_ = lean_ptr_addr(v_a_1152_);
v___x_1160_ = lean_usize_dec_eq(v___x_1158_, v___x_1159_);
v___y_1067_ = v_declName_1144_;
v___y_1068_ = v___y_1115_;
v___y_1069_ = v_nondep_1148_;
v___y_1070_ = v_a_1152_;
v___y_1071_ = v_body_1147_;
v___y_1072_ = v_a_1154_;
v___y_1073_ = v_a_1150_;
v___y_1074_ = v___x_1160_;
goto v___jp_1066_;
}
}
else
{
lean_dec(v_a_1152_);
lean_dec(v_a_1150_);
lean_dec_ref(v_body_1147_);
lean_dec(v_declName_1144_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1153_;
}
}
else
{
lean_dec(v_a_1150_);
lean_dec_ref(v_body_1147_);
lean_dec_ref(v___y_1115_);
lean_dec(v_declName_1144_);
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1151_;
}
}
else
{
lean_dec_ref(v_body_1147_);
lean_dec(v_declName_1144_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1149_;
}
}
case 5:
{
lean_object* v_dummy_1161_; lean_object* v_nargs_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_dummy_1161_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1162_ = l_Lean_Expr_getAppNumArgs(v___y_1115_);
lean_inc(v_nargs_1162_);
v___x_1163_ = lean_mk_array(v_nargs_1162_, v_dummy_1161_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_sub(v_nargs_1162_, v___x_1164_);
lean_dec(v_nargs_1162_);
v___x_1166_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1059_, v_post_1061_, v___y_1115_, v___x_1163_, v___x_1165_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1166_;
}
case 10:
{
lean_object* v_data_1167_; lean_object* v_expr_1168_; lean_object* v___x_1169_; 
v_data_1167_ = lean_ctor_get(v___y_1115_, 0);
v_expr_1168_ = lean_ctor_get(v___y_1115_, 1);
lean_inc_ref(v_expr_1168_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1169_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_expr_1168_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; size_t v___x_1171_; size_t v___x_1172_; uint8_t v___x_1173_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref(v___x_1169_);
v___x_1171_ = lean_ptr_addr(v_expr_1168_);
v___x_1172_ = lean_ptr_addr(v_a_1170_);
v___x_1173_ = lean_usize_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_inc(v_data_1167_);
lean_dec_ref(v___y_1115_);
v___x_1174_ = l_Lean_Expr_mdata___override(v_data_1167_, v_a_1170_);
v___x_1175_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___x_1174_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; 
lean_dec(v_a_1170_);
v___x_1176_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___y_1115_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1176_;
}
}
else
{
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1169_;
}
}
case 11:
{
lean_object* v_typeName_1177_; lean_object* v_idx_1178_; lean_object* v_struct_1179_; lean_object* v___x_1180_; 
v_typeName_1177_ = lean_ctor_get(v___y_1115_, 0);
v_idx_1178_ = lean_ctor_get(v___y_1115_, 1);
v_struct_1179_ = lean_ctor_get(v___y_1115_, 2);
lean_inc_ref(v_struct_1179_);
lean_inc_ref(v_post_1061_);
lean_inc_ref(v_pre_1059_);
v___x_1180_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1059_, v_post_1061_, v_struct_1179_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; size_t v___x_1182_; size_t v___x_1183_; uint8_t v___x_1184_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = lean_ptr_addr(v_struct_1179_);
v___x_1183_ = lean_ptr_addr(v_a_1181_);
v___x_1184_ = lean_usize_dec_eq(v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_inc(v_idx_1178_);
lean_inc(v_typeName_1177_);
lean_dec_ref(v___y_1115_);
v___x_1185_ = l_Lean_Expr_proj___override(v_typeName_1177_, v_idx_1178_, v_a_1181_);
v___x_1186_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___x_1185_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; 
lean_dec(v_a_1181_);
v___x_1187_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___y_1115_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1187_;
}
}
else
{
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_pre_1059_);
return v___x_1180_;
}
}
default: 
{
lean_object* v___x_1188_; 
v___x_1188_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___y_1115_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1188_;
}
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_post_1061_);
lean_dec_ref(v_e_1060_);
lean_dec_ref(v_pre_1059_);
v_a_1200_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1109_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1109_);
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
v___jp_1066_:
{
if (v___y_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref(v___y_1071_);
lean_dec_ref(v___y_1068_);
v___x_1075_ = l_Lean_Expr_letE___override(v___y_1067_, v___y_1073_, v___y_1070_, v___y_1072_, v___y_1069_);
v___x_1076_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___x_1075_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1076_;
}
else
{
size_t v___x_1077_; size_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = lean_ptr_addr(v___y_1071_);
lean_dec_ref(v___y_1071_);
v___x_1078_ = lean_ptr_addr(v___y_1072_);
v___x_1079_ = lean_usize_dec_eq(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v___y_1068_);
v___x_1080_ = l_Lean_Expr_letE___override(v___y_1067_, v___y_1073_, v___y_1070_, v___y_1072_, v___y_1069_);
v___x_1081_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___x_1080_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; 
lean_dec_ref(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1067_);
v___x_1082_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___y_1068_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1082_;
}
}
}
v___jp_1083_:
{
if (v___y_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec_ref(v___y_1085_);
v___x_1090_ = l_Lean_Expr_lam___override(v___y_1084_, v___y_1088_, v___y_1087_, v___y_1086_);
v___x_1091_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___x_1090_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1091_;
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = l_Lean_instBEqBinderInfo_beq(v___y_1086_, v___y_1086_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec_ref(v___y_1085_);
v___x_1093_ = l_Lean_Expr_lam___override(v___y_1084_, v___y_1088_, v___y_1087_, v___y_1086_);
v___x_1094_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___x_1093_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; 
lean_dec_ref(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1084_);
v___x_1095_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___y_1085_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1095_;
}
}
}
v___jp_1096_:
{
if (v___y_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v___y_1097_);
v___x_1103_ = l_Lean_Expr_forallE___override(v___y_1098_, v___y_1100_, v___y_1099_, v___y_1101_);
v___x_1104_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___x_1103_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1104_;
}
else
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lean_instBEqBinderInfo_beq(v___y_1101_, v___y_1101_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec_ref(v___y_1097_);
v___x_1106_ = l_Lean_Expr_forallE___override(v___y_1098_, v___y_1100_, v___y_1099_, v___y_1101_);
v___x_1107_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___x_1106_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
lean_dec_ref(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
v___x_1108_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1059_, v_post_1061_, v___y_1097_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_1208_, lean_object* v_e_1209_, lean_object* v_post_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v_pre_1208_, v_e_1209_, v_post_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1216_, lean_object* v_post_1217_, lean_object* v_e_1218_, lean_object* v_a_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_inc(v_a_1219_);
v___x_1223_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1223_, 0, lean_box(0));
lean_closure_set(v___x_1223_, 1, lean_box(0));
lean_closure_set(v___x_1223_, 2, v_a_1219_);
v___x_1224_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1223_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1255_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1255_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1255_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1225_, v_e_1218_);
lean_dec(v_a_1225_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___f_1230_; lean_object* v___x_1231_; 
lean_del_object(v___x_1227_);
lean_inc_ref(v_e_1218_);
v___f_1230_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 7, 3);
lean_closure_set(v___f_1230_, 0, v_pre_1216_);
lean_closure_set(v___f_1230_, 1, v_e_1218_);
lean_closure_set(v___f_1230_, 2, v_post_1217_);
lean_inc_ref(v___y_1220_);
v___x_1231_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1230_, v_a_1219_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
lean_inc(v_a_1232_);
lean_inc(v_a_1219_);
v___f_1233_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1233_, 0, v_a_1219_);
lean_closure_set(v___f_1233_, 1, v_e_1218_);
lean_closure_set(v___f_1233_, 2, v_a_1232_);
v___x_1234_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1233_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1242_);
v___x_1236_ = v___x_1234_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_dec(v___x_1234_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v_a_1232_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1232_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec(v_a_1232_);
v_a_1243_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1234_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1234_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
else
{
lean_dec_ref(v_e_1218_);
return v___x_1231_;
}
}
else
{
lean_object* v_val_1251_; lean_object* v___x_1253_; 
lean_dec_ref(v_e_1218_);
lean_dec_ref(v_post_1217_);
lean_dec_ref(v_pre_1216_);
v_val_1251_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1251_);
lean_dec_ref(v___x_1229_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v_val_1251_);
v___x_1253_ = v___x_1227_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_val_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_e_1218_);
lean_dec_ref(v_post_1217_);
lean_dec_ref(v_pre_1216_);
v_a_1256_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1224_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1224_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1264_, lean_object* v_post_1265_, lean_object* v_e_1266_, lean_object* v_a_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
lean_inc_ref(v_post_1265_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc_ref(v_e_1266_);
v___x_1271_ = lean_apply_4(v_post_1265_, v_e_1266_, v___y_1268_, v___y_1269_, lean_box(0));
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1290_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1290_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1290_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
switch(lean_obj_tag(v_a_1272_))
{
case 0:
{
lean_object* v_e_1276_; lean_object* v___x_1278_; 
lean_dec_ref(v_e_1266_);
lean_dec_ref(v_post_1265_);
lean_dec_ref(v_pre_1264_);
v_e_1276_ = lean_ctor_get(v_a_1272_, 0);
lean_inc_ref(v_e_1276_);
lean_dec_ref(v_a_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v_e_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_e_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
case 1:
{
lean_object* v_e_1280_; lean_object* v___x_1281_; 
lean_del_object(v___x_1274_);
lean_dec_ref(v_e_1266_);
v_e_1280_ = lean_ctor_get(v_a_1272_, 0);
lean_inc_ref(v_e_1280_);
lean_dec_ref(v_a_1272_);
v___x_1281_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1264_, v_post_1265_, v_e_1280_, v_a_1267_, v___y_1268_, v___y_1269_);
return v___x_1281_;
}
default: 
{
lean_object* v_e_x3f_1282_; 
lean_dec_ref(v_post_1265_);
lean_dec_ref(v_pre_1264_);
v_e_x3f_1282_ = lean_ctor_get(v_a_1272_, 0);
lean_inc(v_e_x3f_1282_);
lean_dec_ref(v_a_1272_);
if (lean_obj_tag(v_e_x3f_1282_) == 0)
{
lean_object* v___x_1284_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v_e_1266_);
v___x_1284_ = v___x_1274_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_e_1266_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
else
{
lean_object* v_val_1286_; lean_object* v___x_1288_; 
lean_dec_ref(v_e_1266_);
v_val_1286_ = lean_ctor_get(v_e_x3f_1282_, 0);
lean_inc(v_val_1286_);
lean_dec_ref(v_e_x3f_1282_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v_val_1286_);
v___x_1288_ = v___x_1274_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_val_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_e_1266_);
lean_dec_ref(v_post_1265_);
lean_dec_ref(v_pre_1264_);
v_a_1291_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1271_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1271_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1299_, lean_object* v_post_1300_, lean_object* v_e_1301_, lean_object* v_a_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1299_, v_post_1300_, v_e_1301_, v_a_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v_a_1302_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1307_, lean_object* v_post_1308_, lean_object* v_sz_1309_, lean_object* v_i_1310_, lean_object* v_bs_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
size_t v_sz_boxed_1316_; size_t v_i_boxed_1317_; lean_object* v_res_1318_; 
v_sz_boxed_1316_ = lean_unbox_usize(v_sz_1309_);
lean_dec(v_sz_1309_);
v_i_boxed_1317_ = lean_unbox_usize(v_i_1310_);
lean_dec(v_i_1310_);
v_res_1318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1307_, v_post_1308_, v_sz_boxed_1316_, v_i_boxed_1317_, v_bs_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1319_, lean_object* v_post_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1319_, v_post_1320_, v_x_1321_, v_x_1322_, v_x_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1329_, lean_object* v_post_1330_, lean_object* v_e_1331_, lean_object* v_a_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1329_, v_post_1330_, v_e_1331_, v_a_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v_a_1332_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1337_, lean_object* v_x_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_apply_1(v_x_1338_, lean_box(0));
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1344_, lean_object* v_x_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1344_, v_x_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1349_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_unsigned_to_nat(16u);
v___x_1352_ = lean_mk_array(v___x_1351_, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v___x_1353_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1357_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1357_, 0, lean_box(0));
lean_closure_set(v___x_1357_, 1, lean_box(0));
lean_closure_set(v___x_1357_, 2, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1358_, lean_object* v_pre_1359_, lean_object* v_post_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_a_1366_; lean_object* v___x_1367_; 
v___x_1364_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1365_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1364_, v___y_1361_, v___y_1362_);
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref(v___x_1365_);
v___x_1367_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1359_, v_post_1360_, v_input_1358_, v_a_1366_, v___y_1361_, v___y_1362_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1369_, 0, lean_box(0));
lean_closure_set(v___x_1369_, 1, lean_box(0));
lean_closure_set(v___x_1369_, 2, v_a_1366_);
v___x_1370_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1369_, v___y_1361_, v___y_1362_);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1378_);
v___x_1372_ = v___x_1370_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v___x_1370_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_a_1368_);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1368_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_dec(v_a_1366_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1379_, lean_object* v_pre_1380_, lean_object* v_post_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1379_, v_pre_1380_, v_post_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___f_1392_; lean_object* v___f_1393_; lean_object* v___x_1394_; 
v___f_1392_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1393_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1394_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1388_, v___f_1392_, v___f_1393_, v_a_1389_, v_a_1390_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1395_, v_a_1396_, v_a_1397_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1400_, lean_object* v_m_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1401_, v_a_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1404_, lean_object* v_m_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1404_, v_m_1405_, v_a_1406_);
lean_dec_ref(v_a_1406_);
lean_dec_ref(v_m_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1408_, lean_object* v_ref_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1409_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1414_, lean_object* v_ref_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1414_, v_ref_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1420_, lean_object* v_x_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
lean_inc_ref(v___y_1423_);
v___x_1426_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1427_, v_x_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1434_, lean_object* v_m_1435_, lean_object* v_a_1436_, lean_object* v_b_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1435_, v_a_1436_, v_b_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1439_, lean_object* v_a_1440_, lean_object* v_x_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1440_, v_x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1443_, lean_object* v_a_1444_, lean_object* v_x_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1443_, v_a_1444_, v_x_1445_);
lean_dec(v_x_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_1447_, lean_object* v_a_1448_, lean_object* v_x_1449_){
_start:
{
uint8_t v___x_1450_; 
v___x_1450_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1448_, v_x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1451_, lean_object* v_a_1452_, lean_object* v_x_1453_){
_start:
{
uint8_t v_res_1454_; lean_object* v_r_1455_; 
v_res_1454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_1451_, v_a_1452_, v_x_1453_);
lean_dec(v_x_1453_);
lean_dec_ref(v_a_1452_);
v_r_1455_ = lean_box(v_res_1454_);
return v_r_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1456_, lean_object* v_data_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_data_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1459_, lean_object* v_a_1460_, lean_object* v_b_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1460_, v_b_1461_, v_x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_1464_, lean_object* v_i_1465_, lean_object* v_source_1466_, lean_object* v_target_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_1465_, v_source_1466_, v_target_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_1470_, v_x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v_env_1477_; uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1476_ = lean_st_ref_get(v___y_1474_);
v_env_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc_ref(v_env_1477_);
lean_dec(v___x_1476_);
v___x_1478_ = l_Lean_isRecCore(v_env_1477_, v_declName_1473_);
v___x_1479_ = lean_box(v___x_1478_);
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1481_, v___y_1482_);
lean_dec(v___y_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1485_, v___y_1489_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v_env_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1502_ = lean_st_ref_get(v___y_1500_);
v_env_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc_ref(v_env_1503_);
lean_dec(v___x_1502_);
v___x_1504_ = lean_get_reducibility_status(v_env_1503_, v_declName_1499_);
v___x_1505_ = lean_box(v___x_1504_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1507_, v___y_1508_);
lean_dec(v___y_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1533_; 
v___x_1517_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1511_, v___y_1515_);
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1533_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1533_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_unbox(v_a_1518_);
lean_dec(v_a_1518_);
if (v___x_1522_ == 0)
{
uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1523_ = 1;
v___x_1524_ = lean_box(v___x_1523_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1524_);
v___x_1526_ = v___x_1520_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
else
{
uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1528_ = 0;
v___x_1529_ = lean_box(v___x_1528_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1529_);
v___x_1531_ = v___x_1520_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1541_, lean_object* v_b_1542_){
_start:
{
lean_object* v_array_1544_; lean_object* v_start_1545_; lean_object* v_stop_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1563_; 
v_array_1544_ = lean_ctor_get(v_a_1541_, 0);
v_start_1545_ = lean_ctor_get(v_a_1541_, 1);
v_stop_1546_ = lean_ctor_get(v_a_1541_, 2);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_a_1541_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1548_ = v_a_1541_;
v_isShared_1549_ = v_isSharedCheck_1563_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_stop_1546_);
lean_inc(v_start_1545_);
lean_inc(v_array_1544_);
lean_dec(v_a_1541_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1563_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_nat_dec_lt(v_start_1545_, v_stop_1546_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_del_object(v___x_1548_);
lean_dec(v_stop_1546_);
lean_dec(v_start_1545_);
lean_dec_ref(v_array_1544_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_b_1542_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1552_ = lean_box(0);
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = lean_nat_add(v_start_1545_, v___x_1553_);
lean_inc_ref(v_array_1544_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 1, v___x_1554_);
v___x_1556_ = v___x_1548_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_array_1544_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_stop_1546_);
v___x_1556_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = lean_array_fget(v_array_1544_, v_start_1545_);
lean_dec(v_start_1545_);
lean_dec_ref(v_array_1544_);
v___x_1558_ = l_Lean_Expr_hasExprMVar(v___x_1557_);
lean_dec(v___x_1557_);
if (v___x_1558_ == 0)
{
v_a_1541_ = v___x_1556_;
v_b_1542_ = v___x_1552_;
goto _start;
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_dec_ref(v___x_1560_);
v_a_1541_ = v___x_1556_;
v_b_1542_ = v___x_1552_;
goto _start;
}
else
{
lean_dec_ref(v___x_1556_);
return v___x_1560_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1564_, lean_object* v_b_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1564_, v_b_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1576_, uint8_t v_isMatch_1577_, uint8_t v_root_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___y_1585_; lean_object* v_b_1586_; lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1576_, v_root_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1784_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1784_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1784_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___y_1603_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; 
if (v_root_1578_ == 0)
{
lean_object* v___x_1772_; 
lean_inc(v_a_1598_);
v___x_1772_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1598_);
if (lean_obj_tag(v___x_1772_) == 1)
{
lean_object* v_val_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1783_; 
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_val_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_val_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 2);
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_val_1773_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
}
else
{
lean_dec(v___x_1772_);
v___y_1613_ = v_a_1579_;
v___y_1614_ = v_a_1580_;
v___y_1615_ = v_a_1581_;
v___y_1616_ = v_a_1582_;
goto v___jp_1612_;
}
}
else
{
v___y_1613_ = v_a_1579_;
v___y_1614_ = v_a_1580_;
v___y_1615_ = v_a_1581_;
v___y_1616_ = v_a_1582_;
goto v___jp_1612_;
}
v___jp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
v___x_1604_ = l_Lean_Expr_getAppNumArgs(v_a_1598_);
lean_inc(v___x_1604_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___y_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_mk_empty_array_with_capacity(v___x_1604_);
lean_dec(v___x_1604_);
v___x_1607_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1598_, v___x_1606_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1605_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1608_);
v___x_1610_ = v___x_1600_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
v___jp_1612_:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Expr_getAppFn(v_a_1598_);
switch(lean_obj_tag(v___x_1617_))
{
case 1:
{
lean_object* v_fvarId_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_del_object(v___x_1600_);
v_fvarId_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_fvarId_1618_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = l_Lean_Expr_getAppNumArgs(v_a_1598_);
lean_inc(v___x_1619_);
v___x_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1620_, 0, v_fvarId_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_mk_empty_array_with_capacity(v___x_1619_);
lean_dec(v___x_1619_);
v___x_1622_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1598_, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1620_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
case 2:
{
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
if (v_isMatch_1577_ == 0)
{
lean_object* v_mvarId_1625_; lean_object* v___x_1626_; 
v_mvarId_1625_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_mvarId_1625_);
lean_dec_ref(v___x_1617_);
v___x_1626_ = l_Lean_Meta_getConfig___redArg(v___y_1613_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1659_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1659_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1659_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
uint8_t v_isDefEqStuckEx_1631_; 
v_isDefEqStuckEx_1631_ = lean_ctor_get_uint8(v_a_1627_, 4);
lean_dec(v_a_1627_);
if (v_isDefEqStuckEx_1631_ == 0)
{
lean_object* v___x_1632_; 
lean_del_object(v___x_1629_);
v___x_1632_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1625_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1646_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_unbox(v_a_1633_);
lean_dec(v_a_1633_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1638_);
v___x_1640_ = v___x_1635_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1642_);
v___x_1644_ = v___x_1635_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_a_1647_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1632_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1632_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_dec(v_mvarId_1625_);
v___x_1655_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1655_);
v___x_1657_ = v___x_1629_;
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
lean_dec(v_mvarId_1625_);
v_a_1660_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1626_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1626_);
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
lean_dec_ref(v___x_1617_);
v___x_1668_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
case 4:
{
lean_object* v_declName_1670_; lean_object* v___x_1671_; 
v_declName_1670_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_declName_1670_);
lean_dec_ref(v___x_1617_);
v___x_1671_ = l_Lean_Meta_getConfig___redArg(v___y_1613_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; uint8_t v_isDefEqStuckEx_1673_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref(v___x_1671_);
v_isDefEqStuckEx_1673_ = lean_ctor_get_uint8(v_a_1672_, 4);
lean_dec(v_a_1672_);
if (v_isDefEqStuckEx_1673_ == 0)
{
v___y_1603_ = v_declName_1670_;
goto v___jp_1602_;
}
else
{
uint8_t v___x_1674_; 
v___x_1674_ = l_Lean_Expr_hasExprMVar(v_a_1598_);
if (v___x_1674_ == 0)
{
v___y_1603_ = v_declName_1670_;
goto v___jp_1602_;
}
else
{
lean_object* v___x_1675_; 
lean_inc(v_declName_1670_);
v___x_1675_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1670_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; uint8_t v___x_1677_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref(v___x_1675_);
v___x_1677_ = lean_unbox(v_a_1676_);
lean_dec(v_a_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v_env_1679_; lean_object* v___x_1680_; 
v___x_1678_ = lean_st_ref_get(v___y_1616_);
v_env_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_ref(v_env_1679_);
lean_dec(v___x_1678_);
v___x_1680_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1679_, v_a_1598_);
if (lean_obj_tag(v___x_1680_) == 1)
{
lean_object* v_val_1681_; lean_object* v_numDiscrs_1682_; lean_object* v_nargs_1683_; lean_object* v_dummy_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_val_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_val_1681_);
lean_dec_ref(v___x_1680_);
v_numDiscrs_1682_ = lean_ctor_get(v_val_1681_, 1);
lean_inc(v_numDiscrs_1682_);
v_nargs_1683_ = l_Lean_Expr_getAppNumArgs(v_a_1598_);
v_dummy_1684_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1683_);
v___x_1685_ = lean_mk_array(v_nargs_1683_, v_dummy_1684_);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_nat_sub(v_nargs_1683_, v___x_1686_);
lean_dec(v_nargs_1683_);
lean_inc(v_a_1598_);
v___x_1688_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1598_, v___x_1685_, v___x_1687_);
v___x_1689_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1681_);
lean_dec(v_val_1681_);
v___x_1690_ = lean_nat_add(v___x_1689_, v_numDiscrs_1682_);
lean_dec(v_numDiscrs_1682_);
v___x_1691_ = l_Array_toSubarray___redArg(v___x_1688_, v___x_1689_, v___x_1690_);
v___x_1692_ = lean_box(0);
v___x_1693_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1691_, v___x_1692_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_dec_ref(v___x_1693_);
v___y_1603_ = v_declName_1670_;
goto v___jp_1602_;
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_declName_1670_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v___x_1702_; lean_object* v_a_1703_; uint8_t v___x_1704_; 
lean_dec(v___x_1680_);
lean_inc(v_declName_1670_);
v___x_1702_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1670_, v___y_1616_);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = lean_unbox(v_a_1703_);
lean_dec(v_a_1703_);
if (v___x_1704_ == 0)
{
v___y_1603_ = v_declName_1670_;
goto v___jp_1602_;
}
else
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_dec_ref(v___x_1705_);
v___y_1603_ = v_declName_1670_;
goto v___jp_1602_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_declName_1670_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
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
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_dec_ref(v___x_1714_);
v___y_1603_ = v_declName_1670_;
goto v___jp_1602_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_declName_1670_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_declName_1670_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_a_1723_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1675_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1675_);
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
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_declName_1670_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_a_1731_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1671_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1671_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
case 7:
{
lean_object* v_binderType_1739_; lean_object* v_body_1740_; uint8_t v___x_1741_; 
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_binderType_1739_ = lean_ctor_get(v___x_1617_, 1);
lean_inc_ref(v_binderType_1739_);
v_body_1740_ = lean_ctor_get(v___x_1617_, 2);
lean_inc_ref(v_body_1740_);
lean_dec_ref(v___x_1617_);
v___x_1741_ = l_Lean_Expr_hasLooseBVars(v_body_1740_);
if (v___x_1741_ == 0)
{
v___y_1585_ = v_binderType_1739_;
v_b_1586_ = v_body_1740_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1740_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___x_1742_);
v___y_1585_ = v_binderType_1739_;
v_b_1586_ = v_a_1743_;
goto v___jp_1584_;
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec_ref(v_binderType_1739_);
v_a_1744_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1742_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1742_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
case 9:
{
lean_object* v_a_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_a_1752_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_ref(v_a_1752_);
lean_dec_ref(v___x_1617_);
v___x_1753_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_a_1752_);
v___x_1754_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1753_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
case 11:
{
lean_object* v_typeName_1757_; lean_object* v_idx_1758_; lean_object* v_struct_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_del_object(v___x_1600_);
v_typeName_1757_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_typeName_1757_);
v_idx_1758_ = lean_ctor_get(v___x_1617_, 1);
lean_inc(v_idx_1758_);
v_struct_1759_ = lean_ctor_get(v___x_1617_, 2);
lean_inc_ref(v_struct_1759_);
lean_dec_ref(v___x_1617_);
v___x_1760_ = l_Lean_Expr_getAppNumArgs(v_a_1598_);
lean_inc(v___x_1760_);
v___x_1761_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1761_, 0, v_typeName_1757_);
lean_ctor_set(v___x_1761_, 1, v_idx_1758_);
lean_ctor_set(v___x_1761_, 2, v___x_1760_);
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_mk_empty_array_with_capacity(v___x_1762_);
v___x_1764_ = lean_array_push(v___x_1763_, v_struct_1759_);
v___x_1765_ = lean_mk_empty_array_with_capacity(v___x_1760_);
lean_dec(v___x_1760_);
v___x_1766_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1598_, v___x_1765_);
v___x_1767_ = l_Array_append___redArg(v___x_1764_, v___x_1766_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1761_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
default: 
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec_ref(v___x_1617_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v___x_1770_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
v_a_1785_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1597_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1597_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
v___jp_1584_:
{
uint8_t v___x_1587_; 
v___x_1587_ = l_Lean_Expr_hasLooseBVars(v_b_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1588_ = lean_box(5);
v___x_1589_ = lean_unsigned_to_nat(2u);
v___x_1590_ = lean_mk_empty_array_with_capacity(v___x_1589_);
v___x_1591_ = lean_array_push(v___x_1590_, v___y_1585_);
v___x_1592_ = lean_array_push(v___x_1591_, v_b_1586_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1588_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref(v_b_1586_);
lean_dec_ref(v___y_1585_);
v___x_1595_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1793_, lean_object* v_isMatch_1794_, lean_object* v_root_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
uint8_t v_isMatch_boxed_1801_; uint8_t v_root_boxed_1802_; lean_object* v_res_1803_; 
v_isMatch_boxed_1801_ = lean_unbox(v_isMatch_1794_);
v_root_boxed_1802_ = lean_unbox(v_root_1795_);
v_res_1803_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1793_, v_isMatch_boxed_1801_, v_root_boxed_1802_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1804_, v___y_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1818_, lean_object* v_R_1819_, lean_object* v_a_1820_, lean_object* v_b_1821_, lean_object* v_c_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1820_, v_b_1821_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1829_, lean_object* v_R_1830_, lean_object* v_a_1831_, lean_object* v_b_1832_, lean_object* v_c_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1829_, v_R_1830_, v_a_1831_, v_b_1832_, v_c_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1840_, uint8_t v_root_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
uint8_t v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = 1;
v___x_1848_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1840_, v___x_1847_, v_root_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1849_, lean_object* v_root_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
uint8_t v_root_boxed_1856_; lean_object* v_res_1857_; 
v_root_boxed_1856_ = lean_unbox(v_root_1850_);
v_res_1857_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1849_, v_root_boxed_1856_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1857_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_unsigned_to_nat(16u);
v___x_1862_ = lean_mk_array(v___x_1861_, v___x_1860_);
return v___x_1862_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v___x_1863_);
return v___x_1865_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1866_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1869_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v___x_1867_);
lean_ctor_set(v___x_1869_, 2, v___x_1866_);
lean_ctor_set(v___x_1869_, 3, v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3);
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
lean_object* v___x_1916_; lean_object* v_env_1917_; lean_object* v___x_1918_; lean_object* v_mctx_1919_; lean_object* v_lctx_1920_; lean_object* v_options_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1916_ = lean_st_ref_get(v___y_1914_);
v_env_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_env_1917_);
lean_dec(v___x_1916_);
v___x_1918_ = lean_st_ref_get(v___y_1912_);
v_mctx_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc_ref(v_mctx_1919_);
lean_dec(v___x_1918_);
v_lctx_1920_ = lean_ctor_get(v___y_1911_, 2);
v_options_1921_ = lean_ctor_get(v___y_1913_, 2);
lean_inc_ref(v_options_1921_);
lean_inc_ref(v_lctx_1920_);
v___x_1922_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1922_, 0, v_env_1917_);
lean_ctor_set(v___x_1922_, 1, v_mctx_1919_);
lean_ctor_set(v___x_1922_, 2, v_lctx_1920_);
lean_ctor_set(v___x_1922_, 3, v_options_1921_);
v___x_1923_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v_msgData_1910_);
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
v_ref_1938_ = lean_ctor_get(v___y_1935_, 5);
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
lean_dec_ref(v___x_1980_);
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
lean_dec(v_declName_2028_);
lean_dec_ref(v___x_1980_);
lean_dec(v_a_1969_);
v_val_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_val_2037_);
lean_dec_ref(v___x_2036_);
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
lean_dec(v_declName_2028_);
lean_dec_ref(v___x_1980_);
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
lean_dec_ref(v___x_1980_);
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
lean_inc(v_typeName_2058_);
v___x_2068_ = lean_is_class(v_env_2067_, v_typeName_2058_);
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
lean_dec_ref(v___x_1980_);
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
lean_dec_ref(v___x_1980_);
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
lean_dec_ref(v___x_1980_);
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
lean_dec_ref(v___x_2095_);
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
lean_dec_ref(v___x_1989_);
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
lean_dec_ref(v___x_2182_);
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
static uint64_t _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0(void){
_start:
{
uint8_t v___x_2286_; uint64_t v___x_2287_; 
v___x_2286_ = 2;
v___x_2287_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2288_, lean_object* v_m_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_tries_2295_; lean_object* v_roots_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2368_; 
v_tries_2295_ = lean_ctor_get(v_d_2288_, 0);
v_roots_2296_ = lean_ctor_get(v_d_2288_, 1);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_d_2288_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2298_ = v_d_2288_;
v_isShared_2299_ = v_isSharedCheck_2368_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_roots_2296_);
lean_inc(v_tries_2295_);
lean_dec(v_d_2288_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2368_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; uint8_t v_foApprox_2301_; uint8_t v_ctxApprox_2302_; uint8_t v_quasiPatternApprox_2303_; uint8_t v_constApprox_2304_; uint8_t v_isDefEqStuckEx_2305_; uint8_t v_unificationHints_2306_; uint8_t v_proofIrrelevance_2307_; uint8_t v_assignSyntheticOpaque_2308_; uint8_t v_offsetCnstrs_2309_; uint8_t v_etaStruct_2310_; uint8_t v_univApprox_2311_; uint8_t v_iota_2312_; uint8_t v_beta_2313_; uint8_t v_proj_2314_; uint8_t v_zeta_2315_; uint8_t v_zetaDelta_2316_; uint8_t v_zetaUnused_2317_; uint8_t v_zetaHave_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2367_; 
v___x_2300_ = l_Lean_Meta_Context_config(v_a_2290_);
v_foApprox_2301_ = lean_ctor_get_uint8(v___x_2300_, 0);
v_ctxApprox_2302_ = lean_ctor_get_uint8(v___x_2300_, 1);
v_quasiPatternApprox_2303_ = lean_ctor_get_uint8(v___x_2300_, 2);
v_constApprox_2304_ = lean_ctor_get_uint8(v___x_2300_, 3);
v_isDefEqStuckEx_2305_ = lean_ctor_get_uint8(v___x_2300_, 4);
v_unificationHints_2306_ = lean_ctor_get_uint8(v___x_2300_, 5);
v_proofIrrelevance_2307_ = lean_ctor_get_uint8(v___x_2300_, 6);
v_assignSyntheticOpaque_2308_ = lean_ctor_get_uint8(v___x_2300_, 7);
v_offsetCnstrs_2309_ = lean_ctor_get_uint8(v___x_2300_, 8);
v_etaStruct_2310_ = lean_ctor_get_uint8(v___x_2300_, 10);
v_univApprox_2311_ = lean_ctor_get_uint8(v___x_2300_, 11);
v_iota_2312_ = lean_ctor_get_uint8(v___x_2300_, 12);
v_beta_2313_ = lean_ctor_get_uint8(v___x_2300_, 13);
v_proj_2314_ = lean_ctor_get_uint8(v___x_2300_, 14);
v_zeta_2315_ = lean_ctor_get_uint8(v___x_2300_, 15);
v_zetaDelta_2316_ = lean_ctor_get_uint8(v___x_2300_, 16);
v_zetaUnused_2317_ = lean_ctor_get_uint8(v___x_2300_, 17);
v_zetaHave_2318_ = lean_ctor_get_uint8(v___x_2300_, 18);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2320_ = v___x_2300_;
v_isShared_2321_ = v_isSharedCheck_2367_;
goto v_resetjp_2319_;
}
else
{
lean_dec(v___x_2300_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2367_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; uint8_t v_trackZetaDelta_2323_; lean_object* v_zetaDeltaSet_2324_; lean_object* v_lctx_2325_; lean_object* v_localInstances_2326_; lean_object* v_defEqCtx_x3f_2327_; lean_object* v_synthPendingDepth_2328_; lean_object* v_canUnfold_x3f_2329_; uint8_t v_univApprox_2330_; uint8_t v_inTypeClassResolution_2331_; uint8_t v_cacheInferType_2332_; uint8_t v___x_2333_; lean_object* v_config_2335_; 
v___x_2322_ = lean_st_mk_ref(v_tries_2295_);
v_trackZetaDelta_2323_ = lean_ctor_get_uint8(v_a_2290_, sizeof(void*)*7);
v_zetaDeltaSet_2324_ = lean_ctor_get(v_a_2290_, 1);
v_lctx_2325_ = lean_ctor_get(v_a_2290_, 2);
v_localInstances_2326_ = lean_ctor_get(v_a_2290_, 3);
v_defEqCtx_x3f_2327_ = lean_ctor_get(v_a_2290_, 4);
v_synthPendingDepth_2328_ = lean_ctor_get(v_a_2290_, 5);
v_canUnfold_x3f_2329_ = lean_ctor_get(v_a_2290_, 6);
v_univApprox_2330_ = lean_ctor_get_uint8(v_a_2290_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2331_ = lean_ctor_get_uint8(v_a_2290_, sizeof(void*)*7 + 2);
v_cacheInferType_2332_ = lean_ctor_get_uint8(v_a_2290_, sizeof(void*)*7 + 3);
v___x_2333_ = 2;
if (v_isShared_2321_ == 0)
{
v_config_2335_ = v___x_2320_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 0, v_foApprox_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 1, v_ctxApprox_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 2, v_quasiPatternApprox_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 3, v_constApprox_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 4, v_isDefEqStuckEx_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 5, v_unificationHints_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 6, v_proofIrrelevance_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 7, v_assignSyntheticOpaque_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 8, v_offsetCnstrs_2309_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 10, v_etaStruct_2310_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 11, v_univApprox_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 12, v_iota_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 13, v_beta_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 14, v_proj_2314_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 15, v_zeta_2315_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 16, v_zetaDelta_2316_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 17, v_zetaUnused_2317_);
lean_ctor_set_uint8(v_reuseFailAlloc_2366_, 18, v_zetaHave_2318_);
v_config_2335_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
uint64_t v___x_2336_; uint64_t v___x_2337_; uint64_t v___x_2338_; uint64_t v___x_2339_; uint64_t v___x_2340_; uint64_t v_key_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_ctor_set_uint8(v_config_2335_, 9, v___x_2333_);
v___x_2336_ = l_Lean_Meta_Context_configKey(v_a_2290_);
v___x_2337_ = 2ULL;
v___x_2338_ = lean_uint64_shift_right(v___x_2336_, v___x_2337_);
v___x_2339_ = lean_uint64_shift_left(v___x_2338_, v___x_2337_);
v___x_2340_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0);
v_key_2341_ = lean_uint64_lor(v___x_2339_, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2342_, 0, v_config_2335_);
lean_ctor_set_uint64(v___x_2342_, sizeof(void*)*1, v_key_2341_);
lean_inc(v_canUnfold_x3f_2329_);
lean_inc(v_synthPendingDepth_2328_);
lean_inc(v_defEqCtx_x3f_2327_);
lean_inc_ref(v_localInstances_2326_);
lean_inc_ref(v_lctx_2325_);
lean_inc(v_zetaDeltaSet_2324_);
v___x_2343_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v_zetaDeltaSet_2324_);
lean_ctor_set(v___x_2343_, 2, v_lctx_2325_);
lean_ctor_set(v___x_2343_, 3, v_localInstances_2326_);
lean_ctor_set(v___x_2343_, 4, v_defEqCtx_x3f_2327_);
lean_ctor_set(v___x_2343_, 5, v_synthPendingDepth_2328_);
lean_ctor_set(v___x_2343_, 6, v_canUnfold_x3f_2329_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*7, v_trackZetaDelta_2323_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*7 + 1, v_univApprox_2330_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2331_);
lean_ctor_set_uint8(v___x_2343_, sizeof(void*)*7 + 3, v_cacheInferType_2332_);
lean_inc(v_a_2293_);
lean_inc_ref(v_a_2292_);
lean_inc(v_a_2291_);
lean_inc(v___x_2322_);
v___x_2344_ = lean_apply_6(v_m_2289_, v___x_2322_, v___x_2343_, v_a_2291_, v_a_2292_, v_a_2293_, lean_box(0));
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2357_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2357_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2357_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = lean_st_ref_get(v___x_2322_);
lean_dec(v___x_2322_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2349_);
v___x_2351_ = v___x_2298_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_roots_2296_);
v___x_2351_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v_a_2345_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v___x_2352_);
v___x_2354_ = v___x_2347_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v___x_2322_);
lean_del_object(v___x_2298_);
lean_dec_ref(v_roots_2296_);
v_a_2358_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2344_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2344_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2369_, lean_object* v_m_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2369_, v_m_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2377_, lean_object* v_00_u03b2_2378_, lean_object* v_d_2379_, lean_object* v_m_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2379_, v_m_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2387_, lean_object* v_00_u03b2_2388_, lean_object* v_d_2389_, lean_object* v_m_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2387_, v_00_u03b2_2388_, v_d_2389_, v_m_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2397_, lean_object* v_v_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2401_ = lean_st_ref_take(v_a_2399_);
v___x_2402_ = lean_array_set(v___x_2401_, v_i_2397_, v_v_2398_);
v___x_2403_ = lean_st_ref_set(v_a_2399_, v___x_2402_);
v___x_2404_ = lean_box(0);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2406_, lean_object* v_v_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2406_, v_v_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec(v_i_2406_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2411_, lean_object* v_i_2412_, lean_object* v_v_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2412_, v_v_2413_, v_a_2414_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2421_, lean_object* v_i_2422_, lean_object* v_v_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2421_, v_i_2422_, v_v_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec(v_i_2422_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_sz_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_sz_2433_ = lean_array_get_size(v_a_2432_);
v___x_2434_ = lean_unsigned_to_nat(0u);
v___x_2435_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2436_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2437_ = lean_unsigned_to_nat(1u);
v___x_2438_ = lean_mk_empty_array_with_capacity(v___x_2437_);
v___x_2439_ = lean_array_push(v___x_2438_, v_e_2431_);
v___x_2440_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2435_);
lean_ctor_set(v___x_2440_, 1, v___x_2434_);
lean_ctor_set(v___x_2440_, 2, v___x_2436_);
lean_ctor_set(v___x_2440_, 3, v___x_2439_);
v___x_2441_ = lean_array_push(v_a_2432_, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_sz_2433_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2443_, lean_object* v_e_2444_){
_start:
{
lean_object* v_modifyGet_2445_; lean_object* v___f_2446_; lean_object* v___x_2447_; 
v_modifyGet_2445_ = lean_ctor_get(v_inst_2443_, 2);
lean_inc(v_modifyGet_2445_);
lean_dec_ref(v_inst_2443_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2446_, 0, v_e_2444_);
v___x_2447_ = lean_apply_2(v_modifyGet_2445_, lean_box(0), v___f_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2448_, lean_object* v_00_u03b1_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_e_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2451_, v_e_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2454_, lean_object* v_00_u03b1_2455_, lean_object* v_inst_2456_, lean_object* v_inst_2457_, lean_object* v_e_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2454_, v_00_u03b1_2455_, v_inst_2456_, v_inst_2457_, v_e_2458_);
lean_dec_ref(v_inst_2456_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2460_, lean_object* v_e_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; lean_object* v_fst_2466_; lean_object* v_snd_2467_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2464_ = lean_st_ref_take(v_a_2462_);
v___x_2470_ = lean_box(0);
v___x_2471_ = lean_array_get_size(v___x_2464_);
v___x_2472_ = lean_nat_dec_lt(v_i_2460_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_dec_ref(v_e_2461_);
v_fst_2466_ = v___x_2470_;
v_snd_2467_ = v___x_2464_;
goto v___jp_2465_;
}
else
{
lean_object* v_v_2473_; lean_object* v_xs_x27_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_v_2473_ = lean_array_fget(v___x_2464_, v_i_2460_);
v_xs_x27_2474_ = lean_array_fset(v___x_2464_, v_i_2460_, v___x_2470_);
v___x_2475_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2473_, v_e_2461_);
v___x_2476_ = lean_array_fset(v_xs_x27_2474_, v_i_2460_, v___x_2475_);
v_fst_2466_ = v___x_2470_;
v_snd_2467_ = v___x_2476_;
goto v___jp_2465_;
}
v___jp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = lean_st_ref_set(v_a_2462_, v_snd_2467_);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_fst_2466_);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2477_, lean_object* v_e_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2477_, v_e_2478_, v_a_2479_);
lean_dec(v_a_2479_);
lean_dec(v_i_2477_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2482_, lean_object* v_i_2483_, lean_object* v_e_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2483_, v_e_2484_, v_a_2485_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2492_, lean_object* v_i_2493_, lean_object* v_e_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2492_, v_i_2493_, v_e_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec(v_i_2493_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; 
lean_inc(v___y_2503_);
v___x_2509_ = lean_apply_6(v_x_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, lean_box(0));
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2511_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2518_, lean_object* v_localInsts_2519_, lean_object* v_x_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___f_2527_; lean_object* v___x_2528_; 
lean_inc(v___y_2521_);
v___f_2527_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2527_, 0, v_x_2520_);
lean_closure_set(v___f_2527_, 1, v___y_2521_);
v___x_2528_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2518_, v_localInsts_2519_, v___f_2527_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2528_) == 0)
{
return v___x_2528_;
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2537_, lean_object* v_localInsts_2538_, lean_object* v_x_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2537_, v_localInsts_2538_, v_x_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2547_, lean_object* v_00_u03b1_2548_, lean_object* v_lctx_2549_, lean_object* v_localInsts_2550_, lean_object* v_x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2549_, v_localInsts_2550_, v_x_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_00_u03b1_2560_, lean_object* v_lctx_2561_, lean_object* v_localInsts_2562_, lean_object* v_x_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2559_, v_00_u03b1_2560_, v_lctx_2561_, v_localInsts_2562_, v_x_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___x_2574_; lean_object* v_sz_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2574_ = lean_st_ref_take(v___y_2572_);
v_sz_2575_ = lean_array_get_size(v___x_2574_);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2578_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2579_ = lean_unsigned_to_nat(1u);
v___x_2580_ = lean_mk_empty_array_with_capacity(v___x_2579_);
v___x_2581_ = lean_array_push(v___x_2580_, v_e_2571_);
v___x_2582_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2577_);
lean_ctor_set(v___x_2582_, 1, v___x_2576_);
lean_ctor_set(v___x_2582_, 2, v___x_2578_);
lean_ctor_set(v___x_2582_, 3, v___x_2581_);
v___x_2583_ = lean_array_push(v___x_2574_, v___x_2582_);
v___x_2584_ = lean_st_ref_set(v___y_2572_, v___x_2583_);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_sz_2575_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2586_, v___y_2587_);
lean_dec(v___y_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2590_, lean_object* v_e_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2591_, v___y_2592_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2599_, lean_object* v_e_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2599_, v_e_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2608_, lean_object* v_todo_2609_, lean_object* v_e_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2608_, v_todo_2609_, v_e_2610_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2618_, lean_object* v_todo_2619_, lean_object* v_e_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
uint8_t v___x_4063__boxed_2627_; lean_object* v_res_2628_; 
v___x_4063__boxed_2627_ = lean_unbox(v___x_2618_);
v_res_2628_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_4063__boxed_2627_, v_todo_2619_, v_e_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2629_, lean_object* v_b_2630_, lean_object* v_x_2631_){
_start:
{
if (lean_obj_tag(v_x_2631_) == 0)
{
lean_dec(v_b_2630_);
lean_dec(v_a_2629_);
return v_x_2631_;
}
else
{
lean_object* v_key_2632_; lean_object* v_value_2633_; lean_object* v_tail_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2646_; 
v_key_2632_ = lean_ctor_get(v_x_2631_, 0);
v_value_2633_ = lean_ctor_get(v_x_2631_, 1);
v_tail_2634_ = lean_ctor_get(v_x_2631_, 2);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_x_2631_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2636_ = v_x_2631_;
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_tail_2634_);
lean_inc(v_value_2633_);
lean_inc(v_key_2632_);
lean_dec(v_x_2631_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2646_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
uint8_t v___x_2638_; 
v___x_2638_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2632_, v_a_2629_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2629_, v_b_2630_, v_tail_2634_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 2, v___x_2639_);
v___x_2641_ = v___x_2636_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_key_2632_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_value_2633_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
else
{
lean_object* v___x_2644_; 
lean_dec(v_value_2633_);
lean_dec(v_key_2632_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 1, v_b_2630_);
lean_ctor_set(v___x_2636_, 0, v_a_2629_);
v___x_2644_ = v___x_2636_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2629_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_b_2630_);
lean_ctor_set(v_reuseFailAlloc_2645_, 2, v_tail_2634_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2647_, lean_object* v_x_2648_){
_start:
{
if (lean_obj_tag(v_x_2648_) == 0)
{
uint8_t v___x_2649_; 
v___x_2649_ = 0;
return v___x_2649_;
}
else
{
lean_object* v_key_2650_; lean_object* v_tail_2651_; uint8_t v___x_2652_; 
v_key_2650_ = lean_ctor_get(v_x_2648_, 0);
v_tail_2651_ = lean_ctor_get(v_x_2648_, 2);
v___x_2652_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2650_, v_a_2647_);
if (v___x_2652_ == 0)
{
v_x_2648_ = v_tail_2651_;
goto _start;
}
else
{
return v___x_2652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2654_, lean_object* v_x_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2654_, v_x_2655_);
lean_dec(v_x_2655_);
lean_dec(v_a_2654_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2658_, lean_object* v_x_2659_){
_start:
{
if (lean_obj_tag(v_x_2659_) == 0)
{
return v_x_2658_;
}
else
{
lean_object* v_key_2660_; lean_object* v_value_2661_; lean_object* v_tail_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2685_; 
v_key_2660_ = lean_ctor_get(v_x_2659_, 0);
v_value_2661_ = lean_ctor_get(v_x_2659_, 1);
v_tail_2662_ = lean_ctor_get(v_x_2659_, 2);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_x_2659_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2664_ = v_x_2659_;
v_isShared_2665_ = v_isSharedCheck_2685_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_tail_2662_);
lean_inc(v_value_2661_);
lean_inc(v_key_2660_);
lean_dec(v_x_2659_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2685_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; uint64_t v___x_2667_; uint64_t v___x_2668_; uint64_t v___x_2669_; uint64_t v_fold_2670_; uint64_t v___x_2671_; uint64_t v___x_2672_; uint64_t v___x_2673_; size_t v___x_2674_; size_t v___x_2675_; size_t v___x_2676_; size_t v___x_2677_; size_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2666_ = lean_array_get_size(v_x_2658_);
v___x_2667_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2660_);
v___x_2668_ = 32ULL;
v___x_2669_ = lean_uint64_shift_right(v___x_2667_, v___x_2668_);
v_fold_2670_ = lean_uint64_xor(v___x_2667_, v___x_2669_);
v___x_2671_ = 16ULL;
v___x_2672_ = lean_uint64_shift_right(v_fold_2670_, v___x_2671_);
v___x_2673_ = lean_uint64_xor(v_fold_2670_, v___x_2672_);
v___x_2674_ = lean_uint64_to_usize(v___x_2673_);
v___x_2675_ = lean_usize_of_nat(v___x_2666_);
v___x_2676_ = ((size_t)1ULL);
v___x_2677_ = lean_usize_sub(v___x_2675_, v___x_2676_);
v___x_2678_ = lean_usize_land(v___x_2674_, v___x_2677_);
v___x_2679_ = lean_array_uget_borrowed(v_x_2658_, v___x_2678_);
lean_inc(v___x_2679_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 2, v___x_2679_);
v___x_2681_ = v___x_2664_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_key_2660_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_value_2661_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_array_uset(v_x_2658_, v___x_2678_, v___x_2681_);
v_x_2658_ = v___x_2682_;
v_x_2659_ = v_tail_2662_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2686_, lean_object* v_source_2687_, lean_object* v_target_2688_){
_start:
{
lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = lean_array_get_size(v_source_2687_);
v___x_2690_ = lean_nat_dec_lt(v_i_2686_, v___x_2689_);
if (v___x_2690_ == 0)
{
lean_dec_ref(v_source_2687_);
lean_dec(v_i_2686_);
return v_target_2688_;
}
else
{
lean_object* v_es_2691_; lean_object* v___x_2692_; lean_object* v_source_2693_; lean_object* v_target_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_es_2691_ = lean_array_fget(v_source_2687_, v_i_2686_);
v___x_2692_ = lean_box(0);
v_source_2693_ = lean_array_fset(v_source_2687_, v_i_2686_, v___x_2692_);
v_target_2694_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2688_, v_es_2691_);
v___x_2695_ = lean_unsigned_to_nat(1u);
v___x_2696_ = lean_nat_add(v_i_2686_, v___x_2695_);
lean_dec(v_i_2686_);
v_i_2686_ = v___x_2696_;
v_source_2687_ = v_source_2693_;
v_target_2688_ = v_target_2694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2698_){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v_nbuckets_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2699_ = lean_array_get_size(v_data_2698_);
v___x_2700_ = lean_unsigned_to_nat(2u);
v_nbuckets_2701_ = lean_nat_mul(v___x_2699_, v___x_2700_);
v___x_2702_ = lean_unsigned_to_nat(0u);
v___x_2703_ = lean_box(0);
v___x_2704_ = lean_mk_array(v_nbuckets_2701_, v___x_2703_);
v___x_2705_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2702_, v_data_2698_, v___x_2704_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2706_, lean_object* v_a_2707_, lean_object* v_b_2708_){
_start:
{
lean_object* v_size_2709_; lean_object* v_buckets_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2753_; 
v_size_2709_ = lean_ctor_get(v_m_2706_, 0);
v_buckets_2710_ = lean_ctor_get(v_m_2706_, 1);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_m_2706_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2712_ = v_m_2706_;
v_isShared_2713_ = v_isSharedCheck_2753_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_buckets_2710_);
lean_inc(v_size_2709_);
lean_dec(v_m_2706_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2753_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; uint64_t v___x_2715_; uint64_t v___x_2716_; uint64_t v___x_2717_; uint64_t v_fold_2718_; uint64_t v___x_2719_; uint64_t v___x_2720_; uint64_t v___x_2721_; size_t v___x_2722_; size_t v___x_2723_; size_t v___x_2724_; size_t v___x_2725_; size_t v___x_2726_; lean_object* v_bkt_2727_; uint8_t v___x_2728_; 
v___x_2714_ = lean_array_get_size(v_buckets_2710_);
v___x_2715_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2707_);
v___x_2716_ = 32ULL;
v___x_2717_ = lean_uint64_shift_right(v___x_2715_, v___x_2716_);
v_fold_2718_ = lean_uint64_xor(v___x_2715_, v___x_2717_);
v___x_2719_ = 16ULL;
v___x_2720_ = lean_uint64_shift_right(v_fold_2718_, v___x_2719_);
v___x_2721_ = lean_uint64_xor(v_fold_2718_, v___x_2720_);
v___x_2722_ = lean_uint64_to_usize(v___x_2721_);
v___x_2723_ = lean_usize_of_nat(v___x_2714_);
v___x_2724_ = ((size_t)1ULL);
v___x_2725_ = lean_usize_sub(v___x_2723_, v___x_2724_);
v___x_2726_ = lean_usize_land(v___x_2722_, v___x_2725_);
v_bkt_2727_ = lean_array_uget_borrowed(v_buckets_2710_, v___x_2726_);
v___x_2728_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2707_, v_bkt_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; lean_object* v_size_x27_2730_; lean_object* v___x_2731_; lean_object* v_buckets_x27_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2729_ = lean_unsigned_to_nat(1u);
v_size_x27_2730_ = lean_nat_add(v_size_2709_, v___x_2729_);
lean_dec(v_size_2709_);
lean_inc(v_bkt_2727_);
v___x_2731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2731_, 0, v_a_2707_);
lean_ctor_set(v___x_2731_, 1, v_b_2708_);
lean_ctor_set(v___x_2731_, 2, v_bkt_2727_);
v_buckets_x27_2732_ = lean_array_uset(v_buckets_2710_, v___x_2726_, v___x_2731_);
v___x_2733_ = lean_unsigned_to_nat(4u);
v___x_2734_ = lean_nat_mul(v_size_x27_2730_, v___x_2733_);
v___x_2735_ = lean_unsigned_to_nat(3u);
v___x_2736_ = lean_nat_div(v___x_2734_, v___x_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_array_get_size(v_buckets_x27_2732_);
v___x_2738_ = lean_nat_dec_le(v___x_2736_, v___x_2737_);
lean_dec(v___x_2736_);
if (v___x_2738_ == 0)
{
lean_object* v_val_2739_; lean_object* v___x_2741_; 
v_val_2739_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2732_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v_val_2739_);
lean_ctor_set(v___x_2712_, 0, v_size_x27_2730_);
v___x_2741_ = v___x_2712_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_size_x27_2730_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_val_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
else
{
lean_object* v___x_2744_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v_buckets_x27_2732_);
lean_ctor_set(v___x_2712_, 0, v_size_x27_2730_);
v___x_2744_ = v___x_2712_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_size_x27_2730_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_buckets_x27_2732_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
else
{
lean_object* v___x_2746_; lean_object* v_buckets_x27_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
lean_inc(v_bkt_2727_);
v___x_2746_ = lean_box(0);
v_buckets_x27_2747_ = lean_array_uset(v_buckets_2710_, v___x_2726_, v___x_2746_);
v___x_2748_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2707_, v_b_2708_, v_bkt_2727_);
v___x_2749_ = lean_array_uset(v_buckets_x27_2747_, v___x_2726_, v___x_2748_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v___x_2749_);
v___x_2751_ = v___x_2712_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_size_2709_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2754_, lean_object* v_x_2755_){
_start:
{
if (lean_obj_tag(v_x_2755_) == 0)
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_box(0);
return v___x_2756_;
}
else
{
lean_object* v_key_2757_; lean_object* v_value_2758_; lean_object* v_tail_2759_; uint8_t v___x_2760_; 
v_key_2757_ = lean_ctor_get(v_x_2755_, 0);
v_value_2758_ = lean_ctor_get(v_x_2755_, 1);
v_tail_2759_ = lean_ctor_get(v_x_2755_, 2);
v___x_2760_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2757_, v_a_2754_);
if (v___x_2760_ == 0)
{
v_x_2755_ = v_tail_2759_;
goto _start;
}
else
{
lean_object* v___x_2762_; 
lean_inc(v_value_2758_);
v___x_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2762_, 0, v_value_2758_);
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2763_, lean_object* v_x_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2763_, v_x_2764_);
lean_dec(v_x_2764_);
lean_dec(v_a_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v_buckets_2768_; lean_object* v___x_2769_; uint64_t v___x_2770_; uint64_t v___x_2771_; uint64_t v___x_2772_; uint64_t v_fold_2773_; uint64_t v___x_2774_; uint64_t v___x_2775_; uint64_t v___x_2776_; size_t v___x_2777_; size_t v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; size_t v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_buckets_2768_ = lean_ctor_get(v_m_2766_, 1);
v___x_2769_ = lean_array_get_size(v_buckets_2768_);
v___x_2770_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2767_);
v___x_2771_ = 32ULL;
v___x_2772_ = lean_uint64_shift_right(v___x_2770_, v___x_2771_);
v_fold_2773_ = lean_uint64_xor(v___x_2770_, v___x_2772_);
v___x_2774_ = 16ULL;
v___x_2775_ = lean_uint64_shift_right(v_fold_2773_, v___x_2774_);
v___x_2776_ = lean_uint64_xor(v_fold_2773_, v___x_2775_);
v___x_2777_ = lean_uint64_to_usize(v___x_2776_);
v___x_2778_ = lean_usize_of_nat(v___x_2769_);
v___x_2779_ = ((size_t)1ULL);
v___x_2780_ = lean_usize_sub(v___x_2778_, v___x_2779_);
v___x_2781_ = lean_usize_land(v___x_2777_, v___x_2780_);
v___x_2782_ = lean_array_uget_borrowed(v_buckets_2768_, v___x_2781_);
v___x_2783_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2767_, v___x_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2784_, v_a_2785_);
lean_dec(v_a_2785_);
lean_dec_ref(v_m_2784_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2787_, lean_object* v_entry_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_snd_2795_; lean_object* v_snd_2796_; lean_object* v_fst_2797_; lean_object* v_fst_2798_; lean_object* v_snd_2799_; lean_object* v_fst_2800_; lean_object* v_fst_2801_; lean_object* v_snd_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
v_snd_2795_ = lean_ctor_get(v_p_2787_, 1);
v_snd_2796_ = lean_ctor_get(v_entry_2788_, 1);
lean_inc(v_snd_2796_);
v_fst_2797_ = lean_ctor_get(v_p_2787_, 0);
v_fst_2798_ = lean_ctor_get(v_snd_2795_, 0);
v_snd_2799_ = lean_ctor_get(v_snd_2795_, 1);
v_fst_2800_ = lean_ctor_get(v_entry_2788_, 0);
lean_inc(v_fst_2800_);
lean_dec_ref(v_entry_2788_);
v_fst_2801_ = lean_ctor_get(v_snd_2796_, 0);
lean_inc(v_fst_2801_);
v_snd_2802_ = lean_ctor_get(v_snd_2796_, 1);
v___x_2803_ = lean_array_get_size(v_fst_2800_);
v___x_2804_ = lean_unsigned_to_nat(0u);
v___x_2805_ = lean_nat_dec_eq(v___x_2803_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v_fst_2806_; lean_object* v_snd_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2912_; 
v_fst_2806_ = lean_ctor_get(v_fst_2801_, 0);
v_snd_2807_ = lean_ctor_get(v_fst_2801_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_fst_2801_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2809_ = v_fst_2801_;
v_isShared_2810_ = v_isSharedCheck_2912_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_snd_2807_);
lean_inc(v_fst_2806_);
lean_dec(v_fst_2801_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2912_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v_e_2814_; lean_object* v_todo_2815_; lean_object* v___x_2816_; lean_object* v___f_2817_; lean_object* v___x_2818_; 
v___x_2811_ = l_Lean_instInhabitedExpr;
v___x_2812_ = lean_unsigned_to_nat(1u);
v___x_2813_ = lean_nat_sub(v___x_2803_, v___x_2812_);
v_e_2814_ = lean_array_get(v___x_2811_, v_fst_2800_, v___x_2813_);
lean_dec(v___x_2813_);
v_todo_2815_ = lean_array_pop(v_fst_2800_);
v___x_2816_ = lean_box(v___x_2805_);
v___f_2817_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2817_, 0, v___x_2816_);
lean_closure_set(v___f_2817_, 1, v_todo_2815_);
lean_closure_set(v___f_2817_, 2, v_e_2814_);
v___x_2818_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2806_, v_snd_2807_, v___f_2817_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v_fst_2820_; lean_object* v_snd_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2903_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2818_);
v_fst_2820_ = lean_ctor_get(v_a_2819_, 0);
v_snd_2821_ = lean_ctor_get(v_a_2819_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_a_2819_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2823_ = v_a_2819_;
v_isShared_2824_ = v_isSharedCheck_2903_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_snd_2821_);
lean_inc(v_fst_2820_);
lean_dec(v_a_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2903_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = lean_box(3);
v___x_2826_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2820_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2799_, v_fst_2820_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v___x_2829_; 
lean_inc(v_snd_2799_);
lean_inc(v_fst_2798_);
lean_inc(v_fst_2797_);
lean_dec_ref(v_p_2787_);
lean_inc(v_snd_2796_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v_snd_2796_);
lean_ctor_set(v___x_2823_, 0, v_snd_2821_);
v___x_2829_ = v___x_2823_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_snd_2821_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_snd_2796_);
v___x_2829_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2849_; 
v_isSharedCheck_2849_ = !lean_is_exclusive(v_snd_2796_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; lean_object* v_unused_2851_; 
v_unused_2850_ = lean_ctor_get(v_snd_2796_, 1);
lean_dec(v_unused_2850_);
v_unused_2851_ = lean_ctor_get(v_snd_2796_, 0);
lean_dec(v_unused_2851_);
v___x_2831_ = v_snd_2796_;
v_isShared_2832_ = v_isSharedCheck_2849_;
goto v_resetjp_2830_;
}
else
{
lean_dec(v_snd_2796_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2849_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2848_; 
v___x_2833_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2829_, v_a_2789_);
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2848_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2848_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2838_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2799_, v_fst_2820_, v_a_2834_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v___x_2838_);
lean_ctor_set(v___x_2809_, 0, v_fst_2798_);
v___x_2840_ = v___x_2809_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_fst_2798_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2842_; 
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v___x_2840_);
lean_ctor_set(v___x_2831_, 0, v_fst_2797_);
v___x_2842_ = v___x_2831_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_fst_2797_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2844_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2842_);
v___x_2844_ = v___x_2836_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2853_; lean_object* v___x_2855_; 
lean_dec(v_fst_2820_);
lean_del_object(v___x_2809_);
v_val_2853_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_val_2853_);
lean_dec_ref(v___x_2827_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v_snd_2796_);
lean_ctor_set(v___x_2823_, 0, v_snd_2821_);
v___x_2855_ = v___x_2823_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_snd_2821_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_snd_2796_);
v___x_2855_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
v___x_2856_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2853_, v___x_2855_, v_a_2789_);
lean_dec(v_val_2853_);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; 
v_unused_2864_ = lean_ctor_get(v___x_2856_, 0);
lean_dec(v_unused_2864_);
v___x_2858_ = v___x_2856_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v___x_2856_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v_p_2787_);
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_p_2787_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
else
{
uint8_t v___x_2866_; 
lean_dec(v_fst_2820_);
v___x_2866_ = lean_nat_dec_eq(v_fst_2798_, v___x_2804_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2868_; 
lean_del_object(v___x_2809_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v_snd_2796_);
lean_ctor_set(v___x_2823_, 0, v_snd_2821_);
v___x_2868_ = v___x_2823_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_snd_2821_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_snd_2796_);
v___x_2868_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
v___x_2869_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2798_, v___x_2868_, v_a_2789_);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2876_ == 0)
{
lean_object* v_unused_2877_; 
v_unused_2877_ = lean_ctor_get(v___x_2869_, 0);
lean_dec(v_unused_2877_);
v___x_2871_ = v___x_2869_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_dec(v___x_2869_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v_p_2787_);
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_p_2787_);
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
else
{
lean_object* v___x_2880_; 
lean_inc(v_snd_2799_);
lean_inc(v_fst_2797_);
lean_dec_ref(v_p_2787_);
lean_inc(v_snd_2796_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v_snd_2796_);
lean_ctor_set(v___x_2823_, 0, v_snd_2821_);
v___x_2880_ = v___x_2823_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_snd_2821_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_snd_2796_);
v___x_2880_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2899_; 
v_isSharedCheck_2899_ = !lean_is_exclusive(v_snd_2796_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; lean_object* v_unused_2901_; 
v_unused_2900_ = lean_ctor_get(v_snd_2796_, 1);
lean_dec(v_unused_2900_);
v_unused_2901_ = lean_ctor_get(v_snd_2796_, 0);
lean_dec(v_unused_2901_);
v___x_2882_ = v_snd_2796_;
v_isShared_2883_ = v_isSharedCheck_2899_;
goto v_resetjp_2881_;
}
else
{
lean_dec(v_snd_2796_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2899_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2898_; 
v___x_2884_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2880_, v_a_2789_);
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2898_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2898_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v_snd_2799_);
lean_ctor_set(v___x_2809_, 0, v_a_2885_);
v___x_2890_ = v___x_2809_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2885_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_snd_2799_);
v___x_2890_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2892_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 1, v___x_2890_);
lean_ctor_set(v___x_2882_, 0, v_fst_2797_);
v___x_2892_ = v___x_2882_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_fst_2797_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2894_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2892_);
v___x_2894_ = v___x_2887_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
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
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_del_object(v___x_2809_);
lean_dec(v_snd_2796_);
lean_dec_ref(v_p_2787_);
v_a_2904_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2818_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2818_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
else
{
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2921_; 
lean_inc(v_snd_2802_);
lean_inc(v_fst_2797_);
lean_inc(v_snd_2795_);
lean_dec(v_fst_2801_);
lean_dec(v_fst_2800_);
lean_dec_ref(v_p_2787_);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_snd_2796_);
if (v_isSharedCheck_2921_ == 0)
{
lean_object* v_unused_2922_; lean_object* v_unused_2923_; 
v_unused_2922_ = lean_ctor_get(v_snd_2796_, 1);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_snd_2796_, 0);
lean_dec(v_unused_2923_);
v___x_2914_ = v_snd_2796_;
v_isShared_2915_ = v_isSharedCheck_2921_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v_snd_2796_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2921_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v_values_2916_; lean_object* v___x_2918_; 
v_values_2916_ = lean_array_push(v_fst_2797_, v_snd_2802_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 1, v_snd_2795_);
lean_ctor_set(v___x_2914_, 0, v_values_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_values_2916_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_snd_2795_);
v___x_2918_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2924_, lean_object* v_entry_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2924_, v_entry_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
lean_dec(v_a_2928_);
lean_dec_ref(v_a_2927_);
lean_dec(v_a_2926_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2933_, lean_object* v_p_2934_, lean_object* v_entry_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2934_, v_entry_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2943_, lean_object* v_p_2944_, lean_object* v_entry_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2943_, v_p_2944_, v_entry_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2953_, lean_object* v_m_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2954_, v_a_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2957_, lean_object* v_m_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2957_, v_m_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_m_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2961_, lean_object* v_m_2962_, lean_object* v_a_2963_, lean_object* v_b_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2962_, v_a_2963_, v_b_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2966_, lean_object* v_a_2967_, lean_object* v_x_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2967_, v_x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2970_, lean_object* v_a_2971_, lean_object* v_x_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_2970_, v_a_2971_, v_x_2972_);
lean_dec(v_x_2972_);
lean_dec(v_a_2971_);
return v_res_2973_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_2974_, lean_object* v_a_2975_, lean_object* v_x_2976_){
_start:
{
uint8_t v___x_2977_; 
v___x_2977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2975_, v_x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2978_, lean_object* v_a_2979_, lean_object* v_x_2980_){
_start:
{
uint8_t v_res_2981_; lean_object* v_r_2982_; 
v_res_2981_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_2978_, v_a_2979_, v_x_2980_);
lean_dec(v_x_2980_);
lean_dec(v_a_2979_);
v_r_2982_ = lean_box(v_res_2981_);
return v_r_2982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_2983_, lean_object* v_data_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_2986_, lean_object* v_a_2987_, lean_object* v_b_2988_, lean_object* v_x_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2987_, v_b_2988_, v_x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_2991_, lean_object* v_i_2992_, lean_object* v_source_2993_, lean_object* v_target_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_2992_, v_source_2993_, v_target_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_2997_, v_x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_3000_, size_t v_i_3001_, size_t v_stop_3002_, lean_object* v_b_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
uint8_t v___x_3010_; 
v___x_3010_ = lean_usize_dec_eq(v_i_3001_, v_stop_3002_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_array_uget_borrowed(v_as_3000_, v_i_3001_);
lean_inc(v___x_3011_);
v___x_3012_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_3003_, v___x_3011_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; size_t v___x_3014_; size_t v___x_3015_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref(v___x_3012_);
v___x_3014_ = ((size_t)1ULL);
v___x_3015_ = lean_usize_add(v_i_3001_, v___x_3014_);
v_i_3001_ = v___x_3015_;
v_b_3003_ = v_a_3013_;
goto _start;
}
else
{
return v___x_3012_;
}
}
else
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_b_3003_);
return v___x_3017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3018_, lean_object* v_i_3019_, lean_object* v_stop_3020_, lean_object* v_b_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
size_t v_i_boxed_3028_; size_t v_stop_boxed_3029_; lean_object* v_res_3030_; 
v_i_boxed_3028_ = lean_unbox_usize(v_i_3019_);
lean_dec(v_i_3019_);
v_stop_boxed_3029_ = lean_unbox_usize(v_stop_3020_);
lean_dec(v_stop_3020_);
v_res_3030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3018_, v_i_boxed_3028_, v_stop_boxed_3029_, v_b_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v_as_3018_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3031_, lean_object* v_starIdx_3032_, lean_object* v_children_3033_, lean_object* v_entries_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v_starIdx_3032_);
lean_ctor_set(v___x_3041_, 1, v_children_3033_);
v___x_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3042_, 0, v_values_3031_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = lean_array_get_size(v_entries_3034_);
v___x_3045_ = lean_nat_dec_lt(v___x_3043_, v___x_3044_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3042_);
return v___x_3046_;
}
else
{
uint8_t v___x_3047_; 
v___x_3047_ = lean_nat_dec_le(v___x_3044_, v___x_3044_);
if (v___x_3047_ == 0)
{
if (v___x_3045_ == 0)
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3042_);
return v___x_3048_;
}
else
{
size_t v___x_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = lean_usize_of_nat(v___x_3044_);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3034_, v___x_3049_, v___x_3050_, v___x_3042_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
return v___x_3051_;
}
}
else
{
size_t v___x_3052_; size_t v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = ((size_t)0ULL);
v___x_3053_ = lean_usize_of_nat(v___x_3044_);
v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3034_, v___x_3052_, v___x_3053_, v___x_3042_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
return v___x_3054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3055_, lean_object* v_starIdx_3056_, lean_object* v_children_3057_, lean_object* v_entries_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3055_, v_starIdx_3056_, v_children_3057_, v_entries_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_entries_3058_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3066_, lean_object* v_values_3067_, lean_object* v_starIdx_3068_, lean_object* v_children_3069_, lean_object* v_entries_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3067_, v_starIdx_3068_, v_children_3069_, v_entries_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3078_, lean_object* v_values_3079_, lean_object* v_starIdx_3080_, lean_object* v_children_3081_, lean_object* v_entries_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3078_, v_values_3079_, v_starIdx_3080_, v_children_3081_, v_entries_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec_ref(v_entries_3082_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3090_, lean_object* v_as_3091_, size_t v_i_3092_, size_t v_stop_3093_, lean_object* v_b_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3091_, v_i_3092_, v_stop_3093_, v_b_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3102_, lean_object* v_as_3103_, lean_object* v_i_3104_, lean_object* v_stop_3105_, lean_object* v_b_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
size_t v_i_boxed_3113_; size_t v_stop_boxed_3114_; lean_object* v_res_3115_; 
v_i_boxed_3113_ = lean_unbox_usize(v_i_3104_);
lean_dec(v_i_3104_);
v_stop_boxed_3114_ = lean_unbox_usize(v_stop_3105_);
lean_dec(v_stop_3105_);
v_res_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3102_, v_as_3103_, v_i_boxed_3113_, v_stop_boxed_3114_, v_b_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v_as_3103_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v_values_3128_; lean_object* v_star_3129_; lean_object* v_children_3130_; lean_object* v_pending_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3161_; 
v___x_3125_ = lean_st_ref_get(v_a_3119_);
v___x_3126_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3127_ = lean_array_get(v___x_3126_, v___x_3125_, v_c_3118_);
lean_dec(v___x_3125_);
v_values_3128_ = lean_ctor_get(v___x_3127_, 0);
v_star_3129_ = lean_ctor_get(v___x_3127_, 1);
v_children_3130_ = lean_ctor_get(v___x_3127_, 2);
v_pending_3131_ = lean_ctor_get(v___x_3127_, 3);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3133_ = v___x_3127_;
v_isShared_3134_ = v_isSharedCheck_3161_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_pending_3131_);
lean_inc(v_children_3130_);
lean_inc(v_star_3129_);
lean_inc(v_values_3128_);
lean_dec(v___x_3127_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3161_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3135_ = lean_array_get_size(v_pending_3131_);
v___x_3136_ = lean_unsigned_to_nat(0u);
v___x_3137_ = lean_nat_dec_eq(v___x_3135_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3118_, v___x_3126_, v_a_3119_);
lean_dec_ref(v___x_3138_);
v___x_3139_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3128_, v_star_3129_, v_children_3130_, v_pending_3131_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_);
lean_dec_ref(v_pending_3131_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v_snd_3141_; lean_object* v_fst_3142_; lean_object* v_fst_3143_; lean_object* v_snd_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3139_);
v_snd_3141_ = lean_ctor_get(v_a_3140_, 1);
v_fst_3142_ = lean_ctor_get(v_a_3140_, 0);
v_fst_3143_ = lean_ctor_get(v_snd_3141_, 0);
v_snd_3144_ = lean_ctor_get(v_snd_3141_, 1);
v___x_3145_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_evalNode___redArg___closed__0));
lean_inc(v_snd_3144_);
lean_inc(v_fst_3143_);
lean_inc(v_fst_3142_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 3, v___x_3145_);
lean_ctor_set(v___x_3133_, 2, v_snd_3144_);
lean_ctor_set(v___x_3133_, 1, v_fst_3143_);
lean_ctor_set(v___x_3133_, 0, v_fst_3142_);
v___x_3147_ = v___x_3133_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_fst_3142_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_fst_3143_);
lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_snd_3144_);
lean_ctor_set(v_reuseFailAlloc_3157_, 3, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
lean_object* v___x_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v___x_3148_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3118_, v___x_3147_, v_a_3119_);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3155_ == 0)
{
lean_object* v_unused_3156_; 
v_unused_3156_ = lean_ctor_get(v___x_3148_, 0);
lean_dec(v_unused_3156_);
v___x_3150_ = v___x_3148_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_dec(v___x_3148_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v_a_3140_);
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3140_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_del_object(v___x_3133_);
return v___x_3139_;
}
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_del_object(v___x_3133_);
lean_dec_ref(v_pending_3131_);
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v_star_3129_);
lean_ctor_set(v___x_3158_, 1, v_children_3130_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_values_3128_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3164_);
lean_dec(v_a_3163_);
lean_dec(v_c_3162_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3170_, lean_object* v_c_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3179_, lean_object* v_c_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3179_, v_c_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
lean_dec(v_a_3185_);
lean_dec_ref(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec_ref(v_a_3182_);
lean_dec(v_a_3181_);
lean_dec(v_c_3180_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3188_, lean_object* v_fallback_3189_, lean_object* v_x_3190_){
_start:
{
if (lean_obj_tag(v_x_3190_) == 0)
{
lean_inc(v_fallback_3189_);
return v_fallback_3189_;
}
else
{
lean_object* v_key_3191_; lean_object* v_value_3192_; lean_object* v_tail_3193_; uint8_t v___x_3194_; 
v_key_3191_ = lean_ctor_get(v_x_3190_, 0);
v_value_3192_ = lean_ctor_get(v_x_3190_, 1);
v_tail_3193_ = lean_ctor_get(v_x_3190_, 2);
v___x_3194_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3191_, v_a_3188_);
if (v___x_3194_ == 0)
{
v_x_3190_ = v_tail_3193_;
goto _start;
}
else
{
lean_inc(v_value_3192_);
return v_value_3192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3196_, lean_object* v_fallback_3197_, lean_object* v_x_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3196_, v_fallback_3197_, v_x_3198_);
lean_dec(v_x_3198_);
lean_dec(v_fallback_3197_);
lean_dec(v_a_3196_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3200_, lean_object* v_a_3201_, lean_object* v_fallback_3202_){
_start:
{
lean_object* v_buckets_3203_; lean_object* v___x_3204_; uint64_t v___x_3205_; uint64_t v___x_3206_; uint64_t v___x_3207_; uint64_t v_fold_3208_; uint64_t v___x_3209_; uint64_t v___x_3210_; uint64_t v___x_3211_; size_t v___x_3212_; size_t v___x_3213_; size_t v___x_3214_; size_t v___x_3215_; size_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_buckets_3203_ = lean_ctor_get(v_m_3200_, 1);
v___x_3204_ = lean_array_get_size(v_buckets_3203_);
v___x_3205_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3201_);
v___x_3206_ = 32ULL;
v___x_3207_ = lean_uint64_shift_right(v___x_3205_, v___x_3206_);
v_fold_3208_ = lean_uint64_xor(v___x_3205_, v___x_3207_);
v___x_3209_ = 16ULL;
v___x_3210_ = lean_uint64_shift_right(v_fold_3208_, v___x_3209_);
v___x_3211_ = lean_uint64_xor(v_fold_3208_, v___x_3210_);
v___x_3212_ = lean_uint64_to_usize(v___x_3211_);
v___x_3213_ = lean_usize_of_nat(v___x_3204_);
v___x_3214_ = ((size_t)1ULL);
v___x_3215_ = lean_usize_sub(v___x_3213_, v___x_3214_);
v___x_3216_ = lean_usize_land(v___x_3212_, v___x_3215_);
v___x_3217_ = lean_array_uget_borrowed(v_buckets_3203_, v___x_3216_);
v___x_3218_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3201_, v_fallback_3202_, v___x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3219_, lean_object* v_a_3220_, lean_object* v_fallback_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3219_, v_a_3220_, v_fallback_3221_);
lean_dec(v_fallback_3221_);
lean_dec(v_a_3220_);
lean_dec_ref(v_m_3219_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3223_, lean_object* v_rest_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = lean_nat_dec_eq(v_next_3223_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3223_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3259_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3259_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3259_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v_snd_3238_; 
v_snd_3238_ = lean_ctor_get(v_a_3234_, 1);
lean_inc(v_snd_3238_);
lean_dec(v_a_3234_);
if (lean_obj_tag(v_rest_3224_) == 0)
{
lean_object* v_fst_3239_; lean_object* v_snd_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v_fst_3239_ = lean_ctor_get(v_snd_3238_, 0);
lean_inc(v_fst_3239_);
v_snd_3240_ = lean_ctor_get(v_snd_3238_, 1);
lean_inc(v_snd_3240_);
lean_dec(v_snd_3238_);
v___x_3241_ = lean_st_ref_take(v_a_3225_);
v___x_3242_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3242_);
lean_ctor_set(v___x_3243_, 1, v_fst_3239_);
lean_ctor_set(v___x_3243_, 2, v_snd_3240_);
lean_ctor_set(v___x_3243_, 3, v___x_3242_);
v___x_3244_ = lean_array_set(v___x_3241_, v_next_3223_, v___x_3243_);
lean_dec(v_next_3223_);
v___x_3245_ = lean_st_ref_set(v_a_3225_, v___x_3244_);
v___x_3246_ = lean_box(0);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3246_);
v___x_3248_ = v___x_3236_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
else
{
lean_object* v_fst_3250_; lean_object* v_snd_3251_; lean_object* v_head_3252_; lean_object* v_tail_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
lean_del_object(v___x_3236_);
lean_dec(v_next_3223_);
v_fst_3250_ = lean_ctor_get(v_snd_3238_, 0);
lean_inc(v_fst_3250_);
v_snd_3251_ = lean_ctor_get(v_snd_3238_, 1);
lean_inc(v_snd_3251_);
lean_dec(v_snd_3238_);
v_head_3252_ = lean_ctor_get(v_rest_3224_, 0);
v_tail_3253_ = lean_ctor_get(v_rest_3224_, 1);
v___x_3254_ = lean_box(3);
v___x_3255_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3252_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; 
lean_dec(v_fst_3250_);
v___x_3256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3251_, v_head_3252_, v___x_3231_);
lean_dec(v_snd_3251_);
v_next_3223_ = v___x_3256_;
v_rest_3224_ = v_tail_3253_;
goto _start;
}
else
{
lean_dec(v_snd_3251_);
v_next_3223_ = v_fst_3250_;
v_rest_3224_ = v_tail_3253_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_next_3223_);
v_a_3260_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3233_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3233_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_dec(v_next_3223_);
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
return v___x_3269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3270_, lean_object* v_rest_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3270_, v_rest_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
lean_dec(v_a_3272_);
lean_dec(v_rest_3271_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3279_, lean_object* v_next_3280_, lean_object* v_rest_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3280_, v_rest_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3289_, lean_object* v_next_3290_, lean_object* v_rest_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3289_, v_next_3290_, v_rest_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec(v_rest_3291_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3299_, lean_object* v_m_3300_, lean_object* v_a_3301_, lean_object* v_fallback_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3300_, v_a_3301_, v_fallback_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3304_, lean_object* v_m_3305_, lean_object* v_a_3306_, lean_object* v_fallback_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3304_, v_m_3305_, v_a_3306_, v_fallback_3307_);
lean_dec(v_fallback_3307_);
lean_dec(v_a_3306_);
lean_dec_ref(v_m_3305_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3309_, lean_object* v_a_3310_, lean_object* v_fallback_3311_, lean_object* v_x_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3310_, v_fallback_3311_, v_x_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3314_, lean_object* v_a_3315_, lean_object* v_fallback_3316_, lean_object* v_x_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3314_, v_a_3315_, v_fallback_3316_, v_x_3317_);
lean_dec(v_x_3317_);
lean_dec(v_fallback_3316_);
lean_dec(v_a_3315_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3319_, lean_object* v_path_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
if (lean_obj_tag(v_path_3320_) == 0)
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_t_3319_);
return v___x_3326_;
}
else
{
lean_object* v_head_3327_; lean_object* v_tail_3328_; lean_object* v_roots_3329_; lean_object* v___x_3330_; lean_object* v_idx_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_head_3327_ = lean_ctor_get(v_path_3320_, 0);
lean_inc(v_head_3327_);
v_tail_3328_ = lean_ctor_get(v_path_3320_, 1);
lean_inc(v_tail_3328_);
lean_dec_ref(v_path_3320_);
v_roots_3329_ = lean_ctor_get(v_t_3319_, 1);
v___x_3330_ = lean_unsigned_to_nat(0u);
v_idx_3331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3329_, v_head_3327_, v___x_3330_);
lean_dec(v_head_3327_);
v___x_3332_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3332_, 0, lean_box(0));
lean_closure_set(v___x_3332_, 1, v_idx_3331_);
lean_closure_set(v___x_3332_, 2, v_tail_3328_);
v___x_3333_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3319_, v___x_3332_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3342_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_snd_3338_; lean_object* v___x_3340_; 
v_snd_3338_ = lean_ctor_get(v_a_3334_, 1);
lean_inc(v_snd_3338_);
lean_dec(v_a_3334_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v_snd_3338_);
v___x_3340_ = v___x_3336_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_snd_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
v_a_3343_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3333_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3333_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3351_, lean_object* v_path_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3351_, v_path_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3359_, lean_object* v_t_3360_, lean_object* v_path_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3360_, v_path_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3368_, lean_object* v_t_3369_, lean_object* v_path_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3368_, v_t_3369_, v_path_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3379_, lean_object* v_e_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3382_ = lean_array_get_size(v_a_3381_);
v___x_3383_ = lean_nat_dec_lt(v___x_3382_, v_score_3379_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3384_ = lean_unsigned_to_nat(1u);
v___x_3385_ = lean_mk_empty_array_with_capacity(v___x_3384_);
v___x_3386_ = lean_array_push(v___x_3385_, v_e_3380_);
v___x_3387_ = lean_array_push(v_a_3381_, v___x_3386_);
return v___x_3387_;
}
else
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3389_ = lean_array_push(v_a_3381_, v___x_3388_);
v_a_3381_ = v___x_3389_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3391_, lean_object* v_e_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3391_, v_e_3392_, v_a_3393_);
lean_dec(v_score_3391_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3395_, lean_object* v_score_3396_, lean_object* v_e_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3396_, v_e_3397_, v_a_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3400_, lean_object* v_score_3401_, lean_object* v_e_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3400_, v_score_3401_, v_e_3402_, v_a_3403_);
lean_dec(v_score_3401_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3405_, lean_object* v_score_3406_, lean_object* v_e_3407_){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v___x_3408_ = lean_array_get_size(v_e_3407_);
v___x_3409_ = lean_unsigned_to_nat(0u);
v___x_3410_ = lean_nat_dec_eq(v___x_3408_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; uint8_t v___x_3412_; 
v___x_3411_ = lean_array_get_size(v_r_3405_);
v___x_3412_ = lean_nat_dec_lt(v_score_3406_, v___x_3411_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; 
v___x_3413_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3406_, v_e_3407_, v_r_3405_);
return v___x_3413_;
}
else
{
if (v___x_3412_ == 0)
{
lean_dec_ref(v_e_3407_);
return v_r_3405_;
}
else
{
lean_object* v_v_3414_; lean_object* v___x_3415_; lean_object* v_xs_x27_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v_v_3414_ = lean_array_fget(v_r_3405_, v_score_3406_);
v___x_3415_ = lean_box(0);
v_xs_x27_3416_ = lean_array_fset(v_r_3405_, v_score_3406_, v___x_3415_);
v___x_3417_ = lean_array_push(v_v_3414_, v_e_3407_);
v___x_3418_ = lean_array_fset(v_xs_x27_3416_, v_score_3406_, v___x_3417_);
return v___x_3418_;
}
}
}
else
{
lean_dec_ref(v_e_3407_);
return v_r_3405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3419_, lean_object* v_score_3420_, lean_object* v_e_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3419_, v_score_3420_, v_e_3421_);
lean_dec(v_score_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3423_, lean_object* v_r_3424_, lean_object* v_score_3425_, lean_object* v_e_3426_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3424_, v_score_3425_, v_e_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3428_, lean_object* v_r_3429_, lean_object* v_score_3430_, lean_object* v_e_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3428_, v_r_3429_, v_score_3430_, v_e_3431_);
lean_dec(v_score_3430_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3433_, size_t v_i_3434_, size_t v_stop_3435_, lean_object* v_b_3436_){
_start:
{
uint8_t v___x_3437_; 
v___x_3437_ = lean_usize_dec_eq(v_i_3434_, v_stop_3435_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; size_t v___x_3441_; size_t v___x_3442_; 
v___x_3438_ = lean_array_uget_borrowed(v_as_3433_, v_i_3434_);
v___x_3439_ = lean_array_get_size(v___x_3438_);
v___x_3440_ = lean_nat_add(v_b_3436_, v___x_3439_);
lean_dec(v_b_3436_);
v___x_3441_ = ((size_t)1ULL);
v___x_3442_ = lean_usize_add(v_i_3434_, v___x_3441_);
v_i_3434_ = v___x_3442_;
v_b_3436_ = v___x_3440_;
goto _start;
}
else
{
return v_b_3436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3444_, lean_object* v_i_3445_, lean_object* v_stop_3446_, lean_object* v_b_3447_){
_start:
{
size_t v_i_boxed_3448_; size_t v_stop_boxed_3449_; lean_object* v_res_3450_; 
v_i_boxed_3448_ = lean_unbox_usize(v_i_3445_);
lean_dec(v_i_3445_);
v_stop_boxed_3449_ = lean_unbox_usize(v_stop_3446_);
lean_dec(v_stop_3446_);
v_res_3450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3444_, v_i_boxed_3448_, v_stop_boxed_3449_, v_b_3447_);
lean_dec_ref(v_as_3444_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3451_, size_t v_i_3452_, size_t v_stop_3453_, lean_object* v_b_3454_){
_start:
{
lean_object* v___y_3456_; uint8_t v___x_3460_; 
v___x_3460_ = lean_usize_dec_eq(v_i_3452_, v_stop_3453_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v___x_3461_ = lean_array_uget_borrowed(v_as_3451_, v_i_3452_);
v___x_3462_ = lean_unsigned_to_nat(0u);
v___x_3463_ = lean_array_get_size(v___x_3461_);
v___x_3464_ = lean_nat_dec_lt(v___x_3462_, v___x_3463_);
if (v___x_3464_ == 0)
{
v___y_3456_ = v_b_3454_;
goto v___jp_3455_;
}
else
{
uint8_t v___x_3465_; 
v___x_3465_ = lean_nat_dec_le(v___x_3463_, v___x_3463_);
if (v___x_3465_ == 0)
{
if (v___x_3464_ == 0)
{
v___y_3456_ = v_b_3454_;
goto v___jp_3455_;
}
else
{
size_t v___x_3466_; size_t v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = ((size_t)0ULL);
v___x_3467_ = lean_usize_of_nat(v___x_3463_);
v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3461_, v___x_3466_, v___x_3467_, v_b_3454_);
v___y_3456_ = v___x_3468_;
goto v___jp_3455_;
}
}
else
{
size_t v___x_3469_; size_t v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = ((size_t)0ULL);
v___x_3470_ = lean_usize_of_nat(v___x_3463_);
v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3461_, v___x_3469_, v___x_3470_, v_b_3454_);
v___y_3456_ = v___x_3471_;
goto v___jp_3455_;
}
}
}
else
{
return v_b_3454_;
}
v___jp_3455_:
{
size_t v___x_3457_; size_t v___x_3458_; 
v___x_3457_ = ((size_t)1ULL);
v___x_3458_ = lean_usize_add(v_i_3452_, v___x_3457_);
v_i_3452_ = v___x_3458_;
v_b_3454_ = v___y_3456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3472_, lean_object* v_i_3473_, lean_object* v_stop_3474_, lean_object* v_b_3475_){
_start:
{
size_t v_i_boxed_3476_; size_t v_stop_boxed_3477_; lean_object* v_res_3478_; 
v_i_boxed_3476_ = lean_unbox_usize(v_i_3473_);
lean_dec(v_i_3473_);
v_stop_boxed_3477_ = lean_unbox_usize(v_stop_3474_);
lean_dec(v_stop_3474_);
v_res_3478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3472_, v_i_boxed_3476_, v_stop_boxed_3477_, v_b_3475_);
lean_dec_ref(v_as_3472_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3479_){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; 
v___x_3480_ = lean_unsigned_to_nat(0u);
v___x_3481_ = lean_array_get_size(v_mr_3479_);
v___x_3482_ = lean_nat_dec_lt(v___x_3480_, v___x_3481_);
if (v___x_3482_ == 0)
{
return v___x_3480_;
}
else
{
uint8_t v___x_3483_; 
v___x_3483_ = lean_nat_dec_le(v___x_3481_, v___x_3481_);
if (v___x_3483_ == 0)
{
if (v___x_3482_ == 0)
{
return v___x_3480_;
}
else
{
size_t v___x_3484_; size_t v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = ((size_t)0ULL);
v___x_3485_ = lean_usize_of_nat(v___x_3481_);
v___x_3486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3479_, v___x_3484_, v___x_3485_, v___x_3480_);
return v___x_3486_;
}
}
else
{
size_t v___x_3487_; size_t v___x_3488_; lean_object* v___x_3489_; 
v___x_3487_ = ((size_t)0ULL);
v___x_3488_ = lean_usize_of_nat(v___x_3481_);
v___x_3489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3479_, v___x_3487_, v___x_3488_, v___x_3480_);
return v___x_3489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3490_);
lean_dec_ref(v_mr_3490_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3492_, lean_object* v_mr_3493_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3495_, lean_object* v_mr_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3495_, v_mr_3496_);
lean_dec_ref(v_mr_3496_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3498_, lean_object* v_as_3499_, size_t v_i_3500_, size_t v_stop_3501_, lean_object* v_b_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3499_, v_i_3500_, v_stop_3501_, v_b_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3504_, lean_object* v_as_3505_, lean_object* v_i_3506_, lean_object* v_stop_3507_, lean_object* v_b_3508_){
_start:
{
size_t v_i_boxed_3509_; size_t v_stop_boxed_3510_; lean_object* v_res_3511_; 
v_i_boxed_3509_ = lean_unbox_usize(v_i_3506_);
lean_dec(v_i_3506_);
v_stop_boxed_3510_ = lean_unbox_usize(v_stop_3507_);
lean_dec(v_stop_3507_);
v_res_3511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3504_, v_as_3505_, v_i_boxed_3509_, v_stop_boxed_3510_, v_b_3508_);
lean_dec_ref(v_as_3505_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3512_, lean_object* v_as_3513_, size_t v_i_3514_, size_t v_stop_3515_, lean_object* v_b_3516_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3513_, v_i_3514_, v_stop_3515_, v_b_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3518_, lean_object* v_as_3519_, lean_object* v_i_3520_, lean_object* v_stop_3521_, lean_object* v_b_3522_){
_start:
{
size_t v_i_boxed_3523_; size_t v_stop_boxed_3524_; lean_object* v_res_3525_; 
v_i_boxed_3523_ = lean_unbox_usize(v_i_3520_);
lean_dec(v_i_3520_);
v_stop_boxed_3524_ = lean_unbox_usize(v_stop_3521_);
lean_dec(v_stop_3521_);
v_res_3525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3518_, v_as_3519_, v_i_boxed_3523_, v_stop_boxed_3524_, v_b_3522_);
lean_dec_ref(v_as_3519_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3526_, lean_object* v_j_3527_, lean_object* v_x_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_apply_2(v_f_3526_, v_j_3527_, v_x_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3549_, lean_object* v_x1_3550_, lean_object* v_x2_3551_){
_start:
{
lean_object* v___x_3552_; size_t v_sz_3553_; size_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3552_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3553_ = lean_array_size(v_x2_3551_);
v___x_3554_ = ((size_t)0ULL);
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3552_, v___f_3549_, v_sz_3553_, v___x_3554_, v_x2_3551_);
v___x_3556_ = l_Array_append___redArg(v_x1_3550_, v___x_3555_);
lean_dec(v___x_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3557_, lean_object* v_mr_3558_, lean_object* v_f_3559_, lean_object* v_i_3560_, lean_object* v_x_3561_, lean_object* v_r_3562_){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v_j_3565_; lean_object* v_b_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3563_ = lean_unsigned_to_nat(1u);
v___x_3564_ = lean_nat_sub(v_n_3557_, v___x_3563_);
v_j_3565_ = lean_nat_sub(v___x_3564_, v_i_3560_);
lean_dec(v___x_3564_);
v_b_3566_ = lean_array_fget_borrowed(v_mr_3558_, v_j_3565_);
v___x_3567_ = lean_unsigned_to_nat(0u);
v___x_3568_ = lean_array_get_size(v_b_3566_);
v___x_3569_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3570_ = lean_nat_dec_lt(v___x_3567_, v___x_3568_);
if (v___x_3570_ == 0)
{
lean_dec(v_j_3565_);
lean_dec(v_f_3559_);
return v_r_3562_;
}
else
{
lean_object* v___f_3571_; lean_object* v___f_3572_; uint8_t v___x_3573_; 
v___f_3571_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3571_, 0, v_f_3559_);
lean_closure_set(v___f_3571_, 1, v_j_3565_);
v___f_3572_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3572_, 0, v___f_3571_);
v___x_3573_ = lean_nat_dec_le(v___x_3568_, v___x_3568_);
if (v___x_3573_ == 0)
{
if (v___x_3570_ == 0)
{
lean_dec_ref(v___f_3572_);
return v_r_3562_;
}
else
{
size_t v___x_3574_; size_t v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = ((size_t)0ULL);
v___x_3575_ = lean_usize_of_nat(v___x_3568_);
lean_inc(v_b_3566_);
v___x_3576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3569_, v___f_3572_, v_b_3566_, v___x_3574_, v___x_3575_, v_r_3562_);
return v___x_3576_;
}
}
else
{
size_t v___x_3577_; size_t v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = ((size_t)0ULL);
v___x_3578_ = lean_usize_of_nat(v___x_3568_);
lean_inc(v_b_3566_);
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3569_, v___f_3572_, v_b_3566_, v___x_3577_, v___x_3578_, v_r_3562_);
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3580_, lean_object* v_mr_3581_, lean_object* v_f_3582_, lean_object* v_i_3583_, lean_object* v_x_3584_, lean_object* v_r_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3580_, v_mr_3581_, v_f_3582_, v_i_3583_, v_x_3584_, v_r_3585_);
lean_dec(v_i_3583_);
lean_dec_ref(v_mr_3581_);
lean_dec(v_n_3580_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3587_, lean_object* v_a_3588_, lean_object* v_f_3589_){
_start:
{
lean_object* v_n_3590_; lean_object* v___f_3591_; lean_object* v___x_3592_; 
v_n_3590_ = lean_array_get_size(v_mr_3587_);
v___f_3591_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3591_, 0, v_n_3590_);
lean_closure_set(v___f_3591_, 1, v_mr_3587_);
lean_closure_set(v___f_3591_, 2, v_f_3589_);
v___x_3592_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3590_, v___f_3591_, v_n_3590_, lean_box(0), v_a_3588_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3593_, lean_object* v_00_u03b2_3594_, lean_object* v_mr_3595_, lean_object* v_a_3596_, lean_object* v_f_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3595_, v_a_3596_, v_f_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3599_, size_t v_i_3600_, lean_object* v_bs_3601_){
_start:
{
uint8_t v___x_3602_; 
v___x_3602_ = lean_usize_dec_lt(v_i_3600_, v_sz_3599_);
if (v___x_3602_ == 0)
{
return v_bs_3601_;
}
else
{
lean_object* v_v_3603_; lean_object* v___x_3604_; lean_object* v_bs_x27_3605_; size_t v___x_3606_; size_t v___x_3607_; lean_object* v___x_3608_; 
v_v_3603_ = lean_array_uget(v_bs_3601_, v_i_3600_);
v___x_3604_ = lean_unsigned_to_nat(0u);
v_bs_x27_3605_ = lean_array_uset(v_bs_3601_, v_i_3600_, v___x_3604_);
v___x_3606_ = ((size_t)1ULL);
v___x_3607_ = lean_usize_add(v_i_3600_, v___x_3606_);
v___x_3608_ = lean_array_uset(v_bs_x27_3605_, v_i_3600_, v_v_3603_);
v_i_3600_ = v___x_3607_;
v_bs_3601_ = v___x_3608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3610_, lean_object* v_i_3611_, lean_object* v_bs_3612_){
_start:
{
size_t v_sz_boxed_3613_; size_t v_i_boxed_3614_; lean_object* v_res_3615_; 
v_sz_boxed_3613_ = lean_unbox_usize(v_sz_3610_);
lean_dec(v_sz_3610_);
v_i_boxed_3614_ = lean_unbox_usize(v_i_3611_);
lean_dec(v_i_3611_);
v_res_3615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3613_, v_i_boxed_3614_, v_bs_3612_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3616_, size_t v_i_3617_, size_t v_stop_3618_, lean_object* v_b_3619_){
_start:
{
uint8_t v___x_3620_; 
v___x_3620_ = lean_usize_dec_eq(v_i_3617_, v_stop_3618_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; size_t v_sz_3622_; size_t v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; size_t v___x_3626_; size_t v___x_3627_; 
v___x_3621_ = lean_array_uget_borrowed(v_as_3616_, v_i_3617_);
v_sz_3622_ = lean_array_size(v___x_3621_);
v___x_3623_ = ((size_t)0ULL);
lean_inc(v___x_3621_);
v___x_3624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3622_, v___x_3623_, v___x_3621_);
v___x_3625_ = l_Array_append___redArg(v_b_3619_, v___x_3624_);
lean_dec_ref(v___x_3624_);
v___x_3626_ = ((size_t)1ULL);
v___x_3627_ = lean_usize_add(v_i_3617_, v___x_3626_);
v_i_3617_ = v___x_3627_;
v_b_3619_ = v___x_3625_;
goto _start;
}
else
{
return v_b_3619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3629_, lean_object* v_i_3630_, lean_object* v_stop_3631_, lean_object* v_b_3632_){
_start:
{
size_t v_i_boxed_3633_; size_t v_stop_boxed_3634_; lean_object* v_res_3635_; 
v_i_boxed_3633_ = lean_unbox_usize(v_i_3630_);
lean_dec(v_i_3630_);
v_stop_boxed_3634_ = lean_unbox_usize(v_stop_3631_);
lean_dec(v_stop_3631_);
v_res_3635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3629_, v_i_boxed_3633_, v_stop_boxed_3634_, v_b_3632_);
lean_dec_ref(v_as_3629_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3636_, lean_object* v_aa_3637_, lean_object* v_n_3638_, lean_object* v_j_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v_zero_3641_; uint8_t v_isZero_3642_; 
v_zero_3641_ = lean_unsigned_to_nat(0u);
v_isZero_3642_ = lean_nat_dec_eq(v_j_3639_, v_zero_3641_);
if (v_isZero_3642_ == 1)
{
lean_dec(v_j_3639_);
return v_a_3640_;
}
else
{
lean_object* v_one_3643_; lean_object* v_n_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_j_3647_; lean_object* v_b_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v_one_3643_ = lean_unsigned_to_nat(1u);
v_n_3644_ = lean_nat_sub(v_j_3639_, v_one_3643_);
v___x_3645_ = lean_nat_sub(v_n_3638_, v_j_3639_);
lean_dec(v_j_3639_);
v___x_3646_ = lean_nat_sub(v_n_3636_, v_one_3643_);
v_j_3647_ = lean_nat_sub(v___x_3646_, v___x_3645_);
lean_dec(v___x_3645_);
lean_dec(v___x_3646_);
v_b_3648_ = lean_array_fget_borrowed(v_aa_3637_, v_j_3647_);
lean_dec(v_j_3647_);
v___x_3649_ = lean_array_get_size(v_b_3648_);
v___x_3650_ = lean_nat_dec_lt(v_zero_3641_, v___x_3649_);
if (v___x_3650_ == 0)
{
v_j_3639_ = v_n_3644_;
goto _start;
}
else
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_nat_dec_le(v___x_3649_, v___x_3649_);
if (v___x_3652_ == 0)
{
if (v___x_3650_ == 0)
{
v_j_3639_ = v_n_3644_;
goto _start;
}
else
{
size_t v___x_3654_; size_t v___x_3655_; lean_object* v___x_3656_; 
v___x_3654_ = ((size_t)0ULL);
v___x_3655_ = lean_usize_of_nat(v___x_3649_);
v___x_3656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3648_, v___x_3654_, v___x_3655_, v_a_3640_);
v_j_3639_ = v_n_3644_;
v_a_3640_ = v___x_3656_;
goto _start;
}
}
else
{
size_t v___x_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = ((size_t)0ULL);
v___x_3659_ = lean_usize_of_nat(v___x_3649_);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3648_, v___x_3658_, v___x_3659_, v_a_3640_);
v_j_3639_ = v_n_3644_;
v_a_3640_ = v___x_3660_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3662_, lean_object* v_aa_3663_, lean_object* v_n_3664_, lean_object* v_j_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3662_, v_aa_3663_, v_n_3664_, v_j_3665_, v_a_3666_);
lean_dec(v_n_3664_);
lean_dec_ref(v_aa_3663_);
lean_dec(v_n_3662_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v_n_3670_; lean_object* v___x_3671_; 
v_n_3670_ = lean_array_get_size(v_mr_3668_);
v___x_3671_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3670_, v_mr_3668_, v_n_3670_, v_n_3670_, v_a_3669_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3672_, v_a_3673_);
lean_dec_ref(v_mr_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3675_, v_a_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3678_, v_a_3679_);
lean_dec_ref(v_mr_3678_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3681_, lean_object* v_mr_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3682_, v_a_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3685_, lean_object* v_mr_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3685_, v_mr_3686_, v_a_3687_);
lean_dec_ref(v_mr_3686_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3689_, lean_object* v_mr_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3690_, v_a_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3693_, lean_object* v_mr_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3693_, v_mr_3694_, v_a_3695_);
lean_dec_ref(v_mr_3694_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3697_, size_t v_sz_3698_, size_t v_i_3699_, lean_object* v_bs_3700_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3698_, v_i_3699_, v_bs_3700_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3702_, lean_object* v_sz_3703_, lean_object* v_i_3704_, lean_object* v_bs_3705_){
_start:
{
size_t v_sz_boxed_3706_; size_t v_i_boxed_3707_; lean_object* v_res_3708_; 
v_sz_boxed_3706_ = lean_unbox_usize(v_sz_3703_);
lean_dec(v_sz_3703_);
v_i_boxed_3707_ = lean_unbox_usize(v_i_3704_);
lean_dec(v_i_3704_);
v_res_3708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3702_, v_sz_boxed_3706_, v_i_boxed_3707_, v_bs_3705_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3709_, lean_object* v_as_3710_, size_t v_i_3711_, size_t v_stop_3712_, lean_object* v_b_3713_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3710_, v_i_3711_, v_stop_3712_, v_b_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3715_, lean_object* v_as_3716_, lean_object* v_i_3717_, lean_object* v_stop_3718_, lean_object* v_b_3719_){
_start:
{
size_t v_i_boxed_3720_; size_t v_stop_boxed_3721_; lean_object* v_res_3722_; 
v_i_boxed_3720_ = lean_unbox_usize(v_i_3717_);
lean_dec(v_i_3717_);
v_stop_boxed_3721_ = lean_unbox_usize(v_stop_3718_);
lean_dec(v_stop_3718_);
v_res_3722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3715_, v_as_3716_, v_i_boxed_3720_, v_stop_boxed_3721_, v_b_3719_);
lean_dec_ref(v_as_3716_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3723_, lean_object* v_n_3724_, lean_object* v_aa_3725_, lean_object* v_n_3726_, lean_object* v_j_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3724_, v_aa_3725_, v_n_3726_, v_j_3727_, v_a_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3731_, lean_object* v_n_3732_, lean_object* v_aa_3733_, lean_object* v_n_3734_, lean_object* v_j_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3731_, v_n_3732_, v_aa_3733_, v_n_3734_, v_j_3735_, v_a_3736_, v_a_3737_);
lean_dec(v_n_3734_);
lean_dec_ref(v_aa_3733_);
lean_dec(v_n_3732_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3746_, lean_object* v___x_3747_, lean_object* v_score_3748_, lean_object* v___x_3749_, lean_object* v_k_3750_, lean_object* v_args_3751_, lean_object* v_cases_3752_){
_start:
{
lean_object* v___x_3753_; 
v___x_3753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3746_, v_k_3750_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_dec_ref(v___x_3747_);
return v_cases_3752_;
}
else
{
lean_object* v_val_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_val_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_val_3754_);
lean_dec_ref(v___x_3753_);
v___x_3755_ = l_Array_append___redArg(v___x_3747_, v_args_3751_);
v___x_3756_ = lean_nat_add(v_score_3748_, v___x_3749_);
v___x_3757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3755_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
lean_ctor_set(v___x_3757_, 2, v_val_3754_);
v___x_3758_ = lean_array_push(v_cases_3752_, v___x_3757_);
return v___x_3758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3759_, lean_object* v___x_3760_, lean_object* v_score_3761_, lean_object* v___x_3762_, lean_object* v_k_3763_, lean_object* v_args_3764_, lean_object* v_cases_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3759_, v___x_3760_, v_score_3761_, v___x_3762_, v_k_3763_, v_args_3764_, v_cases_3765_);
lean_dec_ref(v_args_3764_);
lean_dec(v_k_3763_);
lean_dec(v___x_3762_);
lean_dec(v_score_3761_);
lean_dec_ref(v_snd_3759_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3767_, lean_object* v_result_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3775_ = lean_array_get_size(v_cases_3767_);
v___x_3776_ = lean_unsigned_to_nat(0u);
v___x_3777_ = lean_nat_dec_eq(v___x_3775_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v_ca_3781_; lean_object* v_todo_3782_; lean_object* v_score_3783_; lean_object* v_c_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3850_; 
v___x_3778_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3779_ = lean_unsigned_to_nat(1u);
v___x_3780_ = lean_nat_sub(v___x_3775_, v___x_3779_);
v_ca_3781_ = lean_array_get(v___x_3778_, v_cases_3767_, v___x_3780_);
lean_dec(v___x_3780_);
v_todo_3782_ = lean_ctor_get(v_ca_3781_, 0);
v_score_3783_ = lean_ctor_get(v_ca_3781_, 1);
v_c_3784_ = lean_ctor_get(v_ca_3781_, 2);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_ca_3781_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3786_ = v_ca_3781_;
v_isShared_3787_ = v_isSharedCheck_3850_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_c_3784_);
lean_inc(v_score_3783_);
lean_inc(v_todo_3782_);
lean_dec(v_ca_3781_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3850_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3784_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
lean_dec(v_c_3784_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; uint8_t v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v_snd_3817_; lean_object* v_fst_3818_; lean_object* v_fst_3819_; lean_object* v_snd_3820_; lean_object* v_cases_3821_; lean_object* v___x_3822_; uint8_t v___y_3824_; uint8_t v___x_3836_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref(v___x_3788_);
v_snd_3817_ = lean_ctor_get(v_a_3789_, 1);
lean_inc(v_snd_3817_);
v_fst_3818_ = lean_ctor_get(v_a_3789_, 0);
lean_inc(v_fst_3818_);
lean_dec(v_a_3789_);
v_fst_3819_ = lean_ctor_get(v_snd_3817_, 0);
lean_inc(v_fst_3819_);
v_snd_3820_ = lean_ctor_get(v_snd_3817_, 1);
lean_inc(v_snd_3820_);
lean_dec(v_snd_3817_);
v_cases_3821_ = lean_array_pop(v_cases_3767_);
v___x_3822_ = lean_array_get_size(v_todo_3782_);
v___x_3836_ = lean_nat_dec_eq(v___x_3822_, v___x_3776_);
if (v___x_3836_ == 0)
{
uint8_t v___x_3837_; 
lean_dec(v_fst_3818_);
v___x_3837_ = lean_nat_dec_eq(v_fst_3819_, v___x_3776_);
if (v___x_3837_ == 0)
{
v___y_3824_ = v___x_3837_;
goto v___jp_3823_;
}
else
{
lean_object* v_size_3838_; uint8_t v___x_3839_; 
v_size_3838_ = lean_ctor_get(v_snd_3820_, 0);
v___x_3839_ = lean_nat_dec_eq(v_size_3838_, v___x_3776_);
v___y_3824_ = v___x_3839_;
goto v___jp_3823_;
}
}
else
{
lean_object* v___x_3840_; 
lean_dec(v_snd_3820_);
lean_dec(v_fst_3819_);
lean_del_object(v___x_3786_);
lean_dec_ref(v_todo_3782_);
v___x_3840_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3768_, v_score_3783_, v_fst_3818_);
lean_dec(v_score_3783_);
v_cases_3767_ = v_cases_3821_;
v_result_3768_ = v___x_3840_;
goto _start;
}
v___jp_3790_:
{
uint8_t v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = 1;
v___x_3796_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3792_, v___x_3795_, v___y_3791_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v_fst_3798_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref(v___x_3796_);
v_fst_3798_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_fst_3798_);
switch(lean_obj_tag(v_fst_3798_))
{
case 3:
{
lean_dec(v_a_3797_);
lean_dec_ref(v___y_3793_);
v_cases_3767_ = v___y_3794_;
goto _start;
}
case 5:
{
lean_object* v_snd_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_snd_3800_ = lean_ctor_get(v_a_3797_, 1);
lean_inc(v_snd_3800_);
lean_dec(v_a_3797_);
v___x_3801_ = lean_box(4);
v___x_3802_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3793_);
v___x_3803_ = lean_apply_3(v___y_3793_, v___x_3801_, v___x_3802_, v___y_3794_);
v___x_3804_ = lean_apply_3(v___y_3793_, v_fst_3798_, v_snd_3800_, v___x_3803_);
v_cases_3767_ = v___x_3804_;
goto _start;
}
default: 
{
lean_object* v_snd_3806_; lean_object* v___x_3807_; 
v_snd_3806_ = lean_ctor_get(v_a_3797_, 1);
lean_inc(v_snd_3806_);
lean_dec(v_a_3797_);
v___x_3807_ = lean_apply_3(v___y_3793_, v_fst_3798_, v_snd_3806_, v___y_3794_);
v_cases_3767_ = v___x_3807_;
goto _start;
}
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec_ref(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec_ref(v_result_3768_);
v_a_3809_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3796_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3796_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
v___jp_3823_:
{
if (v___y_3824_ == 0)
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___f_3829_; uint8_t v___x_3830_; 
v___x_3825_ = l_Lean_instInhabitedExpr;
v___x_3826_ = lean_nat_sub(v___x_3822_, v___x_3779_);
v___x_3827_ = lean_array_get(v___x_3825_, v_todo_3782_, v___x_3826_);
lean_dec(v___x_3826_);
v___x_3828_ = lean_array_pop(v_todo_3782_);
lean_inc(v_score_3783_);
lean_inc_ref(v___x_3828_);
v___f_3829_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3829_, 0, v_snd_3820_);
lean_closure_set(v___f_3829_, 1, v___x_3828_);
lean_closure_set(v___f_3829_, 2, v_score_3783_);
lean_closure_set(v___f_3829_, 3, v___x_3779_);
v___x_3830_ = lean_nat_dec_eq(v_fst_3819_, v___x_3776_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3832_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 2, v_fst_3819_);
lean_ctor_set(v___x_3786_, 0, v___x_3828_);
v___x_3832_ = v___x_3786_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3828_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v_score_3783_);
lean_ctor_set(v_reuseFailAlloc_3834_, 2, v_fst_3819_);
v___x_3832_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_array_push(v_cases_3821_, v___x_3832_);
v___y_3791_ = v___y_3824_;
v___y_3792_ = v___x_3827_;
v___y_3793_ = v___f_3829_;
v___y_3794_ = v___x_3833_;
goto v___jp_3790_;
}
}
else
{
lean_dec_ref(v___x_3828_);
lean_dec(v_fst_3819_);
lean_del_object(v___x_3786_);
lean_dec(v_score_3783_);
v___y_3791_ = v___y_3824_;
v___y_3792_ = v___x_3827_;
v___y_3793_ = v___f_3829_;
v___y_3794_ = v_cases_3821_;
goto v___jp_3790_;
}
}
else
{
lean_dec(v_snd_3820_);
lean_dec(v_fst_3819_);
lean_del_object(v___x_3786_);
lean_dec(v_score_3783_);
lean_dec_ref(v_todo_3782_);
v_cases_3767_ = v_cases_3821_;
goto _start;
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_del_object(v___x_3786_);
lean_dec(v_score_3783_);
lean_dec_ref(v_todo_3782_);
lean_dec_ref(v_result_3768_);
lean_dec_ref(v_cases_3767_);
v_a_3842_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3788_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3788_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
else
{
lean_object* v___x_3851_; 
lean_dec_ref(v_cases_3767_);
v___x_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3851_, 0, v_result_3768_);
return v___x_3851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3852_, lean_object* v_result_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3852_, v_result_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
lean_dec(v_a_3854_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3861_, lean_object* v_cases_3862_, lean_object* v_result_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3862_, v_result_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3871_, lean_object* v_cases_3872_, lean_object* v_result_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3871_, v_cases_3872_, v_result_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_);
lean_dec(v_a_3878_);
lean_dec_ref(v_a_3877_);
lean_dec(v_a_3876_);
lean_dec_ref(v_a_3875_);
lean_dec(v_a_3874_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_box(3);
v___x_3891_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3883_, v___x_3890_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
return v___x_3893_;
}
else
{
lean_object* v_val_3894_; lean_object* v___x_3895_; 
v_val_3894_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_val_3894_);
lean_dec_ref(v___x_3891_);
v___x_3895_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3894_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
lean_dec(v_val_3894_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3907_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_3907_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3907_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v_fst_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
v_fst_3900_ = lean_ctor_get(v_a_3896_, 0);
lean_inc(v_fst_3900_);
lean_dec(v_a_3896_);
v___x_3901_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3902_ = lean_unsigned_to_nat(1u);
v___x_3903_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3901_, v___x_3902_, v_fst_3900_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3903_);
v___x_3905_ = v___x_3898_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
v_a_3908_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3895_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3895_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec_ref(v_root_3916_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3924_, lean_object* v_root_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3933_, lean_object* v_root_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3933_, v_root_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_a_3935_);
lean_dec_ref(v_root_3934_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3942_, lean_object* v_k_3943_, lean_object* v_args_3944_, lean_object* v_cases_3945_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3942_, v_k_3943_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_dec_ref(v_args_3944_);
return v_cases_3945_;
}
else
{
lean_object* v_val_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v_val_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_val_3947_);
lean_dec_ref(v___x_3946_);
v___x_3948_ = lean_unsigned_to_nat(1u);
v___x_3949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3949_, 0, v_args_3944_);
lean_ctor_set(v___x_3949_, 1, v___x_3948_);
lean_ctor_set(v___x_3949_, 2, v_val_3947_);
v___x_3950_ = lean_array_push(v_cases_3945_, v___x_3949_);
return v___x_3950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3951_, lean_object* v_k_3952_, lean_object* v_args_3953_, lean_object* v_cases_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3951_, v_k_3952_, v_args_3953_, v_cases_3954_);
lean_dec(v_k_3952_);
lean_dec_ref(v_r_3951_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3958_, lean_object* v_e_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3958_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; uint8_t v___x_3968_; lean_object* v___x_3969_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref(v___x_3966_);
v___x_3968_ = 1;
v___x_3969_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3959_, v___x_3968_, v___x_3968_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v_fst_3971_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref(v___x_3969_);
v_fst_3971_ = lean_ctor_get(v_a_3970_, 0);
lean_inc(v_fst_3971_);
switch(lean_obj_tag(v_fst_3971_))
{
case 3:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
lean_dec(v_a_3970_);
v___x_3972_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3973_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3972_, v_a_3967_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
return v___x_3973_;
}
case 5:
{
lean_object* v_snd_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_snd_3974_ = lean_ctor_get(v_a_3970_, 1);
lean_inc(v_snd_3974_);
lean_dec(v_a_3970_);
v___x_3975_ = lean_box(4);
v___x_3976_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_3977_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3958_, v___x_3975_, v___x_3976_, v___x_3976_);
v___x_3978_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3958_, v_fst_3971_, v_snd_3974_, v___x_3977_);
v___x_3979_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3978_, v_a_3967_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
return v___x_3979_;
}
default: 
{
lean_object* v_snd_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_snd_3980_ = lean_ctor_get(v_a_3970_, 1);
lean_inc(v_snd_3980_);
lean_dec(v_a_3970_);
v___x_3981_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3982_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3958_, v_fst_3971_, v_snd_3980_, v___x_3981_);
lean_dec(v_fst_3971_);
v___x_3983_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3982_, v_a_3967_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
return v___x_3983_;
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v_a_3967_);
v_a_3984_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3969_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3969_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
else
{
lean_dec_ref(v_e_3959_);
return v___x_3966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_3992_, lean_object* v_e_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3992_, v_e_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
lean_dec(v_a_3994_);
lean_dec_ref(v_root_3992_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_4001_, lean_object* v_root_4002_, lean_object* v_e_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_4002_, v_e_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4011_, lean_object* v_root_4012_, lean_object* v_e_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4011_, v_root_4012_, v_e_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec_ref(v_root_4012_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4021_, lean_object* v_e_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_roots_4028_; lean_object* v___x_4029_; uint8_t v_foApprox_4030_; uint8_t v_ctxApprox_4031_; uint8_t v_quasiPatternApprox_4032_; uint8_t v_constApprox_4033_; uint8_t v_isDefEqStuckEx_4034_; uint8_t v_unificationHints_4035_; uint8_t v_proofIrrelevance_4036_; uint8_t v_assignSyntheticOpaque_4037_; uint8_t v_offsetCnstrs_4038_; uint8_t v_etaStruct_4039_; uint8_t v_univApprox_4040_; uint8_t v_iota_4041_; uint8_t v_beta_4042_; uint8_t v_proj_4043_; uint8_t v_zeta_4044_; uint8_t v_zetaDelta_4045_; uint8_t v_zetaUnused_4046_; uint8_t v_zetaHave_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4075_; 
v_roots_4028_ = lean_ctor_get(v_d_4021_, 1);
v___x_4029_ = l_Lean_Meta_Context_config(v_a_4023_);
v_foApprox_4030_ = lean_ctor_get_uint8(v___x_4029_, 0);
v_ctxApprox_4031_ = lean_ctor_get_uint8(v___x_4029_, 1);
v_quasiPatternApprox_4032_ = lean_ctor_get_uint8(v___x_4029_, 2);
v_constApprox_4033_ = lean_ctor_get_uint8(v___x_4029_, 3);
v_isDefEqStuckEx_4034_ = lean_ctor_get_uint8(v___x_4029_, 4);
v_unificationHints_4035_ = lean_ctor_get_uint8(v___x_4029_, 5);
v_proofIrrelevance_4036_ = lean_ctor_get_uint8(v___x_4029_, 6);
v_assignSyntheticOpaque_4037_ = lean_ctor_get_uint8(v___x_4029_, 7);
v_offsetCnstrs_4038_ = lean_ctor_get_uint8(v___x_4029_, 8);
v_etaStruct_4039_ = lean_ctor_get_uint8(v___x_4029_, 10);
v_univApprox_4040_ = lean_ctor_get_uint8(v___x_4029_, 11);
v_iota_4041_ = lean_ctor_get_uint8(v___x_4029_, 12);
v_beta_4042_ = lean_ctor_get_uint8(v___x_4029_, 13);
v_proj_4043_ = lean_ctor_get_uint8(v___x_4029_, 14);
v_zeta_4044_ = lean_ctor_get_uint8(v___x_4029_, 15);
v_zetaDelta_4045_ = lean_ctor_get_uint8(v___x_4029_, 16);
v_zetaUnused_4046_ = lean_ctor_get_uint8(v___x_4029_, 17);
v_zetaHave_4047_ = lean_ctor_get_uint8(v___x_4029_, 18);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4049_ = v___x_4029_;
v_isShared_4050_ = v_isSharedCheck_4075_;
goto v_resetjp_4048_;
}
else
{
lean_dec(v___x_4029_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4075_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
uint8_t v_trackZetaDelta_4051_; lean_object* v_zetaDeltaSet_4052_; lean_object* v_lctx_4053_; lean_object* v_localInstances_4054_; lean_object* v_defEqCtx_x3f_4055_; lean_object* v_synthPendingDepth_4056_; lean_object* v_canUnfold_x3f_4057_; uint8_t v_univApprox_4058_; uint8_t v_inTypeClassResolution_4059_; uint8_t v_cacheInferType_4060_; uint8_t v___x_4061_; lean_object* v_config_4063_; 
v_trackZetaDelta_4051_ = lean_ctor_get_uint8(v_a_4023_, sizeof(void*)*7);
v_zetaDeltaSet_4052_ = lean_ctor_get(v_a_4023_, 1);
v_lctx_4053_ = lean_ctor_get(v_a_4023_, 2);
v_localInstances_4054_ = lean_ctor_get(v_a_4023_, 3);
v_defEqCtx_x3f_4055_ = lean_ctor_get(v_a_4023_, 4);
v_synthPendingDepth_4056_ = lean_ctor_get(v_a_4023_, 5);
v_canUnfold_x3f_4057_ = lean_ctor_get(v_a_4023_, 6);
v_univApprox_4058_ = lean_ctor_get_uint8(v_a_4023_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4059_ = lean_ctor_get_uint8(v_a_4023_, sizeof(void*)*7 + 2);
v_cacheInferType_4060_ = lean_ctor_get_uint8(v_a_4023_, sizeof(void*)*7 + 3);
v___x_4061_ = 2;
if (v_isShared_4050_ == 0)
{
v_config_4063_ = v___x_4049_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 0, v_foApprox_4030_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 1, v_ctxApprox_4031_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 2, v_quasiPatternApprox_4032_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 3, v_constApprox_4033_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 4, v_isDefEqStuckEx_4034_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 5, v_unificationHints_4035_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 6, v_proofIrrelevance_4036_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 7, v_assignSyntheticOpaque_4037_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 8, v_offsetCnstrs_4038_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 10, v_etaStruct_4039_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 11, v_univApprox_4040_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 12, v_iota_4041_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 13, v_beta_4042_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 14, v_proj_4043_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 15, v_zeta_4044_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 16, v_zetaDelta_4045_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 17, v_zetaUnused_4046_);
lean_ctor_set_uint8(v_reuseFailAlloc_4074_, 18, v_zetaHave_4047_);
v_config_4063_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
uint64_t v___x_4064_; uint64_t v___x_4065_; uint64_t v___x_4066_; lean_object* v___x_4067_; uint64_t v___x_4068_; uint64_t v___x_4069_; uint64_t v_key_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_ctor_set_uint8(v_config_4063_, 9, v___x_4061_);
v___x_4064_ = l_Lean_Meta_Context_configKey(v_a_4023_);
v___x_4065_ = 2ULL;
v___x_4066_ = lean_uint64_shift_right(v___x_4064_, v___x_4065_);
lean_inc_ref(v_roots_4028_);
v___x_4067_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4067_, 0, lean_box(0));
lean_closure_set(v___x_4067_, 1, v_roots_4028_);
lean_closure_set(v___x_4067_, 2, v_e_4022_);
v___x_4068_ = lean_uint64_shift_left(v___x_4066_, v___x_4065_);
v___x_4069_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0);
v_key_4070_ = lean_uint64_lor(v___x_4068_, v___x_4069_);
v___x_4071_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4071_, 0, v_config_4063_);
lean_ctor_set_uint64(v___x_4071_, sizeof(void*)*1, v_key_4070_);
lean_inc(v_canUnfold_x3f_4057_);
lean_inc(v_synthPendingDepth_4056_);
lean_inc(v_defEqCtx_x3f_4055_);
lean_inc_ref(v_localInstances_4054_);
lean_inc_ref(v_lctx_4053_);
lean_inc(v_zetaDeltaSet_4052_);
v___x_4072_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
lean_ctor_set(v___x_4072_, 1, v_zetaDeltaSet_4052_);
lean_ctor_set(v___x_4072_, 2, v_lctx_4053_);
lean_ctor_set(v___x_4072_, 3, v_localInstances_4054_);
lean_ctor_set(v___x_4072_, 4, v_defEqCtx_x3f_4055_);
lean_ctor_set(v___x_4072_, 5, v_synthPendingDepth_4056_);
lean_ctor_set(v___x_4072_, 6, v_canUnfold_x3f_4057_);
lean_ctor_set_uint8(v___x_4072_, sizeof(void*)*7, v_trackZetaDelta_4051_);
lean_ctor_set_uint8(v___x_4072_, sizeof(void*)*7 + 1, v_univApprox_4058_);
lean_ctor_set_uint8(v___x_4072_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4059_);
lean_ctor_set_uint8(v___x_4072_, sizeof(void*)*7 + 3, v_cacheInferType_4060_);
v___x_4073_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4021_, v___x_4067_, v___x_4072_, v_a_4024_, v_a_4025_, v_a_4026_);
lean_dec_ref(v___x_4072_);
return v___x_4073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4076_, lean_object* v_e_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4076_, v_e_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_);
lean_dec(v_a_4081_);
lean_dec_ref(v_a_4080_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4084_, lean_object* v_d_4085_, lean_object* v_e_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v___x_4092_; 
v___x_4092_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4085_, v_e_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4093_, lean_object* v_d_4094_, lean_object* v_e_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4093_, v_d_4094_, v_e_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
lean_dec(v_a_4097_);
lean_dec_ref(v_a_4096_);
return v_res_4101_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4105_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
lean_ctor_set(v___x_4106_, 1, v___x_4104_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_a_4107_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4108_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4110_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4112_, lean_object* v_k_4113_, lean_object* v_f_4114_){
_start:
{
lean_object* v_roots_4115_; lean_object* v_tries_4116_; lean_object* v___x_4117_; 
v_roots_4115_ = lean_ctor_get(v_d_4112_, 0);
v_tries_4116_ = lean_ctor_get(v_d_4112_, 1);
v___x_4117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4115_, v_k_4113_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4129_; 
lean_inc_ref(v_tries_4116_);
lean_inc_ref(v_roots_4115_);
v_isSharedCheck_4129_ = !lean_is_exclusive(v_d_4112_);
if (v_isSharedCheck_4129_ == 0)
{
lean_object* v_unused_4130_; lean_object* v_unused_4131_; 
v_unused_4130_ = lean_ctor_get(v_d_4112_, 1);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_d_4112_, 0);
lean_dec(v_unused_4131_);
v___x_4119_ = v_d_4112_;
v_isShared_4120_ = v_isSharedCheck_4129_;
goto v_resetjp_4118_;
}
else
{
lean_dec(v_d_4112_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4129_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4121_; lean_object* v_roots_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4127_; 
v___x_4121_ = lean_array_get_size(v_tries_4116_);
v_roots_4122_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4115_, v_k_4113_, v___x_4121_);
v___x_4123_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_evalNode___redArg___closed__0));
v___x_4124_ = lean_apply_1(v_f_4114_, v___x_4123_);
v___x_4125_ = lean_array_push(v_tries_4116_, v___x_4124_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 1, v___x_4125_);
lean_ctor_set(v___x_4119_, 0, v_roots_4122_);
v___x_4127_ = v___x_4119_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_roots_4122_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v___x_4125_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
else
{
lean_object* v_val_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
lean_dec(v_k_4113_);
v_val_4132_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_val_4132_);
lean_dec_ref(v___x_4117_);
v___x_4133_ = lean_array_get_size(v_tries_4116_);
v___x_4134_ = lean_nat_dec_lt(v_val_4132_, v___x_4133_);
if (v___x_4134_ == 0)
{
lean_dec(v_val_4132_);
lean_dec_ref(v_f_4114_);
return v_d_4112_;
}
else
{
lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4146_; 
lean_inc_ref(v_tries_4116_);
lean_inc_ref(v_roots_4115_);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_d_4112_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; lean_object* v_unused_4148_; 
v_unused_4147_ = lean_ctor_get(v_d_4112_, 1);
lean_dec(v_unused_4147_);
v_unused_4148_ = lean_ctor_get(v_d_4112_, 0);
lean_dec(v_unused_4148_);
v___x_4136_ = v_d_4112_;
v_isShared_4137_ = v_isSharedCheck_4146_;
goto v_resetjp_4135_;
}
else
{
lean_dec(v_d_4112_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4146_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v_v_4138_; lean_object* v___x_4139_; lean_object* v_xs_x27_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4144_; 
v_v_4138_ = lean_array_fget(v_tries_4116_, v_val_4132_);
v___x_4139_ = lean_box(0);
v_xs_x27_4140_ = lean_array_fset(v_tries_4116_, v_val_4132_, v___x_4139_);
v___x_4141_ = lean_apply_1(v_f_4114_, v_v_4138_);
v___x_4142_ = lean_array_fset(v_xs_x27_4140_, v_val_4132_, v___x_4141_);
lean_dec(v_val_4132_);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 1, v___x_4142_);
v___x_4144_ = v___x_4136_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_roots_4115_);
lean_ctor_set(v_reuseFailAlloc_4145_, 1, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4149_, lean_object* v_d_4150_, lean_object* v_k_4151_, lean_object* v_f_4152_){
_start:
{
lean_object* v___x_4153_; 
v___x_4153_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4150_, v_k_4151_, v_f_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4154_, lean_object* v_x_4155_){
_start:
{
lean_object* v___x_4156_; 
v___x_4156_ = lean_array_push(v_x_4155_, v_e_4154_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4157_, lean_object* v_k_4158_, lean_object* v_e_4159_){
_start:
{
lean_object* v___f_4160_; lean_object* v___x_4161_; 
v___f_4160_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4160_, 0, v_e_4159_);
v___x_4161_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4157_, v_k_4158_, v___f_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4162_, lean_object* v_d_4163_, lean_object* v_k_4164_, lean_object* v_e_4165_){
_start:
{
lean_object* v___x_4166_; 
v___x_4166_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4163_, v_k_4164_, v_e_4165_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4167_, size_t v_i_4168_, lean_object* v_bs_4169_){
_start:
{
uint8_t v___x_4170_; 
v___x_4170_ = lean_usize_dec_lt(v_i_4168_, v_sz_4167_);
if (v___x_4170_ == 0)
{
return v_bs_4169_;
}
else
{
lean_object* v_v_4171_; lean_object* v___x_4172_; lean_object* v_bs_x27_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; size_t v___x_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v_v_4171_ = lean_array_uget(v_bs_4169_, v_i_4168_);
v___x_4172_ = lean_unsigned_to_nat(0u);
v_bs_x27_4173_ = lean_array_uset(v_bs_4169_, v_i_4168_, v___x_4172_);
v___x_4174_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4175_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4174_);
lean_ctor_set(v___x_4176_, 1, v___x_4172_);
lean_ctor_set(v___x_4176_, 2, v___x_4175_);
lean_ctor_set(v___x_4176_, 3, v_v_4171_);
v___x_4177_ = ((size_t)1ULL);
v___x_4178_ = lean_usize_add(v_i_4168_, v___x_4177_);
v___x_4179_ = lean_array_uset(v_bs_x27_4173_, v_i_4168_, v___x_4176_);
v_i_4168_ = v___x_4178_;
v_bs_4169_ = v___x_4179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4181_, lean_object* v_i_4182_, lean_object* v_bs_4183_){
_start:
{
size_t v_sz_boxed_4184_; size_t v_i_boxed_4185_; lean_object* v_res_4186_; 
v_sz_boxed_4184_ = lean_unbox_usize(v_sz_4181_);
lean_dec(v_sz_4181_);
v_i_boxed_4185_ = lean_unbox_usize(v_i_4182_);
lean_dec(v_i_4182_);
v_res_4186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4184_, v_i_boxed_4185_, v_bs_4183_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4187_, lean_object* v_x_4188_){
_start:
{
if (lean_obj_tag(v_x_4188_) == 0)
{
return v_x_4187_;
}
else
{
lean_object* v_key_4189_; lean_object* v_value_4190_; lean_object* v_tail_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v_key_4189_ = lean_ctor_get(v_x_4188_, 0);
lean_inc(v_key_4189_);
v_value_4190_ = lean_ctor_get(v_x_4188_, 1);
lean_inc(v_value_4190_);
v_tail_4191_ = lean_ctor_get(v_x_4188_, 2);
lean_inc(v_tail_4191_);
lean_dec_ref(v_x_4188_);
v___x_4192_ = lean_unsigned_to_nat(1u);
v___x_4193_ = lean_nat_add(v_value_4190_, v___x_4192_);
lean_dec(v_value_4190_);
v___x_4194_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4187_, v_key_4189_, v___x_4193_);
v_x_4187_ = v___x_4194_;
v_x_4188_ = v_tail_4191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4196_, size_t v_i_4197_, size_t v_stop_4198_, lean_object* v_b_4199_){
_start:
{
uint8_t v___x_4200_; 
v___x_4200_ = lean_usize_dec_eq(v_i_4197_, v_stop_4198_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4201_; lean_object* v___x_4202_; size_t v___x_4203_; size_t v___x_4204_; 
v___x_4201_ = lean_array_uget_borrowed(v_as_4196_, v_i_4197_);
lean_inc(v___x_4201_);
v___x_4202_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4199_, v___x_4201_);
v___x_4203_ = ((size_t)1ULL);
v___x_4204_ = lean_usize_add(v_i_4197_, v___x_4203_);
v_i_4197_ = v___x_4204_;
v_b_4199_ = v___x_4202_;
goto _start;
}
else
{
return v_b_4199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4206_, lean_object* v_i_4207_, lean_object* v_stop_4208_, lean_object* v_b_4209_){
_start:
{
size_t v_i_boxed_4210_; size_t v_stop_boxed_4211_; lean_object* v_res_4212_; 
v_i_boxed_4210_ = lean_unbox_usize(v_i_4207_);
lean_dec(v_i_4207_);
v_stop_boxed_4211_ = lean_unbox_usize(v_stop_4208_);
lean_dec(v_stop_4208_);
v_res_4212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4206_, v_i_boxed_4210_, v_stop_boxed_4211_, v_b_4209_);
lean_dec_ref(v_as_4206_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4213_){
_start:
{
lean_object* v_roots_4214_; lean_object* v_tries_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4242_; 
v_roots_4214_ = lean_ctor_get(v_d_4213_, 0);
v_tries_4215_ = lean_ctor_get(v_d_4213_, 1);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_d_4213_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4217_ = v_d_4213_;
v_isShared_4218_ = v_isSharedCheck_4242_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_tries_4215_);
lean_inc(v_roots_4214_);
lean_dec(v_d_4213_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4242_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___y_4220_; lean_object* v_buckets_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; 
v_buckets_4231_ = lean_ctor_get(v_roots_4214_, 1);
v___x_4232_ = lean_unsigned_to_nat(0u);
v___x_4233_ = lean_array_get_size(v_buckets_4231_);
v___x_4234_ = lean_nat_dec_lt(v___x_4232_, v___x_4233_);
if (v___x_4234_ == 0)
{
v___y_4220_ = v_roots_4214_;
goto v___jp_4219_;
}
else
{
uint8_t v___x_4235_; 
v___x_4235_ = lean_nat_dec_le(v___x_4233_, v___x_4233_);
if (v___x_4235_ == 0)
{
if (v___x_4234_ == 0)
{
v___y_4220_ = v_roots_4214_;
goto v___jp_4219_;
}
else
{
size_t v___x_4236_; size_t v___x_4237_; lean_object* v___x_4238_; 
lean_inc_ref(v_buckets_4231_);
v___x_4236_ = ((size_t)0ULL);
v___x_4237_ = lean_usize_of_nat(v___x_4233_);
v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4231_, v___x_4236_, v___x_4237_, v_roots_4214_);
lean_dec_ref(v_buckets_4231_);
v___y_4220_ = v___x_4238_;
goto v___jp_4219_;
}
}
else
{
size_t v___x_4239_; size_t v___x_4240_; lean_object* v___x_4241_; 
lean_inc_ref(v_buckets_4231_);
v___x_4239_ = ((size_t)0ULL);
v___x_4240_ = lean_usize_of_nat(v___x_4233_);
v___x_4241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4231_, v___x_4239_, v___x_4240_, v_roots_4214_);
lean_dec_ref(v_buckets_4231_);
v___y_4220_ = v___x_4241_;
goto v___jp_4219_;
}
}
v___jp_4219_:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; size_t v_sz_4224_; size_t v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4221_ = lean_unsigned_to_nat(1u);
v___x_4222_ = lean_mk_empty_array_with_capacity(v___x_4221_);
lean_dec_ref(v___x_4222_);
v___x_4223_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4224_ = lean_array_size(v_tries_4215_);
v___x_4225_ = ((size_t)0ULL);
v___x_4226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4224_, v___x_4225_, v_tries_4215_);
v___x_4227_ = l_Array_append___redArg(v___x_4223_, v___x_4226_);
lean_dec_ref(v___x_4226_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 1, v___y_4220_);
lean_ctor_set(v___x_4217_, 0, v___x_4227_);
v___x_4229_ = v___x_4217_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___y_4220_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
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
v___x_4264_ = l_Array_instInhabited(lean_box(0));
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
lean_dec_ref(v_x_4268_);
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
lean_object* v_fst_4308_; lean_object* v_buckets_4309_; lean_object* v_tries_4310_; lean_object* v_snd_4311_; lean_object* v_roots_4322_; lean_object* v_roots_4323_; lean_object* v_tries_4324_; lean_object* v_size_4325_; lean_object* v_buckets_4326_; lean_object* v_tries_4327_; lean_object* v_size_4328_; lean_object* v_buckets_4329_; uint8_t v___x_4330_; 
v_roots_4322_ = lean_ctor_get(v_y_4306_, 0);
v_roots_4323_ = lean_ctor_get(v_x_4305_, 0);
v_tries_4324_ = lean_ctor_get(v_y_4306_, 1);
v_size_4325_ = lean_ctor_get(v_roots_4322_, 0);
v_buckets_4326_ = lean_ctor_get(v_roots_4322_, 1);
v_tries_4327_ = lean_ctor_get(v_x_4305_, 1);
v_size_4328_ = lean_ctor_get(v_roots_4323_, 0);
v_buckets_4329_ = lean_ctor_get(v_roots_4323_, 1);
v___x_4330_ = lean_nat_dec_le(v_size_4325_, v_size_4328_);
if (v___x_4330_ == 0)
{
lean_object* v___f_4331_; 
lean_inc_ref(v_buckets_4329_);
lean_inc_ref(v_tries_4327_);
lean_dec_ref(v_x_4305_);
v___f_4331_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4308_ = v_y_4306_;
v_buckets_4309_ = v_buckets_4329_;
v_tries_4310_ = v_tries_4327_;
v_snd_4311_ = v___f_4331_;
goto v___jp_4307_;
}
else
{
lean_object* v___f_4332_; 
lean_inc_ref(v_buckets_4326_);
lean_inc_ref(v_tries_4324_);
lean_dec_ref(v_y_4306_);
v___f_4332_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4308_ = v_x_4305_;
v_buckets_4309_ = v_buckets_4326_;
v_tries_4310_ = v_tries_4324_;
v_snd_4311_ = v___f_4332_;
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
lean_dec_ref(v_snd_4311_);
lean_dec_ref(v_tries_4310_);
lean_dec_ref(v_buckets_4309_);
return v_fst_4308_;
}
else
{
uint8_t v___x_4315_; 
v___x_4315_ = lean_nat_dec_le(v___x_4313_, v___x_4313_);
if (v___x_4315_ == 0)
{
if (v___x_4314_ == 0)
{
lean_dec_ref(v_snd_4311_);
lean_dec_ref(v_tries_4310_);
lean_dec_ref(v_buckets_4309_);
return v_fst_4308_;
}
else
{
size_t v___x_4316_; size_t v___x_4317_; lean_object* v___x_4318_; 
v___x_4316_ = ((size_t)0ULL);
v___x_4317_ = lean_usize_of_nat(v___x_4313_);
v___x_4318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4310_, v_snd_4311_, v_buckets_4309_, v___x_4316_, v___x_4317_, v_fst_4308_);
lean_dec_ref(v_buckets_4309_);
lean_dec_ref(v_tries_4310_);
return v___x_4318_;
}
}
else
{
size_t v___x_4319_; size_t v___x_4320_; lean_object* v___x_4321_; 
v___x_4319_ = ((size_t)0ULL);
v___x_4320_ = lean_usize_of_nat(v___x_4313_);
v___x_4321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4310_, v_snd_4311_, v_buckets_4309_, v___x_4319_, v___x_4320_, v_fst_4308_);
lean_dec_ref(v_buckets_4309_);
lean_dec_ref(v_tries_4310_);
return v___x_4321_;
}
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
v___x_4377_ = l_Lean_Meta_getLocalInstances___redArg(v_a_4372_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref(v___x_4377_);
v___x_4379_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4370_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4400_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4382_ = v___x_4379_;
v_isShared_4383_ = v_isSharedCheck_4400_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4379_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4400_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v_fst_4384_; lean_object* v_snd_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4399_; 
v_fst_4384_ = lean_ctor_get(v_a_4380_, 0);
v_snd_4385_ = lean_ctor_get(v_a_4380_, 1);
v_isSharedCheck_4399_ = !lean_is_exclusive(v_a_4380_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4387_ = v_a_4380_;
v_isShared_4388_ = v_isSharedCheck_4399_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_snd_4385_);
lean_inc(v_fst_4384_);
lean_dec(v_a_4380_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4399_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v_lctx_4389_; lean_object* v___x_4391_; 
v_lctx_4389_ = lean_ctor_get(v_a_4372_, 2);
lean_inc_ref(v_lctx_4389_);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 1, v_a_4378_);
lean_ctor_set(v___x_4387_, 0, v_lctx_4389_);
v___x_4391_ = v___x_4387_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_lctx_4389_);
lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_a_4378_);
v___x_4391_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4396_; 
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4391_);
lean_ctor_set(v___x_4392_, 1, v_value_4371_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v_snd_4385_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4394_, 0, v_fst_4384_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4394_);
v___x_4396_ = v___x_4382_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4394_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_a_4378_);
lean_dec(v_value_4371_);
v_a_4401_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4379_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4379_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec(v_value_4371_);
lean_dec_ref(v_expr_4370_);
v_a_4409_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4377_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4377_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4417_, lean_object* v_value_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4417_, v_value_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_);
lean_dec(v_a_4422_);
lean_dec_ref(v_a_4421_);
lean_dec(v_a_4420_);
lean_dec_ref(v_a_4419_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4425_, lean_object* v_expr_4426_, lean_object* v_value_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4426_, v_value_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4434_, lean_object* v_expr_4435_, lean_object* v_value_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4434_, v_expr_4435_, v_value_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_);
lean_dec(v_a_4440_);
lean_dec_ref(v_a_4439_);
lean_dec(v_a_4438_);
lean_dec_ref(v_a_4437_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4443_, lean_object* v_idx_4444_, lean_object* v_value_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_){
_start:
{
lean_object* v_entry_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4497_; 
v_entry_4451_ = lean_ctor_get(v_e_4443_, 1);
v_isSharedCheck_4497_ = !lean_is_exclusive(v_e_4443_);
if (v_isSharedCheck_4497_ == 0)
{
lean_object* v_unused_4498_; 
v_unused_4498_ = lean_ctor_get(v_e_4443_, 0);
lean_dec(v_unused_4498_);
v___x_4453_ = v_e_4443_;
v_isShared_4454_ = v_isSharedCheck_4497_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_entry_4451_);
lean_dec(v_e_4443_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4497_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v_snd_4455_; lean_object* v_fst_4456_; lean_object* v_fst_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4495_; 
v_snd_4455_ = lean_ctor_get(v_entry_4451_, 1);
lean_inc(v_snd_4455_);
v_fst_4456_ = lean_ctor_get(v_entry_4451_, 0);
lean_inc(v_fst_4456_);
lean_dec_ref(v_entry_4451_);
v_fst_4457_ = lean_ctor_get(v_snd_4455_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_snd_4455_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; 
v_unused_4496_ = lean_ctor_get(v_snd_4455_, 1);
lean_dec(v_unused_4496_);
v___x_4459_ = v_snd_4455_;
v_isShared_4460_ = v_isSharedCheck_4495_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_fst_4457_);
lean_dec(v_snd_4455_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4495_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4461_ = l_Lean_instInhabitedExpr;
v___x_4462_ = lean_array_get(v___x_4461_, v_fst_4456_, v_idx_4444_);
lean_dec(v_fst_4456_);
v___x_4463_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4462_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4486_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4466_ = v___x_4463_;
v_isShared_4467_ = v_isSharedCheck_4486_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4463_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4486_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v_fst_4468_; lean_object* v_snd_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4485_; 
v_fst_4468_ = lean_ctor_get(v_a_4464_, 0);
v_snd_4469_ = lean_ctor_get(v_a_4464_, 1);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_a_4464_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4471_ = v_a_4464_;
v_isShared_4472_ = v_isSharedCheck_4485_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_snd_4469_);
lean_inc(v_fst_4468_);
lean_dec(v_a_4464_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4485_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 1, v_value_4445_);
lean_ctor_set(v___x_4471_, 0, v_fst_4457_);
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_fst_4457_);
lean_ctor_set(v_reuseFailAlloc_4484_, 1, v_value_4445_);
v___x_4474_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4476_; 
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 1, v___x_4474_);
lean_ctor_set(v___x_4459_, 0, v_snd_4469_);
v___x_4476_ = v___x_4459_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_snd_4469_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v___x_4474_);
v___x_4476_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4478_; 
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 1, v___x_4476_);
lean_ctor_set(v___x_4453_, 0, v_fst_4468_);
v___x_4478_ = v___x_4453_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_fst_4468_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v___x_4476_);
v___x_4478_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
lean_object* v___x_4480_; 
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 0, v___x_4478_);
v___x_4480_ = v___x_4466_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4478_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
lean_del_object(v___x_4459_);
lean_dec(v_fst_4457_);
lean_del_object(v___x_4453_);
lean_dec(v_value_4445_);
v_a_4487_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4463_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4463_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4499_, lean_object* v_idx_4500_, lean_object* v_value_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4499_, v_idx_4500_, v_value_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec(v_idx_4500_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4508_, lean_object* v_e_4509_, lean_object* v_idx_4510_, lean_object* v_value_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4509_, v_idx_4510_, v_value_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4518_, lean_object* v_e_4519_, lean_object* v_idx_4520_, lean_object* v_value_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4518_, v_e_4519_, v_idx_4520_, v_value_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_idx_4520_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4532_ = lean_st_mk_ref(v___x_4531_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4534_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4535_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
return v___x_4537_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4538_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
return v___x_4539_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4540_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4541_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
lean_ctor_set(v___x_4541_, 1, v___x_4540_);
lean_ctor_set(v___x_4541_, 2, v___x_4540_);
lean_ctor_set(v___x_4541_, 3, v___x_4540_);
lean_ctor_set(v___x_4541_, 4, v___x_4540_);
lean_ctor_set(v___x_4541_, 5, v___x_4540_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4542_){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4543_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4544_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4545_, 0, v_ngen_4542_);
lean_ctor_set(v___x_4545_, 1, v___x_4543_);
lean_ctor_set(v___x_4545_, 2, v___x_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4546_, lean_object* v_declName_4547_){
_start:
{
uint8_t v___x_4548_; 
v___x_4548_ = l_Lean_isPrivateName(v_declName_4547_);
if (v___x_4548_ == 0)
{
return v___x_4548_;
}
else
{
lean_object* v___x_4549_; 
v___x_4549_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4546_, v_declName_4547_);
if (lean_obj_tag(v___x_4549_) == 0)
{
return v___x_4548_;
}
else
{
lean_object* v_val_4550_; lean_object* v___x_4551_; uint8_t v_isModule_4552_; 
v_val_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_val_4550_);
lean_dec_ref(v___x_4549_);
v___x_4551_ = l_Lean_Environment_header(v_env_4546_);
v_isModule_4552_ = lean_ctor_get_uint8(v___x_4551_, sizeof(void*)*7 + 4);
if (v_isModule_4552_ == 0)
{
lean_dec_ref(v___x_4551_);
lean_dec(v_val_4550_);
return v_isModule_4552_;
}
else
{
lean_object* v_modules_4553_; lean_object* v___x_4554_; uint8_t v___x_4555_; 
v_modules_4553_ = lean_ctor_get(v___x_4551_, 3);
lean_inc_ref(v_modules_4553_);
lean_dec_ref(v___x_4551_);
v___x_4554_ = lean_array_get_size(v_modules_4553_);
v___x_4555_ = lean_nat_dec_lt(v_val_4550_, v___x_4554_);
if (v___x_4555_ == 0)
{
lean_dec_ref(v_modules_4553_);
lean_dec(v_val_4550_);
return v___x_4555_;
}
else
{
lean_object* v___x_4556_; lean_object* v_toImport_4557_; uint8_t v_importAll_4558_; 
v___x_4556_ = lean_array_fget(v_modules_4553_, v_val_4550_);
lean_dec(v_val_4550_);
lean_dec_ref(v_modules_4553_);
v_toImport_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc_ref(v_toImport_4557_);
lean_dec(v___x_4556_);
v_importAll_4558_ = lean_ctor_get_uint8(v_toImport_4557_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4557_);
return v_importAll_4558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4559_, lean_object* v_declName_4560_){
_start:
{
uint8_t v_res_4561_; lean_object* v_r_4562_; 
v_res_4561_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4559_, v_declName_4560_);
lean_dec(v_declName_4560_);
lean_dec_ref(v_env_4559_);
v_r_4562_ = lean_box(v_res_4561_);
return v_r_4562_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4568_, lean_object* v_declName_4569_){
_start:
{
uint8_t v___x_4570_; 
lean_inc(v_declName_4569_);
lean_inc_ref(v_env_4568_);
v___x_4570_ = l_Lean_Meta_allowCompletion(v_env_4568_, v_declName_4569_);
if (v___x_4570_ == 0)
{
uint8_t v___x_4571_; 
lean_dec(v_declName_4569_);
lean_dec_ref(v_env_4568_);
v___x_4571_ = 1;
return v___x_4571_;
}
else
{
lean_object* v___x_4572_; uint8_t v___x_4573_; uint8_t v___y_4583_; 
v___x_4572_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4573_ = lean_name_eq(v_declName_4569_, v___x_4572_);
if (v___x_4573_ == 0)
{
uint8_t v___x_4584_; 
lean_inc(v_declName_4569_);
v___x_4584_ = l_Lean_Name_isInternalDetail(v_declName_4569_);
if (v___x_4584_ == 0)
{
lean_dec_ref(v_env_4568_);
v___y_4583_ = v___x_4584_;
goto v___jp_4582_;
}
else
{
uint8_t v___x_4585_; 
v___x_4585_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4568_, v_declName_4569_);
lean_dec_ref(v_env_4568_);
if (v___x_4585_ == 0)
{
v___y_4583_ = v___x_4584_;
goto v___jp_4582_;
}
else
{
goto v___jp_4578_;
}
}
}
else
{
lean_dec(v_declName_4569_);
lean_dec_ref(v_env_4568_);
return v___x_4573_;
}
v___jp_4574_:
{
if (lean_obj_tag(v_declName_4569_) == 1)
{
lean_object* v_str_4575_; lean_object* v___x_4576_; uint8_t v___x_4577_; 
v_str_4575_ = lean_ctor_get(v_declName_4569_, 1);
lean_inc_ref(v_str_4575_);
lean_dec_ref(v_declName_4569_);
v___x_4576_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4577_ = lean_string_dec_eq(v_str_4575_, v___x_4576_);
lean_dec_ref(v_str_4575_);
if (v___x_4577_ == 0)
{
return v___x_4573_;
}
else
{
return v___x_4570_;
}
}
else
{
lean_dec(v_declName_4569_);
return v___x_4573_;
}
}
v___jp_4578_:
{
if (lean_obj_tag(v_declName_4569_) == 1)
{
lean_object* v_str_4579_; lean_object* v___x_4580_; uint8_t v___x_4581_; 
v_str_4579_ = lean_ctor_get(v_declName_4569_, 1);
v___x_4580_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4581_ = lean_string_dec_eq(v_str_4579_, v___x_4580_);
if (v___x_4581_ == 0)
{
goto v___jp_4574_;
}
else
{
lean_dec_ref(v_declName_4569_);
return v___x_4570_;
}
}
else
{
goto v___jp_4574_;
}
}
v___jp_4582_:
{
if (v___y_4583_ == 0)
{
goto v___jp_4578_;
}
else
{
lean_dec(v_declName_4569_);
return v___y_4583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4586_, lean_object* v_declName_4587_){
_start:
{
uint8_t v_res_4588_; lean_object* v_r_4589_; 
v_res_4588_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4586_, v_declName_4587_);
v_r_4589_ = lean_box(v_res_4588_);
return v_r_4589_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4590_, lean_object* v_opt_4591_){
_start:
{
lean_object* v_name_4592_; lean_object* v_defValue_4593_; lean_object* v_map_4594_; lean_object* v___x_4595_; 
v_name_4592_ = lean_ctor_get(v_opt_4591_, 0);
v_defValue_4593_ = lean_ctor_get(v_opt_4591_, 1);
v_map_4594_ = lean_ctor_get(v_opts_4590_, 0);
v___x_4595_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4594_, v_name_4592_);
if (lean_obj_tag(v___x_4595_) == 0)
{
uint8_t v___x_4596_; 
v___x_4596_ = lean_unbox(v_defValue_4593_);
return v___x_4596_;
}
else
{
lean_object* v_val_4597_; 
v_val_4597_ = lean_ctor_get(v___x_4595_, 0);
lean_inc(v_val_4597_);
lean_dec_ref(v___x_4595_);
if (lean_obj_tag(v_val_4597_) == 1)
{
uint8_t v_v_4598_; 
v_v_4598_ = lean_ctor_get_uint8(v_val_4597_, 0);
lean_dec_ref(v_val_4597_);
return v_v_4598_;
}
else
{
uint8_t v___x_4599_; 
lean_dec(v_val_4597_);
v___x_4599_ = lean_unbox(v_defValue_4593_);
return v___x_4599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4600_, lean_object* v_opt_4601_){
_start:
{
uint8_t v_res_4602_; lean_object* v_r_4603_; 
v_res_4602_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4600_, v_opt_4601_);
lean_dec_ref(v_opt_4601_);
lean_dec_ref(v_opts_4600_);
v_r_4603_ = lean_box(v_res_4602_);
return v_r_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4604_, lean_object* v_opt_4605_){
_start:
{
lean_object* v_name_4606_; lean_object* v_defValue_4607_; lean_object* v_map_4608_; lean_object* v___x_4609_; 
v_name_4606_ = lean_ctor_get(v_opt_4605_, 0);
v_defValue_4607_ = lean_ctor_get(v_opt_4605_, 1);
v_map_4608_ = lean_ctor_get(v_opts_4604_, 0);
v___x_4609_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4608_, v_name_4606_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_inc(v_defValue_4607_);
return v_defValue_4607_;
}
else
{
lean_object* v_val_4610_; 
v_val_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_val_4610_);
lean_dec_ref(v___x_4609_);
if (lean_obj_tag(v_val_4610_) == 3)
{
lean_object* v_v_4611_; 
v_v_4611_ = lean_ctor_get(v_val_4610_, 0);
lean_inc(v_v_4611_);
lean_dec_ref(v_val_4610_);
return v_v_4611_;
}
else
{
lean_dec(v_val_4610_);
lean_inc(v_defValue_4607_);
return v_defValue_4607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4612_, lean_object* v_opt_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4612_, v_opt_4613_);
lean_dec_ref(v_opt_4613_);
lean_dec_ref(v_opts_4612_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4615_, size_t v_i_4616_, size_t v_stop_4617_, lean_object* v_b_4618_){
_start:
{
uint8_t v___x_4619_; 
v___x_4619_ = lean_usize_dec_eq(v_i_4616_, v_stop_4617_);
if (v___x_4619_ == 0)
{
lean_object* v___x_4620_; lean_object* v_key_4621_; lean_object* v_entry_4622_; lean_object* v___x_4623_; size_t v___x_4624_; size_t v___x_4625_; 
v___x_4620_ = lean_array_uget_borrowed(v_as_4615_, v_i_4616_);
v_key_4621_ = lean_ctor_get(v___x_4620_, 0);
v_entry_4622_ = lean_ctor_get(v___x_4620_, 1);
lean_inc_ref(v_entry_4622_);
lean_inc(v_key_4621_);
v___x_4623_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4618_, v_key_4621_, v_entry_4622_);
v___x_4624_ = ((size_t)1ULL);
v___x_4625_ = lean_usize_add(v_i_4616_, v___x_4624_);
v_i_4616_ = v___x_4625_;
v_b_4618_ = v___x_4623_;
goto _start;
}
else
{
return v_b_4618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4627_, lean_object* v_i_4628_, lean_object* v_stop_4629_, lean_object* v_b_4630_){
_start:
{
size_t v_i_boxed_4631_; size_t v_stop_boxed_4632_; lean_object* v_res_4633_; 
v_i_boxed_4631_ = lean_unbox_usize(v_i_4628_);
lean_dec(v_i_4628_);
v_stop_boxed_4632_ = lean_unbox_usize(v_stop_4629_);
lean_dec(v_stop_4629_);
v_res_4633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4627_, v_i_boxed_4631_, v_stop_boxed_4632_, v_b_4630_);
lean_dec_ref(v_as_4627_);
return v_res_4633_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4634_; 
v___x_4634_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4634_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
return v___x_4636_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4637_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4638_ = lean_unsigned_to_nat(0u);
v___x_4639_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4638_);
lean_ctor_set(v___x_4639_, 1, v___x_4638_);
lean_ctor_set(v___x_4639_, 2, v___x_4638_);
lean_ctor_set(v___x_4639_, 3, v___x_4637_);
lean_ctor_set(v___x_4639_, 4, v___x_4637_);
lean_ctor_set(v___x_4639_, 5, v___x_4637_);
lean_ctor_set(v___x_4639_, 6, v___x_4637_);
lean_ctor_set(v___x_4639_, 7, v___x_4637_);
lean_ctor_set(v___x_4639_, 8, v___x_4637_);
return v___x_4639_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4640_ = lean_unsigned_to_nat(32u);
v___x_4641_ = lean_mk_empty_array_with_capacity(v___x_4640_);
v___x_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
return v___x_4642_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4643_ = ((size_t)5ULL);
v___x_4644_ = lean_unsigned_to_nat(0u);
v___x_4645_ = lean_unsigned_to_nat(32u);
v___x_4646_ = lean_mk_empty_array_with_capacity(v___x_4645_);
v___x_4647_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4648_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
lean_ctor_set(v___x_4648_, 1, v___x_4646_);
lean_ctor_set(v___x_4648_, 2, v___x_4644_);
lean_ctor_set(v___x_4648_, 3, v___x_4644_);
lean_ctor_set_usize(v___x_4648_, 4, v___x_4643_);
return v___x_4648_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4649_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
lean_ctor_set(v___x_4650_, 1, v___x_4649_);
lean_ctor_set(v___x_4650_, 2, v___x_4649_);
lean_ctor_set(v___x_4650_, 3, v___x_4649_);
lean_ctor_set(v___x_4650_, 4, v___x_4649_);
return v___x_4650_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4651_ = lean_box(1);
v___x_4652_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4653_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4653_);
lean_ctor_set(v___x_4654_, 1, v___x_4652_);
lean_ctor_set(v___x_4654_, 2, v___x_4651_);
return v___x_4654_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4657_ = lean_unsigned_to_nat(1u);
v___x_4658_ = l_Lean_firstFrontendMacroScope;
v___x_4659_ = lean_nat_add(v___x_4658_, v___x_4657_);
return v___x_4659_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4664_; uint64_t v___x_4665_; lean_object* v___x_4666_; 
v___x_4664_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4665_ = 0ULL;
v___x_4666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4666_, 0, v___x_4664_);
lean_ctor_set_uint64(v___x_4666_, sizeof(void*)*1, v___x_4665_);
return v___x_4666_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4667_ = l_Lean_NameSet_empty;
v___x_4668_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4668_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
lean_ctor_set(v___x_4669_, 2, v___x_4667_);
return v___x_4669_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; uint8_t v___x_4672_; lean_object* v___x_4673_; 
v___x_4670_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4671_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4672_ = 1;
v___x_4673_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4673_, 0, v___x_4671_);
lean_ctor_set(v___x_4673_, 1, v___x_4671_);
lean_ctor_set(v___x_4673_, 2, v___x_4670_);
lean_ctor_set_uint8(v___x_4673_, sizeof(void*)*3, v___x_4672_);
return v___x_4673_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4674_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
lean_ctor_set(v___x_4675_, 1, v___x_4674_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4676_, lean_object* v_env_4677_, lean_object* v_modName_4678_, lean_object* v_d_4679_, lean_object* v_cacheRef_4680_, lean_object* v_tree_4681_, lean_object* v_act_4682_, lean_object* v_name_4683_, lean_object* v_constInfo_4684_){
_start:
{
uint8_t v___x_4686_; 
v___x_4686_ = l_Lean_ConstantInfo_isUnsafe(v_constInfo_4684_);
if (v___x_4686_ == 0)
{
uint8_t v___x_4687_; 
lean_inc(v_name_4683_);
lean_inc_ref(v_env_4677_);
v___x_4687_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4677_, v_name_4683_);
if (v___x_4687_ == 0)
{
lean_object* v___x_4688_; lean_object* v_ngen_4689_; lean_object* v_core_4690_; lean_object* v_meta_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4825_; 
v___x_4688_ = lean_st_ref_get(v_cacheRef_4680_);
v_ngen_4689_ = lean_ctor_get(v___x_4688_, 0);
v_core_4690_ = lean_ctor_get(v___x_4688_, 1);
v_meta_4691_ = lean_ctor_get(v___x_4688_, 2);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4693_ = v___x_4688_;
v_isShared_4694_ = v_isSharedCheck_4825_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_meta_4691_);
lean_inc(v_core_4690_);
lean_inc(v_ngen_4689_);
lean_dec(v___x_4688_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4825_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; lean_object* v___x_4703_; uint8_t v___x_4704_; uint8_t v___x_4705_; uint8_t v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v_fileName_4723_; lean_object* v_fileMap_4724_; lean_object* v_options_4725_; lean_object* v_currRecDepth_4726_; lean_object* v_maxRecDepth_4727_; lean_object* v_ref_4728_; lean_object* v_currNamespace_4729_; lean_object* v_openDecls_4730_; lean_object* v_initHeartbeats_4731_; lean_object* v_maxHeartbeats_4732_; lean_object* v_quotContext_4733_; lean_object* v_currMacroScope_4734_; uint8_t v_diag_4735_; lean_object* v_cancelTk_x3f_4736_; uint8_t v_suppressElabErrors_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4823_; 
v___x_4695_ = lean_unsigned_to_nat(0u);
v___x_4696_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4697_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4698_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4689_);
v___x_4699_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4689_);
v___x_4700_ = lean_st_ref_set(v_cacheRef_4680_, v___x_4699_);
v___x_4701_ = lean_box(1);
v___x_4702_ = 1;
v___x_4703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4696_);
lean_ctor_set(v___x_4703_, 1, v_meta_4691_);
lean_ctor_set(v___x_4703_, 2, v___x_4701_);
lean_ctor_set(v___x_4703_, 3, v___x_4697_);
lean_ctor_set(v___x_4703_, 4, v___x_4698_);
v___x_4704_ = 2;
v___x_4705_ = 0;
v___x_4706_ = 2;
v___x_4707_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4707_, 0, v___x_4687_);
lean_ctor_set_uint8(v___x_4707_, 1, v___x_4687_);
lean_ctor_set_uint8(v___x_4707_, 2, v___x_4687_);
lean_ctor_set_uint8(v___x_4707_, 3, v___x_4687_);
lean_ctor_set_uint8(v___x_4707_, 4, v___x_4687_);
lean_ctor_set_uint8(v___x_4707_, 5, v___x_4702_);
lean_ctor_set_uint8(v___x_4707_, 6, v___x_4702_);
lean_ctor_set_uint8(v___x_4707_, 7, v___x_4687_);
lean_ctor_set_uint8(v___x_4707_, 8, v___x_4702_);
lean_ctor_set_uint8(v___x_4707_, 9, v___x_4704_);
lean_ctor_set_uint8(v___x_4707_, 10, v___x_4705_);
lean_ctor_set_uint8(v___x_4707_, 11, v___x_4702_);
lean_ctor_set_uint8(v___x_4707_, 12, v___x_4702_);
lean_ctor_set_uint8(v___x_4707_, 13, v___x_4702_);
lean_ctor_set_uint8(v___x_4707_, 14, v___x_4706_);
lean_ctor_set_uint8(v___x_4707_, 15, v___x_4702_);
lean_ctor_set_uint8(v___x_4707_, 16, v___x_4702_);
lean_ctor_set_uint8(v___x_4707_, 17, v___x_4702_);
lean_ctor_set_uint8(v___x_4707_, 18, v___x_4702_);
v___x_4708_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4707_);
v___x_4709_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4710_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4711_ = lean_box(0);
v___x_4712_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4712_, 0, v___x_4708_);
lean_ctor_set(v___x_4712_, 1, v___x_4701_);
lean_ctor_set(v___x_4712_, 2, v___x_4709_);
lean_ctor_set(v___x_4712_, 3, v___x_4710_);
lean_ctor_set(v___x_4712_, 4, v___x_4711_);
lean_ctor_set(v___x_4712_, 5, v___x_4695_);
lean_ctor_set(v___x_4712_, 6, v___x_4711_);
lean_ctor_set_uint8(v___x_4712_, sizeof(void*)*7, v___x_4687_);
lean_ctor_set_uint8(v___x_4712_, sizeof(void*)*7 + 1, v___x_4687_);
lean_ctor_set_uint8(v___x_4712_, sizeof(void*)*7 + 2, v___x_4687_);
lean_ctor_set_uint8(v___x_4712_, sizeof(void*)*7 + 3, v___x_4702_);
v___x_4713_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4714_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4715_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4716_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4717_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4718_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4718_, 0, v_env_4677_);
lean_ctor_set(v___x_4718_, 1, v___x_4713_);
lean_ctor_set(v___x_4718_, 2, v_ngen_4689_);
lean_ctor_set(v___x_4718_, 3, v___x_4714_);
lean_ctor_set(v___x_4718_, 4, v___x_4715_);
lean_ctor_set(v___x_4718_, 5, v_core_4690_);
lean_ctor_set(v___x_4718_, 6, v___x_4716_);
lean_ctor_set(v___x_4718_, 7, v___x_4717_);
lean_ctor_set(v___x_4718_, 8, v___x_4710_);
v___x_4719_ = lean_st_mk_ref(v___x_4718_);
v___x_4720_ = l_Lean_inheritedTraceOptions;
v___x_4721_ = lean_st_ref_get(v___x_4720_);
v___x_4722_ = lean_st_ref_get(v___x_4719_);
v_fileName_4723_ = lean_ctor_get(v_cctx_4676_, 0);
v_fileMap_4724_ = lean_ctor_get(v_cctx_4676_, 1);
v_options_4725_ = lean_ctor_get(v_cctx_4676_, 2);
v_currRecDepth_4726_ = lean_ctor_get(v_cctx_4676_, 3);
v_maxRecDepth_4727_ = lean_ctor_get(v_cctx_4676_, 4);
v_ref_4728_ = lean_ctor_get(v_cctx_4676_, 5);
v_currNamespace_4729_ = lean_ctor_get(v_cctx_4676_, 6);
v_openDecls_4730_ = lean_ctor_get(v_cctx_4676_, 7);
v_initHeartbeats_4731_ = lean_ctor_get(v_cctx_4676_, 8);
v_maxHeartbeats_4732_ = lean_ctor_get(v_cctx_4676_, 9);
v_quotContext_4733_ = lean_ctor_get(v_cctx_4676_, 10);
v_currMacroScope_4734_ = lean_ctor_get(v_cctx_4676_, 11);
v_diag_4735_ = lean_ctor_get_uint8(v_cctx_4676_, sizeof(void*)*14);
v_cancelTk_x3f_4736_ = lean_ctor_get(v_cctx_4676_, 12);
v_suppressElabErrors_4737_ = lean_ctor_get_uint8(v_cctx_4676_, sizeof(void*)*14 + 1);
v_isSharedCheck_4823_ = !lean_is_exclusive(v_cctx_4676_);
if (v_isSharedCheck_4823_ == 0)
{
lean_object* v_unused_4824_; 
v_unused_4824_ = lean_ctor_get(v_cctx_4676_, 13);
lean_dec(v_unused_4824_);
v___x_4739_ = v_cctx_4676_;
v_isShared_4740_ = v_isSharedCheck_4823_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_cancelTk_x3f_4736_);
lean_inc(v_currMacroScope_4734_);
lean_inc(v_quotContext_4733_);
lean_inc(v_maxHeartbeats_4732_);
lean_inc(v_initHeartbeats_4731_);
lean_inc(v_openDecls_4730_);
lean_inc(v_currNamespace_4729_);
lean_inc(v_ref_4728_);
lean_inc(v_maxRecDepth_4727_);
lean_inc(v_currRecDepth_4726_);
lean_inc(v_options_4725_);
lean_inc(v_fileMap_4724_);
lean_inc(v_fileName_4723_);
lean_dec(v_cctx_4676_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4823_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v_env_4741_; lean_object* v___x_4743_; 
v_env_4741_ = lean_ctor_get(v___x_4722_, 0);
lean_inc_ref(v_env_4741_);
lean_dec(v___x_4722_);
lean_inc_ref(v_options_4725_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 13, v___x_4721_);
v___x_4743_ = v___x_4739_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_fileName_4723_);
lean_ctor_set(v_reuseFailAlloc_4822_, 1, v_fileMap_4724_);
lean_ctor_set(v_reuseFailAlloc_4822_, 2, v_options_4725_);
lean_ctor_set(v_reuseFailAlloc_4822_, 3, v_currRecDepth_4726_);
lean_ctor_set(v_reuseFailAlloc_4822_, 4, v_maxRecDepth_4727_);
lean_ctor_set(v_reuseFailAlloc_4822_, 5, v_ref_4728_);
lean_ctor_set(v_reuseFailAlloc_4822_, 6, v_currNamespace_4729_);
lean_ctor_set(v_reuseFailAlloc_4822_, 7, v_openDecls_4730_);
lean_ctor_set(v_reuseFailAlloc_4822_, 8, v_initHeartbeats_4731_);
lean_ctor_set(v_reuseFailAlloc_4822_, 9, v_maxHeartbeats_4732_);
lean_ctor_set(v_reuseFailAlloc_4822_, 10, v_quotContext_4733_);
lean_ctor_set(v_reuseFailAlloc_4822_, 11, v_currMacroScope_4734_);
lean_ctor_set(v_reuseFailAlloc_4822_, 12, v_cancelTk_x3f_4736_);
lean_ctor_set(v_reuseFailAlloc_4822_, 13, v___x_4721_);
lean_ctor_set_uint8(v_reuseFailAlloc_4822_, sizeof(void*)*14, v_diag_4735_);
lean_ctor_set_uint8(v_reuseFailAlloc_4822_, sizeof(void*)*14 + 1, v_suppressElabErrors_4737_);
v___x_4743_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
lean_object* v___x_4744_; uint8_t v___x_4745_; lean_object* v___y_4747_; lean_object* v___y_4748_; uint8_t v___y_4800_; uint8_t v___x_4821_; 
v___x_4744_ = l_Lean_diagnostics;
v___x_4745_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4725_, v___x_4744_);
v___x_4821_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4741_);
lean_dec_ref(v_env_4741_);
if (v___x_4821_ == 0)
{
if (v___x_4745_ == 0)
{
lean_inc(v___x_4719_);
v___y_4747_ = v___x_4743_;
v___y_4748_ = v___x_4719_;
goto v___jp_4746_;
}
else
{
v___y_4800_ = v___x_4821_;
goto v___jp_4799_;
}
}
else
{
v___y_4800_ = v___x_4745_;
goto v___jp_4799_;
}
v___jp_4746_:
{
lean_object* v___x_4749_; lean_object* v_fileName_4750_; lean_object* v_fileMap_4751_; lean_object* v_currRecDepth_4752_; lean_object* v_ref_4753_; lean_object* v_currNamespace_4754_; lean_object* v_openDecls_4755_; lean_object* v_initHeartbeats_4756_; lean_object* v_maxHeartbeats_4757_; lean_object* v_quotContext_4758_; lean_object* v_currMacroScope_4759_; lean_object* v_cancelTk_x3f_4760_; uint8_t v_suppressElabErrors_4761_; lean_object* v_inheritedTraceOptions_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4796_; 
v___x_4749_ = lean_st_mk_ref(v___x_4703_);
v_fileName_4750_ = lean_ctor_get(v___y_4747_, 0);
v_fileMap_4751_ = lean_ctor_get(v___y_4747_, 1);
v_currRecDepth_4752_ = lean_ctor_get(v___y_4747_, 3);
v_ref_4753_ = lean_ctor_get(v___y_4747_, 5);
v_currNamespace_4754_ = lean_ctor_get(v___y_4747_, 6);
v_openDecls_4755_ = lean_ctor_get(v___y_4747_, 7);
v_initHeartbeats_4756_ = lean_ctor_get(v___y_4747_, 8);
v_maxHeartbeats_4757_ = lean_ctor_get(v___y_4747_, 9);
v_quotContext_4758_ = lean_ctor_get(v___y_4747_, 10);
v_currMacroScope_4759_ = lean_ctor_get(v___y_4747_, 11);
v_cancelTk_x3f_4760_ = lean_ctor_get(v___y_4747_, 12);
v_suppressElabErrors_4761_ = lean_ctor_get_uint8(v___y_4747_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4762_ = lean_ctor_get(v___y_4747_, 13);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___y_4747_);
if (v_isSharedCheck_4796_ == 0)
{
lean_object* v_unused_4797_; lean_object* v_unused_4798_; 
v_unused_4797_ = lean_ctor_get(v___y_4747_, 4);
lean_dec(v_unused_4797_);
v_unused_4798_ = lean_ctor_get(v___y_4747_, 2);
lean_dec(v_unused_4798_);
v___x_4764_ = v___y_4747_;
v_isShared_4765_ = v_isSharedCheck_4796_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_inheritedTraceOptions_4762_);
lean_inc(v_cancelTk_x3f_4760_);
lean_inc(v_currMacroScope_4759_);
lean_inc(v_quotContext_4758_);
lean_inc(v_maxHeartbeats_4757_);
lean_inc(v_initHeartbeats_4756_);
lean_inc(v_openDecls_4755_);
lean_inc(v_currNamespace_4754_);
lean_inc(v_ref_4753_);
lean_inc(v_currRecDepth_4752_);
lean_inc(v_fileMap_4751_);
lean_inc(v_fileName_4750_);
lean_dec(v___y_4747_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4796_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4769_; 
v___x_4766_ = l_Lean_maxRecDepth;
v___x_4767_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4725_, v___x_4766_);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 4, v___x_4767_);
lean_ctor_set(v___x_4764_, 2, v_options_4725_);
v___x_4769_ = v___x_4764_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_fileName_4750_);
lean_ctor_set(v_reuseFailAlloc_4795_, 1, v_fileMap_4751_);
lean_ctor_set(v_reuseFailAlloc_4795_, 2, v_options_4725_);
lean_ctor_set(v_reuseFailAlloc_4795_, 3, v_currRecDepth_4752_);
lean_ctor_set(v_reuseFailAlloc_4795_, 4, v___x_4767_);
lean_ctor_set(v_reuseFailAlloc_4795_, 5, v_ref_4753_);
lean_ctor_set(v_reuseFailAlloc_4795_, 6, v_currNamespace_4754_);
lean_ctor_set(v_reuseFailAlloc_4795_, 7, v_openDecls_4755_);
lean_ctor_set(v_reuseFailAlloc_4795_, 8, v_initHeartbeats_4756_);
lean_ctor_set(v_reuseFailAlloc_4795_, 9, v_maxHeartbeats_4757_);
lean_ctor_set(v_reuseFailAlloc_4795_, 10, v_quotContext_4758_);
lean_ctor_set(v_reuseFailAlloc_4795_, 11, v_currMacroScope_4759_);
lean_ctor_set(v_reuseFailAlloc_4795_, 12, v_cancelTk_x3f_4760_);
lean_ctor_set(v_reuseFailAlloc_4795_, 13, v_inheritedTraceOptions_4762_);
lean_ctor_set_uint8(v_reuseFailAlloc_4795_, sizeof(void*)*14 + 1, v_suppressElabErrors_4761_);
v___x_4769_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
lean_object* v___x_4770_; 
lean_ctor_set_uint8(v___x_4769_, sizeof(void*)*14, v___x_4745_);
lean_inc(v___x_4749_);
lean_inc(v_name_4683_);
v___x_4770_ = lean_apply_7(v_act_4682_, v_name_4683_, v_constInfo_4684_, v___x_4712_, v___x_4749_, v___x_4769_, v___y_4748_, lean_box(0));
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v_ngen_4774_; lean_object* v_cache_4775_; lean_object* v_cache_4776_; lean_object* v___x_4778_; 
lean_dec(v_name_4683_);
lean_dec(v_modName_4678_);
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_a_4771_);
lean_dec_ref(v___x_4770_);
v___x_4772_ = lean_st_ref_get(v___x_4749_);
lean_dec(v___x_4749_);
v___x_4773_ = lean_st_ref_get(v___x_4719_);
lean_dec(v___x_4719_);
v_ngen_4774_ = lean_ctor_get(v___x_4773_, 2);
lean_inc_ref(v_ngen_4774_);
v_cache_4775_ = lean_ctor_get(v___x_4773_, 5);
lean_inc_ref(v_cache_4775_);
lean_dec(v___x_4773_);
v_cache_4776_ = lean_ctor_get(v___x_4772_, 1);
lean_inc_ref(v_cache_4776_);
lean_dec(v___x_4772_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 2, v_cache_4776_);
lean_ctor_set(v___x_4693_, 1, v_cache_4775_);
lean_ctor_set(v___x_4693_, 0, v_ngen_4774_);
v___x_4778_ = v___x_4693_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_ngen_4774_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_cache_4775_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_cache_4776_);
v___x_4778_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; uint8_t v___x_4781_; 
v___x_4779_ = lean_st_ref_set(v_cacheRef_4680_, v___x_4778_);
v___x_4780_ = lean_array_get_size(v_a_4771_);
v___x_4781_ = lean_nat_dec_lt(v___x_4695_, v___x_4780_);
if (v___x_4781_ == 0)
{
lean_dec(v_a_4771_);
return v_tree_4681_;
}
else
{
uint8_t v___x_4782_; 
v___x_4782_ = lean_nat_dec_le(v___x_4780_, v___x_4780_);
if (v___x_4782_ == 0)
{
if (v___x_4781_ == 0)
{
lean_dec(v_a_4771_);
return v_tree_4681_;
}
else
{
size_t v___x_4783_; size_t v___x_4784_; lean_object* v___x_4785_; 
v___x_4783_ = ((size_t)0ULL);
v___x_4784_ = lean_usize_of_nat(v___x_4780_);
v___x_4785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4771_, v___x_4783_, v___x_4784_, v_tree_4681_);
lean_dec(v_a_4771_);
return v___x_4785_;
}
}
else
{
size_t v___x_4786_; size_t v___x_4787_; lean_object* v___x_4788_; 
v___x_4786_ = ((size_t)0ULL);
v___x_4787_ = lean_usize_of_nat(v___x_4780_);
v___x_4788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4771_, v___x_4786_, v___x_4787_, v_tree_4681_);
lean_dec(v_a_4771_);
return v___x_4788_;
}
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_dec(v___x_4749_);
lean_dec(v___x_4719_);
lean_del_object(v___x_4693_);
v_a_4790_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_a_4790_);
lean_dec_ref(v___x_4770_);
v___x_4791_ = lean_st_ref_take(v_d_4679_);
v___x_4792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4792_, 0, v_modName_4678_);
lean_ctor_set(v___x_4792_, 1, v_name_4683_);
lean_ctor_set(v___x_4792_, 2, v_a_4790_);
v___x_4793_ = lean_array_push(v___x_4791_, v___x_4792_);
v___x_4794_ = lean_st_ref_set(v_d_4679_, v___x_4793_);
return v_tree_4681_;
}
}
}
}
v___jp_4799_:
{
if (v___y_4800_ == 0)
{
lean_object* v___x_4801_; lean_object* v_env_4802_; lean_object* v_nextMacroScope_4803_; lean_object* v_ngen_4804_; lean_object* v_auxDeclNGen_4805_; lean_object* v_traceState_4806_; lean_object* v_messages_4807_; lean_object* v_infoState_4808_; lean_object* v_snapshotTasks_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4819_; 
v___x_4801_ = lean_st_ref_take(v___x_4719_);
v_env_4802_ = lean_ctor_get(v___x_4801_, 0);
v_nextMacroScope_4803_ = lean_ctor_get(v___x_4801_, 1);
v_ngen_4804_ = lean_ctor_get(v___x_4801_, 2);
v_auxDeclNGen_4805_ = lean_ctor_get(v___x_4801_, 3);
v_traceState_4806_ = lean_ctor_get(v___x_4801_, 4);
v_messages_4807_ = lean_ctor_get(v___x_4801_, 6);
v_infoState_4808_ = lean_ctor_get(v___x_4801_, 7);
v_snapshotTasks_4809_ = lean_ctor_get(v___x_4801_, 8);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4801_);
if (v_isSharedCheck_4819_ == 0)
{
lean_object* v_unused_4820_; 
v_unused_4820_ = lean_ctor_get(v___x_4801_, 5);
lean_dec(v_unused_4820_);
v___x_4811_ = v___x_4801_;
v_isShared_4812_ = v_isSharedCheck_4819_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_snapshotTasks_4809_);
lean_inc(v_infoState_4808_);
lean_inc(v_messages_4807_);
lean_inc(v_traceState_4806_);
lean_inc(v_auxDeclNGen_4805_);
lean_inc(v_ngen_4804_);
lean_inc(v_nextMacroScope_4803_);
lean_inc(v_env_4802_);
lean_dec(v___x_4801_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4819_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4816_; 
v___x_4813_ = l_Lean_Kernel_enableDiag(v_env_4802_, v___x_4745_);
v___x_4814_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4812_ == 0)
{
lean_ctor_set(v___x_4811_, 5, v___x_4814_);
lean_ctor_set(v___x_4811_, 0, v___x_4813_);
v___x_4816_ = v___x_4811_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4813_);
lean_ctor_set(v_reuseFailAlloc_4818_, 1, v_nextMacroScope_4803_);
lean_ctor_set(v_reuseFailAlloc_4818_, 2, v_ngen_4804_);
lean_ctor_set(v_reuseFailAlloc_4818_, 3, v_auxDeclNGen_4805_);
lean_ctor_set(v_reuseFailAlloc_4818_, 4, v_traceState_4806_);
lean_ctor_set(v_reuseFailAlloc_4818_, 5, v___x_4814_);
lean_ctor_set(v_reuseFailAlloc_4818_, 6, v_messages_4807_);
lean_ctor_set(v_reuseFailAlloc_4818_, 7, v_infoState_4808_);
lean_ctor_set(v_reuseFailAlloc_4818_, 8, v_snapshotTasks_4809_);
v___x_4816_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
lean_object* v___x_4817_; 
v___x_4817_ = lean_st_ref_set(v___x_4719_, v___x_4816_);
lean_inc(v___x_4719_);
v___y_4747_ = v___x_4743_;
v___y_4748_ = v___x_4719_;
goto v___jp_4746_;
}
}
}
else
{
lean_inc(v___x_4719_);
v___y_4747_ = v___x_4743_;
v___y_4748_ = v___x_4719_;
goto v___jp_4746_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_constInfo_4684_);
lean_dec(v_name_4683_);
lean_dec_ref(v_act_4682_);
lean_dec(v_modName_4678_);
lean_dec_ref(v_env_4677_);
lean_dec_ref(v_cctx_4676_);
return v_tree_4681_;
}
}
else
{
lean_dec_ref(v_constInfo_4684_);
lean_dec(v_name_4683_);
lean_dec_ref(v_act_4682_);
lean_dec(v_modName_4678_);
lean_dec_ref(v_env_4677_);
lean_dec_ref(v_cctx_4676_);
return v_tree_4681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4826_, lean_object* v_env_4827_, lean_object* v_modName_4828_, lean_object* v_d_4829_, lean_object* v_cacheRef_4830_, lean_object* v_tree_4831_, lean_object* v_act_4832_, lean_object* v_name_4833_, lean_object* v_constInfo_4834_, lean_object* v_a_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4826_, v_env_4827_, v_modName_4828_, v_d_4829_, v_cacheRef_4830_, v_tree_4831_, v_act_4832_, v_name_4833_, v_constInfo_4834_);
lean_dec(v_cacheRef_4830_);
lean_dec(v_d_4829_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4837_, lean_object* v_cctx_4838_, lean_object* v_env_4839_, lean_object* v_modName_4840_, lean_object* v_d_4841_, lean_object* v_cacheRef_4842_, lean_object* v_tree_4843_, lean_object* v_act_4844_, lean_object* v_name_4845_, lean_object* v_constInfo_4846_){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4838_, v_env_4839_, v_modName_4840_, v_d_4841_, v_cacheRef_4842_, v_tree_4843_, v_act_4844_, v_name_4845_, v_constInfo_4846_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4849_, lean_object* v_cctx_4850_, lean_object* v_env_4851_, lean_object* v_modName_4852_, lean_object* v_d_4853_, lean_object* v_cacheRef_4854_, lean_object* v_tree_4855_, lean_object* v_act_4856_, lean_object* v_name_4857_, lean_object* v_constInfo_4858_, lean_object* v_a_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4849_, v_cctx_4850_, v_env_4851_, v_modName_4852_, v_d_4853_, v_cacheRef_4854_, v_tree_4855_, v_act_4856_, v_name_4857_, v_constInfo_4858_);
lean_dec(v_cacheRef_4854_);
lean_dec(v_d_4853_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object* v_00_u03b1_4861_, lean_object* v_as_4862_, size_t v_i_4863_, size_t v_stop_4864_, lean_object* v_b_4865_){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4862_, v_i_4863_, v_stop_4864_, v_b_4865_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object* v_00_u03b1_4867_, lean_object* v_as_4868_, lean_object* v_i_4869_, lean_object* v_stop_4870_, lean_object* v_b_4871_){
_start:
{
size_t v_i_boxed_4872_; size_t v_stop_boxed_4873_; lean_object* v_res_4874_; 
v_i_boxed_4872_ = lean_unbox_usize(v_i_4869_);
lean_dec(v_i_4869_);
v_stop_boxed_4873_ = lean_unbox_usize(v_stop_4870_);
lean_dec(v_stop_4870_);
v_res_4874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(v_00_u03b1_4867_, v_as_4868_, v_i_boxed_4872_, v_stop_boxed_4873_, v_b_4871_);
lean_dec_ref(v_as_4868_);
return v_res_4874_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4877_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0));
v___x_4878_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
lean_ctor_set(v___x_4879_, 1, v___x_4877_);
return v___x_4879_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2(void){
_start:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4880_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0));
v___x_4881_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1);
v___x_4882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4881_);
lean_ctor_set(v___x_4882_, 1, v___x_4880_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4883_){
_start:
{
lean_object* v___x_4884_; 
v___x_4884_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2);
return v___x_4884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4885_, lean_object* v_y_4886_){
_start:
{
lean_object* v_tree_4887_; lean_object* v_errors_4888_; lean_object* v_tree_4889_; lean_object* v_errors_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4899_; 
v_tree_4887_ = lean_ctor_get(v_x_4885_, 0);
lean_inc_ref(v_tree_4887_);
v_errors_4888_ = lean_ctor_get(v_x_4885_, 1);
lean_inc_ref(v_errors_4888_);
lean_dec_ref(v_x_4885_);
v_tree_4889_ = lean_ctor_get(v_y_4886_, 0);
v_errors_4890_ = lean_ctor_get(v_y_4886_, 1);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_y_4886_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4892_ = v_y_4886_;
v_isShared_4893_ = v_isSharedCheck_4899_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_errors_4890_);
lean_inc(v_tree_4889_);
lean_dec(v_y_4886_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4899_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4897_; 
v___x_4894_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4887_, v_tree_4889_);
v___x_4895_ = l_Array_append___redArg(v_errors_4888_, v_errors_4890_);
lean_dec_ref(v_errors_4890_);
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 1, v___x_4895_);
lean_ctor_set(v___x_4892_, 0, v___x_4894_);
v___x_4897_ = v___x_4892_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v___x_4894_);
lean_ctor_set(v_reuseFailAlloc_4898_, 1, v___x_4895_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4900_, lean_object* v_x_4901_, lean_object* v_y_4902_){
_start:
{
lean_object* v___x_4903_; 
v___x_4903_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4901_, v_y_4902_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4905_){
_start:
{
lean_object* v___x_4906_; 
v___x_4906_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
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
lean_object* v_constInfo_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v_constInfo_4940_ = lean_array_fget_borrowed(v_constants_4937_, v_i_4935_);
v___x_4941_ = l_Lean_ConstantInfo_name(v_constInfo_4940_);
lean_inc(v_constInfo_4940_);
lean_inc_ref(v_act_4929_);
lean_inc(v_mname_4933_);
lean_inc_ref(v_env_4928_);
lean_inc_ref(v_cctx_4927_);
v___x_4942_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4927_, v_env_4928_, v_mname_4933_, v_d_4930_, v_cacheRef_4931_, v_tree_4932_, v_act_4929_, v___x_4941_, v_constInfo_4940_);
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
lean_object* v___x_4992_; lean_object* v_moduleData_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v_mname_4996_; lean_object* v___x_4997_; lean_object* v_mdata_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_4992_ = l_Lean_Environment_header(v_env_4982_);
v_moduleData_4993_ = lean_ctor_get(v___x_4992_, 6);
lean_inc_ref(v_moduleData_4993_);
v___x_4994_ = lean_box(0);
v___x_4995_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4992_);
v_mname_4996_ = lean_array_get(v___x_4994_, v___x_4995_, v_start_4987_);
lean_dec_ref(v___x_4995_);
v___x_4997_ = l_Lean_instInhabitedModuleData_default;
v_mdata_4998_ = lean_array_get(v___x_4997_, v_moduleData_4993_, v_start_4987_);
lean_dec_ref(v_moduleData_4993_);
v___x_4999_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4983_);
lean_inc_ref(v_env_4982_);
lean_inc_ref(v_cctx_4981_);
v___x_5000_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4981_, v_env_4982_, v_act_4983_, v_d_4984_, v_cacheRef_4985_, v_tree_4986_, v_mname_4996_, v_mdata_4998_, v___x_4999_);
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
v___x_5046_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1);
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
lean_inc(v_toBind_5126_);
lean_dec_ref(v_inst_5123_);
v_getNGen_5127_ = lean_ctor_get(v_inst_5124_, 0);
lean_inc(v_getNGen_5127_);
v_setNGen_5128_ = lean_ctor_get(v_inst_5124_, 1);
lean_inc(v_setNGen_5128_);
lean_dec_ref(v_inst_5124_);
v_toPure_5129_ = lean_ctor_get(v_toApplicative_5125_, 1);
lean_inc(v_toPure_5129_);
lean_dec_ref(v_toApplicative_5125_);
lean_inc(v_toBind_5126_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0(lean_object* v_cctx_5136_, lean_object* v_env_5137_, lean_object* v_mainModule_5138_, lean_object* v_d_5139_, lean_object* v_val_5140_, lean_object* v_act_5141_, lean_object* v_t_5142_, lean_object* v_n_5143_, lean_object* v_c_5144_){
_start:
{
lean_object* v___x_5146_; 
v___x_5146_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5136_, v_env_5137_, v_mainModule_5138_, v_d_5139_, v_val_5140_, v_t_5142_, v_act_5141_, v_n_5143_, v_c_5144_);
return v___x_5146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0___boxed(lean_object* v_cctx_5147_, lean_object* v_env_5148_, lean_object* v_mainModule_5149_, lean_object* v_d_5150_, lean_object* v_val_5151_, lean_object* v_act_5152_, lean_object* v_t_5153_, lean_object* v_n_5154_, lean_object* v_c_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0(v_cctx_5147_, v_env_5148_, v_mainModule_5149_, v_d_5150_, v_val_5151_, v_act_5152_, v_t_5153_, v_n_5154_, v_c_5155_);
lean_dec(v_val_5151_);
lean_dec(v_d_5150_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(lean_object* v_f_5158_, lean_object* v_keys_5159_, lean_object* v_vals_5160_, lean_object* v_i_5161_, lean_object* v_acc_5162_){
_start:
{
lean_object* v___x_5164_; uint8_t v___x_5165_; 
v___x_5164_ = lean_array_get_size(v_keys_5159_);
v___x_5165_ = lean_nat_dec_lt(v_i_5161_, v___x_5164_);
if (v___x_5165_ == 0)
{
lean_dec(v_i_5161_);
lean_dec_ref(v_f_5158_);
return v_acc_5162_;
}
else
{
lean_object* v_k_5166_; lean_object* v_v_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v_k_5166_ = lean_array_fget_borrowed(v_keys_5159_, v_i_5161_);
v_v_5167_ = lean_array_fget_borrowed(v_vals_5160_, v_i_5161_);
lean_inc_ref(v_f_5158_);
lean_inc(v_v_5167_);
lean_inc(v_k_5166_);
v___x_5168_ = lean_apply_4(v_f_5158_, v_acc_5162_, v_k_5166_, v_v_5167_, lean_box(0));
v___x_5169_ = lean_unsigned_to_nat(1u);
v___x_5170_ = lean_nat_add(v_i_5161_, v___x_5169_);
lean_dec(v_i_5161_);
v_i_5161_ = v___x_5170_;
v_acc_5162_ = v___x_5168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_5172_, lean_object* v_keys_5173_, lean_object* v_vals_5174_, lean_object* v_i_5175_, lean_object* v_acc_5176_, lean_object* v___y_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(v_f_5172_, v_keys_5173_, v_vals_5174_, v_i_5175_, v_acc_5176_);
lean_dec_ref(v_vals_5174_);
lean_dec_ref(v_keys_5173_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(lean_object* v_f_5179_, lean_object* v_x_5180_, lean_object* v_x_5181_){
_start:
{
if (lean_obj_tag(v_x_5180_) == 0)
{
lean_object* v_es_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; uint8_t v___x_5186_; 
v_es_5183_ = lean_ctor_get(v_x_5180_, 0);
v___x_5184_ = lean_unsigned_to_nat(0u);
v___x_5185_ = lean_array_get_size(v_es_5183_);
v___x_5186_ = lean_nat_dec_lt(v___x_5184_, v___x_5185_);
if (v___x_5186_ == 0)
{
lean_dec_ref(v_f_5179_);
return v_x_5181_;
}
else
{
uint8_t v___x_5187_; 
v___x_5187_ = lean_nat_dec_le(v___x_5185_, v___x_5185_);
if (v___x_5187_ == 0)
{
if (v___x_5186_ == 0)
{
lean_dec_ref(v_f_5179_);
return v_x_5181_;
}
else
{
size_t v___x_5188_; size_t v___x_5189_; lean_object* v___x_5190_; 
v___x_5188_ = ((size_t)0ULL);
v___x_5189_ = lean_usize_of_nat(v___x_5185_);
v___x_5190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5179_, v_es_5183_, v___x_5188_, v___x_5189_, v_x_5181_);
return v___x_5190_;
}
}
else
{
size_t v___x_5191_; size_t v___x_5192_; lean_object* v___x_5193_; 
v___x_5191_ = ((size_t)0ULL);
v___x_5192_ = lean_usize_of_nat(v___x_5185_);
v___x_5193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5179_, v_es_5183_, v___x_5191_, v___x_5192_, v_x_5181_);
return v___x_5193_;
}
}
}
else
{
lean_object* v_ks_5194_; lean_object* v_vs_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; 
v_ks_5194_ = lean_ctor_get(v_x_5180_, 0);
v_vs_5195_ = lean_ctor_get(v_x_5180_, 1);
v___x_5196_ = lean_unsigned_to_nat(0u);
v___x_5197_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(v_f_5179_, v_ks_5194_, v_vs_5195_, v___x_5196_, v_x_5181_);
return v___x_5197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(lean_object* v_f_5198_, lean_object* v_as_5199_, size_t v_i_5200_, size_t v_stop_5201_, lean_object* v_b_5202_){
_start:
{
lean_object* v_val_5205_; lean_object* v___y_5210_; uint8_t v___x_5211_; 
v___x_5211_ = lean_usize_dec_eq(v_i_5200_, v_stop_5201_);
if (v___x_5211_ == 0)
{
lean_object* v___x_5212_; 
v___x_5212_ = lean_array_uget_borrowed(v_as_5199_, v_i_5200_);
switch(lean_obj_tag(v___x_5212_))
{
case 0:
{
lean_object* v_key_5213_; lean_object* v_val_5214_; lean_object* v___x_5215_; 
v_key_5213_ = lean_ctor_get(v___x_5212_, 0);
v_val_5214_ = lean_ctor_get(v___x_5212_, 1);
lean_inc_ref(v_f_5198_);
lean_inc(v_val_5214_);
lean_inc(v_key_5213_);
v___x_5215_ = lean_apply_4(v_f_5198_, v_b_5202_, v_key_5213_, v_val_5214_, lean_box(0));
v___y_5210_ = v___x_5215_;
goto v___jp_5209_;
}
case 1:
{
lean_object* v_node_5216_; lean_object* v___x_5217_; 
v_node_5216_ = lean_ctor_get(v___x_5212_, 0);
lean_inc_ref(v_f_5198_);
v___x_5217_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5198_, v_node_5216_, v_b_5202_);
v___y_5210_ = v___x_5217_;
goto v___jp_5209_;
}
default: 
{
v_val_5205_ = v_b_5202_;
goto v___jp_5204_;
}
}
}
else
{
lean_dec_ref(v_f_5198_);
return v_b_5202_;
}
v___jp_5204_:
{
size_t v___x_5206_; size_t v___x_5207_; 
v___x_5206_ = ((size_t)1ULL);
v___x_5207_ = lean_usize_add(v_i_5200_, v___x_5206_);
v_i_5200_ = v___x_5207_;
v_b_5202_ = v_val_5205_;
goto _start;
}
v___jp_5209_:
{
v_val_5205_ = v___y_5210_;
goto v___jp_5204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_5218_, lean_object* v_as_5219_, lean_object* v_i_5220_, lean_object* v_stop_5221_, lean_object* v_b_5222_, lean_object* v___y_5223_){
_start:
{
size_t v_i_boxed_5224_; size_t v_stop_boxed_5225_; lean_object* v_res_5226_; 
v_i_boxed_5224_ = lean_unbox_usize(v_i_5220_);
lean_dec(v_i_5220_);
v_stop_boxed_5225_ = lean_unbox_usize(v_stop_5221_);
lean_dec(v_stop_5221_);
v_res_5226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5218_, v_as_5219_, v_i_boxed_5224_, v_stop_boxed_5225_, v_b_5222_);
lean_dec_ref(v_as_5219_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg___boxed(lean_object* v_f_5227_, lean_object* v_x_5228_, lean_object* v_x_5229_, lean_object* v___y_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5227_, v_x_5228_, v_x_5229_);
lean_dec_ref(v_x_5228_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5232_, lean_object* v_ngen_5233_, lean_object* v_env_5234_, lean_object* v_d_5235_, lean_object* v_act_5236_){
_start:
{
lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v_mainModule_5241_; lean_object* v___x_5242_; lean_object* v_map_u2082_5243_; lean_object* v___f_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5238_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5233_);
v___x_5239_ = lean_st_mk_ref(v___x_5238_);
v___x_5240_ = l_Lean_Environment_header(v_env_5234_);
v_mainModule_5241_ = lean_ctor_get(v___x_5240_, 0);
lean_inc(v_mainModule_5241_);
lean_dec_ref(v___x_5240_);
lean_inc_ref(v_env_5234_);
v___x_5242_ = l_Lean_Environment_constants(v_env_5234_);
v_map_u2082_5243_ = lean_ctor_get(v___x_5242_, 1);
lean_inc_ref(v_map_u2082_5243_);
lean_dec_ref(v___x_5242_);
v___f_5244_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0___boxed), 10, 6);
lean_closure_set(v___f_5244_, 0, v_cctx_5232_);
lean_closure_set(v___f_5244_, 1, v_env_5234_);
lean_closure_set(v___f_5244_, 2, v_mainModule_5241_);
lean_closure_set(v___f_5244_, 3, v_d_5235_);
lean_closure_set(v___f_5244_, 4, v___x_5239_);
lean_closure_set(v___f_5244_, 5, v_act_5236_);
v___x_5245_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1);
v___x_5246_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v___f_5244_, v_map_u2082_5243_, v___x_5245_);
lean_dec_ref(v_map_u2082_5243_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5247_, lean_object* v_ngen_5248_, lean_object* v_env_5249_, lean_object* v_d_5250_, lean_object* v_act_5251_, lean_object* v_a_5252_){
_start:
{
lean_object* v_res_5253_; 
v_res_5253_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5247_, v_ngen_5248_, v_env_5249_, v_d_5250_, v_act_5251_);
return v_res_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5254_, lean_object* v_cctx_5255_, lean_object* v_ngen_5256_, lean_object* v_env_5257_, lean_object* v_d_5258_, lean_object* v_act_5259_){
_start:
{
lean_object* v___x_5261_; 
v___x_5261_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5255_, v_ngen_5256_, v_env_5257_, v_d_5258_, v_act_5259_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5262_, lean_object* v_cctx_5263_, lean_object* v_ngen_5264_, lean_object* v_env_5265_, lean_object* v_d_5266_, lean_object* v_act_5267_, lean_object* v_a_5268_){
_start:
{
lean_object* v_res_5269_; 
v_res_5269_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5262_, v_cctx_5263_, v_ngen_5264_, v_env_5265_, v_d_5266_, v_act_5267_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_map_5270_, lean_object* v_f_5271_, lean_object* v_init_5272_){
_start:
{
lean_object* v___x_5274_; 
v___x_5274_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5271_, v_map_5270_, v_init_5272_);
return v___x_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_map_5275_, lean_object* v_f_5276_, lean_object* v_init_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v_res_5279_; 
v_res_5279_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_map_5275_, v_f_5276_, v_init_5277_);
lean_dec_ref(v_map_5275_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03c3_5280_, lean_object* v_00_u03b2_5281_, lean_object* v_map_5282_, lean_object* v_f_5283_, lean_object* v_init_5284_){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5283_, v_map_5282_, v_init_5284_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03c3_5287_, lean_object* v_00_u03b2_5288_, lean_object* v_map_5289_, lean_object* v_f_5290_, lean_object* v_init_5291_, lean_object* v___y_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03c3_5287_, v_00_u03b2_5288_, v_map_5289_, v_f_5290_, v_init_5291_);
lean_dec_ref(v_map_5289_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0(lean_object* v_00_u03c3_5294_, lean_object* v_00_u03b1_5295_, lean_object* v_00_u03b2_5296_, lean_object* v_f_5297_, lean_object* v_x_5298_, lean_object* v_x_5299_){
_start:
{
lean_object* v___x_5301_; 
v___x_5301_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5297_, v_x_5298_, v_x_5299_);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___boxed(lean_object* v_00_u03c3_5302_, lean_object* v_00_u03b1_5303_, lean_object* v_00_u03b2_5304_, lean_object* v_f_5305_, lean_object* v_x_5306_, lean_object* v_x_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0(v_00_u03c3_5302_, v_00_u03b1_5303_, v_00_u03b2_5304_, v_f_5305_, v_x_5306_, v_x_5307_);
lean_dec_ref(v_x_5306_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5310_, lean_object* v_00_u03b2_5311_, lean_object* v_00_u03c3_5312_, lean_object* v_f_5313_, lean_object* v_as_5314_, size_t v_i_5315_, size_t v_stop_5316_, lean_object* v_b_5317_){
_start:
{
lean_object* v___x_5319_; 
v___x_5319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5313_, v_as_5314_, v_i_5315_, v_stop_5316_, v_b_5317_);
return v___x_5319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5320_, lean_object* v_00_u03b2_5321_, lean_object* v_00_u03c3_5322_, lean_object* v_f_5323_, lean_object* v_as_5324_, lean_object* v_i_5325_, lean_object* v_stop_5326_, lean_object* v_b_5327_, lean_object* v___y_5328_){
_start:
{
size_t v_i_boxed_5329_; size_t v_stop_boxed_5330_; lean_object* v_res_5331_; 
v_i_boxed_5329_ = lean_unbox_usize(v_i_5325_);
lean_dec(v_i_5325_);
v_stop_boxed_5330_ = lean_unbox_usize(v_stop_5326_);
lean_dec(v_stop_5326_);
v_res_5331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1(v_00_u03b1_5320_, v_00_u03b2_5321_, v_00_u03c3_5322_, v_f_5323_, v_as_5324_, v_i_boxed_5329_, v_stop_boxed_5330_, v_b_5327_);
lean_dec_ref(v_as_5324_);
return v_res_5331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_5332_, lean_object* v_00_u03b1_5333_, lean_object* v_00_u03b2_5334_, lean_object* v_f_5335_, lean_object* v_keys_5336_, lean_object* v_vals_5337_, lean_object* v_heq_5338_, lean_object* v_i_5339_, lean_object* v_acc_5340_){
_start:
{
lean_object* v___x_5342_; 
v___x_5342_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(v_f_5335_, v_keys_5336_, v_vals_5337_, v_i_5339_, v_acc_5340_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_5343_, lean_object* v_00_u03b1_5344_, lean_object* v_00_u03b2_5345_, lean_object* v_f_5346_, lean_object* v_keys_5347_, lean_object* v_vals_5348_, lean_object* v_heq_5349_, lean_object* v_i_5350_, lean_object* v_acc_5351_, lean_object* v___y_5352_){
_start:
{
lean_object* v_res_5353_; 
v_res_5353_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2(v_00_u03c3_5343_, v_00_u03b1_5344_, v_00_u03b2_5345_, v_f_5346_, v_keys_5347_, v_vals_5348_, v_heq_5349_, v_i_5350_, v_acc_5351_);
lean_dec_ref(v_vals_5348_);
lean_dec_ref(v_keys_5347_);
return v_res_5353_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5354_, lean_object* v_x_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
if (lean_obj_tag(v_x_5355_) == 0)
{
lean_object* v___x_5361_; 
v___x_5361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5361_, 0, v_x_5354_);
return v___x_5361_;
}
else
{
lean_object* v_head_5362_; lean_object* v_tail_5363_; lean_object* v___x_5364_; 
v_head_5362_ = lean_ctor_get(v_x_5355_, 0);
lean_inc(v_head_5362_);
v_tail_5363_ = lean_ctor_get(v_x_5355_, 1);
lean_inc(v_tail_5363_);
lean_dec_ref(v_x_5355_);
v___x_5364_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5354_, v_head_5362_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
if (lean_obj_tag(v___x_5364_) == 0)
{
lean_object* v_a_5365_; 
v_a_5365_ = lean_ctor_get(v___x_5364_, 0);
lean_inc(v_a_5365_);
lean_dec_ref(v___x_5364_);
v_x_5354_ = v_a_5365_;
v_x_5355_ = v_tail_5363_;
goto _start;
}
else
{
lean_dec(v_tail_5363_);
return v___x_5364_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5367_, lean_object* v_x_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_){
_start:
{
lean_object* v_res_5374_; 
v_res_5374_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5367_, v_x_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
return v_res_5374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5375_, lean_object* v_keys_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v___x_5382_; 
v___x_5382_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5375_, v_keys_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5383_, lean_object* v_keys_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5383_, v_keys_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
lean_dec(v_a_5388_);
lean_dec_ref(v_a_5387_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5391_, lean_object* v_t_5392_, lean_object* v_keys_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_){
_start:
{
lean_object* v___x_5399_; 
v___x_5399_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5392_, v_keys_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_);
return v___x_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5400_, lean_object* v_t_5401_, lean_object* v_keys_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_){
_start:
{
lean_object* v_res_5408_; 
v_res_5408_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5400_, v_t_5401_, v_keys_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_);
lean_dec(v_a_5406_);
lean_dec_ref(v_a_5405_);
lean_dec(v_a_5404_);
lean_dec_ref(v_a_5403_);
return v_res_5408_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5409_, lean_object* v_x_5410_, lean_object* v_x_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v___x_5417_; 
v___x_5417_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5410_, v_x_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5418_, lean_object* v_x_5419_, lean_object* v_x_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_){
_start:
{
lean_object* v_res_5426_; 
v_res_5426_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5418_, v_x_5419_, v_x_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_);
lean_dec(v___y_5424_);
lean_dec_ref(v___y_5423_);
lean_dec(v___y_5422_);
lean_dec_ref(v___y_5421_);
return v_res_5426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5427_, size_t v_sz_5428_, size_t v_i_5429_, lean_object* v_b_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
uint8_t v___x_5437_; 
v___x_5437_ = lean_usize_dec_lt(v_i_5429_, v_sz_5428_);
if (v___x_5437_ == 0)
{
lean_object* v___x_5438_; 
v___x_5438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5438_, 0, v_b_5430_);
return v___x_5438_;
}
else
{
lean_object* v_a_5439_; lean_object* v___x_5440_; 
v_a_5439_ = lean_array_uget_borrowed(v_as_5427_, v_i_5429_);
v___x_5440_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5439_, v_b_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v_a_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5453_; 
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5443_ = v___x_5440_;
v_isShared_5444_ = v_isSharedCheck_5453_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_a_5441_);
lean_dec(v___x_5440_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5453_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
if (lean_obj_tag(v_a_5441_) == 0)
{
lean_object* v_a_5445_; lean_object* v___x_5447_; 
v_a_5445_ = lean_ctor_get(v_a_5441_, 0);
lean_inc(v_a_5445_);
lean_dec_ref(v_a_5441_);
if (v_isShared_5444_ == 0)
{
lean_ctor_set(v___x_5443_, 0, v_a_5445_);
v___x_5447_ = v___x_5443_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_a_5445_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
else
{
lean_object* v_a_5449_; size_t v___x_5450_; size_t v___x_5451_; 
lean_del_object(v___x_5443_);
v_a_5449_ = lean_ctor_get(v_a_5441_, 0);
lean_inc(v_a_5449_);
lean_dec_ref(v_a_5441_);
v___x_5450_ = ((size_t)1ULL);
v___x_5451_ = lean_usize_add(v_i_5429_, v___x_5450_);
v_i_5429_ = v___x_5451_;
v_b_5430_ = v_a_5449_;
goto _start;
}
}
}
else
{
lean_object* v_a_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5461_; 
v_a_5454_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5456_ = v___x_5440_;
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_a_5454_);
lean_dec(v___x_5440_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5459_; 
if (v_isShared_5457_ == 0)
{
v___x_5459_ = v___x_5456_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5454_);
v___x_5459_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
return v___x_5459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_){
_start:
{
lean_object* v___x_5469_; uint8_t v___x_5470_; 
v___x_5469_ = lean_unsigned_to_nat(0u);
v___x_5470_ = lean_nat_dec_eq(v_next_5462_, v___x_5469_);
if (v___x_5470_ == 0)
{
lean_object* v___x_5471_; 
v___x_5471_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_);
if (lean_obj_tag(v___x_5471_) == 0)
{
lean_object* v_a_5472_; lean_object* v_snd_5473_; lean_object* v_fst_5474_; lean_object* v_fst_5475_; lean_object* v_snd_5476_; lean_object* v___x_5477_; 
v_a_5472_ = lean_ctor_get(v___x_5471_, 0);
lean_inc(v_a_5472_);
lean_dec_ref(v___x_5471_);
v_snd_5473_ = lean_ctor_get(v_a_5472_, 1);
lean_inc(v_snd_5473_);
v_fst_5474_ = lean_ctor_get(v_a_5472_, 0);
lean_inc(v_fst_5474_);
lean_dec(v_a_5472_);
v_fst_5475_ = lean_ctor_get(v_snd_5473_, 0);
lean_inc(v_fst_5475_);
v_snd_5476_ = lean_ctor_get(v_snd_5473_, 1);
lean_inc(v_snd_5476_);
lean_dec(v_snd_5473_);
v___x_5477_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5475_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_);
if (lean_obj_tag(v___x_5477_) == 0)
{
lean_object* v_a_5478_; lean_object* v_buckets_5479_; lean_object* v___x_5480_; size_t v_sz_5481_; size_t v___x_5482_; lean_object* v___x_5483_; 
v_a_5478_ = lean_ctor_get(v___x_5477_, 0);
lean_inc(v_a_5478_);
lean_dec_ref(v___x_5477_);
v_buckets_5479_ = lean_ctor_get(v_snd_5476_, 1);
v___x_5480_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v_sz_5481_ = lean_array_size(v_buckets_5479_);
v___x_5482_ = ((size_t)0ULL);
v___x_5483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5479_, v_sz_5481_, v___x_5482_, v___x_5480_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_);
if (lean_obj_tag(v___x_5483_) == 0)
{
lean_object* v_a_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5497_; 
v_a_5484_ = lean_ctor_get(v___x_5483_, 0);
v_isSharedCheck_5497_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5497_ == 0)
{
v___x_5486_ = v___x_5483_;
v_isShared_5487_ = v_isSharedCheck_5497_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_a_5484_);
lean_dec(v___x_5483_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5497_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5495_; 
v___x_5488_ = lean_st_ref_take(v_a_5463_);
v___x_5489_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5480_);
lean_ctor_set(v___x_5489_, 1, v_fst_5475_);
lean_ctor_set(v___x_5489_, 2, v_snd_5476_);
lean_ctor_set(v___x_5489_, 3, v___x_5480_);
v___x_5490_ = lean_array_set(v___x_5488_, v_next_5462_, v___x_5489_);
v___x_5491_ = lean_st_ref_set(v_a_5463_, v___x_5490_);
v___x_5492_ = l_Array_append___redArg(v_fst_5474_, v_a_5478_);
lean_dec(v_a_5478_);
v___x_5493_ = l_Array_append___redArg(v___x_5492_, v_a_5484_);
lean_dec(v_a_5484_);
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 0, v___x_5493_);
v___x_5495_ = v___x_5486_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5493_);
v___x_5495_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
return v___x_5495_;
}
}
}
else
{
lean_dec(v_a_5478_);
lean_dec(v_snd_5476_);
lean_dec(v_fst_5475_);
lean_dec(v_fst_5474_);
return v___x_5483_;
}
}
else
{
lean_dec(v_snd_5476_);
lean_dec(v_fst_5475_);
lean_dec(v_fst_5474_);
return v___x_5477_;
}
}
else
{
lean_object* v_a_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5505_; 
v_a_5498_ = lean_ctor_get(v___x_5471_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5500_ = v___x_5471_;
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5471_);
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
v___x_5506_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5507_, 0, v___x_5506_);
return v___x_5507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_){
_start:
{
if (lean_obj_tag(v_a_5508_) == 0)
{
lean_object* v___x_5516_; lean_object* v___x_5517_; 
v___x_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5516_, 0, v_a_5509_);
v___x_5517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5517_, 0, v___x_5516_);
return v___x_5517_;
}
else
{
lean_object* v_value_5518_; lean_object* v_tail_5519_; lean_object* v___x_5520_; 
v_value_5518_ = lean_ctor_get(v_a_5508_, 1);
v_tail_5519_ = lean_ctor_get(v_a_5508_, 2);
v___x_5520_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5518_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_);
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v_a_5521_; lean_object* v___x_5522_; 
v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
lean_inc(v_a_5521_);
lean_dec_ref(v___x_5520_);
v___x_5522_ = l_Array_append___redArg(v_a_5509_, v_a_5521_);
lean_dec(v_a_5521_);
v_a_5508_ = v_tail_5519_;
v_a_5509_ = v___x_5522_;
goto _start;
}
else
{
lean_object* v_a_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5531_; 
lean_dec_ref(v_a_5509_);
v_a_5524_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5526_ = v___x_5520_;
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_dec(v___x_5520_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___x_5529_; 
if (v_isShared_5527_ == 0)
{
v___x_5529_ = v___x_5526_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_){
_start:
{
lean_object* v_res_5540_; 
v_res_5540_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5532_, v_a_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec_ref(v___y_5535_);
lean_dec(v___y_5534_);
lean_dec(v_a_5532_);
return v_res_5540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5541_, lean_object* v_sz_5542_, lean_object* v_i_5543_, lean_object* v_b_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_){
_start:
{
size_t v_sz_boxed_5551_; size_t v_i_boxed_5552_; lean_object* v_res_5553_; 
v_sz_boxed_5551_ = lean_unbox_usize(v_sz_5542_);
lean_dec(v_sz_5542_);
v_i_boxed_5552_ = lean_unbox_usize(v_i_5543_);
lean_dec(v_i_5543_);
v_res_5553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5541_, v_sz_boxed_5551_, v_i_boxed_5552_, v_b_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_);
lean_dec(v___y_5549_);
lean_dec_ref(v___y_5548_);
lean_dec(v___y_5547_);
lean_dec_ref(v___y_5546_);
lean_dec(v___y_5545_);
lean_dec_ref(v_as_5541_);
return v_res_5553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_){
_start:
{
lean_object* v_res_5561_; 
v_res_5561_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5554_, v_a_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_);
lean_dec(v_a_5559_);
lean_dec_ref(v_a_5558_);
lean_dec(v_a_5557_);
lean_dec_ref(v_a_5556_);
lean_dec(v_a_5555_);
lean_dec(v_next_5554_);
return v_res_5561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5562_, lean_object* v_next_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_){
_start:
{
lean_object* v___x_5570_; 
v___x_5570_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_);
return v___x_5570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5571_, lean_object* v_next_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_){
_start:
{
lean_object* v_res_5579_; 
v_res_5579_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5571_, v_next_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_);
lean_dec(v_a_5577_);
lean_dec_ref(v_a_5576_);
lean_dec(v_a_5575_);
lean_dec_ref(v_a_5574_);
lean_dec(v_a_5573_);
lean_dec(v_next_5572_);
return v_res_5579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_){
_start:
{
lean_object* v___x_5589_; 
v___x_5589_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5581_, v_a_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_);
return v___x_5589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_){
_start:
{
lean_object* v_res_5599_; 
v_res_5599_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5590_, v_a_5591_, v_a_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_);
lean_dec(v___y_5597_);
lean_dec_ref(v___y_5596_);
lean_dec(v___y_5595_);
lean_dec_ref(v___y_5594_);
lean_dec(v___y_5593_);
lean_dec(v_a_5591_);
return v_res_5599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5600_, lean_object* v_as_5601_, size_t v_sz_5602_, size_t v_i_5603_, lean_object* v_b_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
lean_object* v___x_5611_; 
v___x_5611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5601_, v_sz_5602_, v_i_5603_, v_b_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
return v___x_5611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5612_, lean_object* v_as_5613_, lean_object* v_sz_5614_, lean_object* v_i_5615_, lean_object* v_b_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_){
_start:
{
size_t v_sz_boxed_5623_; size_t v_i_boxed_5624_; lean_object* v_res_5625_; 
v_sz_boxed_5623_ = lean_unbox_usize(v_sz_5614_);
lean_dec(v_sz_5614_);
v_i_boxed_5624_ = lean_unbox_usize(v_i_5615_);
lean_dec(v_i_5615_);
v_res_5625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5612_, v_as_5613_, v_sz_boxed_5623_, v_i_boxed_5624_, v_b_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
lean_dec(v___y_5621_);
lean_dec_ref(v___y_5620_);
lean_dec(v___y_5619_);
lean_dec_ref(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec_ref(v_as_5613_);
return v_res_5625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5626_, lean_object* v_rest_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_){
_start:
{
lean_object* v___x_5634_; uint8_t v___x_5635_; 
v___x_5634_ = lean_unsigned_to_nat(0u);
v___x_5635_ = lean_nat_dec_eq(v_next_5626_, v___x_5634_);
if (v___x_5635_ == 0)
{
lean_object* v___x_5636_; 
v___x_5636_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5626_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_);
if (lean_obj_tag(v___x_5636_) == 0)
{
lean_object* v_a_5637_; lean_object* v_snd_5638_; 
v_a_5637_ = lean_ctor_get(v___x_5636_, 0);
lean_inc(v_a_5637_);
lean_dec_ref(v___x_5636_);
v_snd_5638_ = lean_ctor_get(v_a_5637_, 1);
lean_inc(v_snd_5638_);
lean_dec(v_a_5637_);
if (lean_obj_tag(v_rest_5627_) == 0)
{
lean_object* v___x_5639_; 
lean_dec(v_snd_5638_);
v___x_5639_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5626_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_);
lean_dec(v_next_5626_);
return v___x_5639_;
}
else
{
lean_object* v_fst_5640_; lean_object* v_snd_5641_; lean_object* v_head_5642_; lean_object* v_tail_5643_; lean_object* v___x_5644_; uint8_t v___x_5645_; 
lean_dec(v_next_5626_);
v_fst_5640_ = lean_ctor_get(v_snd_5638_, 0);
lean_inc(v_fst_5640_);
v_snd_5641_ = lean_ctor_get(v_snd_5638_, 1);
lean_inc(v_snd_5641_);
lean_dec(v_snd_5638_);
v_head_5642_ = lean_ctor_get(v_rest_5627_, 0);
v_tail_5643_ = lean_ctor_get(v_rest_5627_, 1);
v___x_5644_ = lean_box(3);
v___x_5645_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5642_, v___x_5644_);
if (v___x_5645_ == 0)
{
lean_object* v___x_5646_; 
lean_dec(v_fst_5640_);
v___x_5646_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5641_, v_head_5642_, v___x_5634_);
lean_dec(v_snd_5641_);
v_next_5626_ = v___x_5646_;
v_rest_5627_ = v_tail_5643_;
goto _start;
}
else
{
lean_dec(v_snd_5641_);
v_next_5626_ = v_fst_5640_;
v_rest_5627_ = v_tail_5643_;
goto _start;
}
}
}
else
{
lean_object* v_a_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5656_; 
lean_dec(v_next_5626_);
v_a_5649_ = lean_ctor_get(v___x_5636_, 0);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5636_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5651_ = v___x_5636_;
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_a_5649_);
lean_dec(v___x_5636_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
lean_object* v___x_5654_; 
if (v_isShared_5652_ == 0)
{
v___x_5654_ = v___x_5651_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5649_);
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
else
{
lean_object* v___x_5657_; lean_object* v___x_5658_; 
lean_dec(v_next_5626_);
v___x_5657_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5657_);
return v___x_5658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5659_, lean_object* v_rest_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_){
_start:
{
lean_object* v_res_5667_; 
v_res_5667_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5659_, v_rest_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_, v_a_5665_);
lean_dec(v_a_5665_);
lean_dec_ref(v_a_5664_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
lean_dec(v_a_5661_);
lean_dec(v_rest_5660_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5668_, lean_object* v_next_5669_, lean_object* v_rest_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_){
_start:
{
lean_object* v___x_5677_; 
v___x_5677_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5669_, v_rest_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_, v_a_5675_);
return v___x_5677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5678_, lean_object* v_next_5679_, lean_object* v_rest_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_){
_start:
{
lean_object* v_res_5687_; 
v_res_5687_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5678_, v_next_5679_, v_rest_5680_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_, v_a_5685_);
lean_dec(v_a_5685_);
lean_dec_ref(v_a_5684_);
lean_dec(v_a_5683_);
lean_dec_ref(v_a_5682_);
lean_dec(v_a_5681_);
lean_dec(v_rest_5680_);
return v_res_5687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5688_, lean_object* v_path_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_){
_start:
{
if (lean_obj_tag(v_path_5689_) == 0)
{
lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; 
v___x_5695_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5695_);
lean_ctor_set(v___x_5696_, 1, v_t_5688_);
v___x_5697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5697_, 0, v___x_5696_);
return v___x_5697_;
}
else
{
lean_object* v_head_5698_; lean_object* v_tail_5699_; lean_object* v_roots_5700_; lean_object* v___x_5701_; lean_object* v_idx_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; 
v_head_5698_ = lean_ctor_get(v_path_5689_, 0);
lean_inc(v_head_5698_);
v_tail_5699_ = lean_ctor_get(v_path_5689_, 1);
lean_inc(v_tail_5699_);
lean_dec_ref(v_path_5689_);
v_roots_5700_ = lean_ctor_get(v_t_5688_, 1);
v___x_5701_ = lean_unsigned_to_nat(0u);
v_idx_5702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5700_, v_head_5698_, v___x_5701_);
lean_dec(v_head_5698_);
v___x_5703_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5703_, 0, lean_box(0));
lean_closure_set(v___x_5703_, 1, v_idx_5702_);
lean_closure_set(v___x_5703_, 2, v_tail_5699_);
v___x_5704_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5688_, v___x_5703_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_);
return v___x_5704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5705_, lean_object* v_path_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
lean_object* v_res_5712_; 
v_res_5712_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5705_, v_path_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_);
lean_dec(v_a_5710_);
lean_dec_ref(v_a_5709_);
lean_dec(v_a_5708_);
lean_dec_ref(v_a_5707_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5713_, lean_object* v_t_5714_, lean_object* v_path_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_){
_start:
{
lean_object* v___x_5721_; 
v___x_5721_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5714_, v_path_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_);
return v___x_5721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5722_, lean_object* v_t_5723_, lean_object* v_path_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_){
_start:
{
lean_object* v_res_5730_; 
v_res_5730_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5722_, v_t_5723_, v_path_5724_, v_a_5725_, v_a_5726_, v_a_5727_, v_a_5728_);
lean_dec(v_a_5728_);
lean_dec_ref(v_a_5727_);
lean_dec(v_a_5726_);
lean_dec_ref(v_a_5725_);
return v_res_5730_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5731_, lean_object* v_b_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_){
_start:
{
if (lean_obj_tag(v_as_x27_5731_) == 0)
{
lean_object* v___x_5738_; 
v___x_5738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5738_, 0, v_b_5732_);
return v___x_5738_;
}
else
{
lean_object* v_head_5739_; lean_object* v_tail_5740_; lean_object* v_fst_5741_; lean_object* v_snd_5742_; lean_object* v___x_5743_; 
v_head_5739_ = lean_ctor_get(v_as_x27_5731_, 0);
lean_inc(v_head_5739_);
v_tail_5740_ = lean_ctor_get(v_as_x27_5731_, 1);
lean_inc(v_tail_5740_);
lean_dec_ref(v_as_x27_5731_);
v_fst_5741_ = lean_ctor_get(v_b_5732_, 0);
lean_inc(v_fst_5741_);
v_snd_5742_ = lean_ctor_get(v_b_5732_, 1);
lean_inc(v_snd_5742_);
lean_dec_ref(v_b_5732_);
v___x_5743_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5742_, v_head_5739_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_);
if (lean_obj_tag(v___x_5743_) == 0)
{
lean_object* v_a_5744_; lean_object* v_fst_5745_; lean_object* v_snd_5746_; lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5755_; 
v_a_5744_ = lean_ctor_get(v___x_5743_, 0);
lean_inc(v_a_5744_);
lean_dec_ref(v___x_5743_);
v_fst_5745_ = lean_ctor_get(v_a_5744_, 0);
v_snd_5746_ = lean_ctor_get(v_a_5744_, 1);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_a_5744_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5748_ = v_a_5744_;
v_isShared_5749_ = v_isSharedCheck_5755_;
goto v_resetjp_5747_;
}
else
{
lean_inc(v_snd_5746_);
lean_inc(v_fst_5745_);
lean_dec(v_a_5744_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5755_;
goto v_resetjp_5747_;
}
v_resetjp_5747_:
{
lean_object* v___x_5750_; lean_object* v___x_5752_; 
v___x_5750_ = l_Array_append___redArg(v_fst_5741_, v_fst_5745_);
lean_dec(v_fst_5745_);
if (v_isShared_5749_ == 0)
{
lean_ctor_set(v___x_5748_, 0, v___x_5750_);
v___x_5752_ = v___x_5748_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5750_);
lean_ctor_set(v_reuseFailAlloc_5754_, 1, v_snd_5746_);
v___x_5752_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
v_as_x27_5731_ = v_tail_5740_;
v_b_5732_ = v___x_5752_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5741_);
lean_dec(v_tail_5740_);
return v___x_5743_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5756_, lean_object* v_b_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_){
_start:
{
lean_object* v_res_5763_; 
v_res_5763_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5756_, v_b_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_);
lean_dec(v___y_5761_);
lean_dec_ref(v___y_5760_);
lean_dec(v___y_5759_);
lean_dec_ref(v___y_5758_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5764_, lean_object* v_keys_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_){
_start:
{
lean_object* v_allExtracted_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; 
v_allExtracted_5771_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5772_, 0, v_allExtracted_5771_);
lean_ctor_set(v___x_5772_, 1, v_t_5764_);
v___x_5773_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5765_, v___x_5772_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_);
if (lean_obj_tag(v___x_5773_) == 0)
{
lean_object* v_a_5774_; lean_object* v___x_5776_; uint8_t v_isShared_5777_; uint8_t v_isSharedCheck_5790_; 
v_a_5774_ = lean_ctor_get(v___x_5773_, 0);
v_isSharedCheck_5790_ = !lean_is_exclusive(v___x_5773_);
if (v_isSharedCheck_5790_ == 0)
{
v___x_5776_ = v___x_5773_;
v_isShared_5777_ = v_isSharedCheck_5790_;
goto v_resetjp_5775_;
}
else
{
lean_inc(v_a_5774_);
lean_dec(v___x_5773_);
v___x_5776_ = lean_box(0);
v_isShared_5777_ = v_isSharedCheck_5790_;
goto v_resetjp_5775_;
}
v_resetjp_5775_:
{
lean_object* v_fst_5778_; lean_object* v_snd_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5789_; 
v_fst_5778_ = lean_ctor_get(v_a_5774_, 0);
v_snd_5779_ = lean_ctor_get(v_a_5774_, 1);
v_isSharedCheck_5789_ = !lean_is_exclusive(v_a_5774_);
if (v_isSharedCheck_5789_ == 0)
{
v___x_5781_ = v_a_5774_;
v_isShared_5782_ = v_isSharedCheck_5789_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_snd_5779_);
lean_inc(v_fst_5778_);
lean_dec(v_a_5774_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5789_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
lean_object* v___x_5784_; 
if (v_isShared_5782_ == 0)
{
v___x_5784_ = v___x_5781_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_fst_5778_);
lean_ctor_set(v_reuseFailAlloc_5788_, 1, v_snd_5779_);
v___x_5784_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
lean_object* v___x_5786_; 
if (v_isShared_5777_ == 0)
{
lean_ctor_set(v___x_5776_, 0, v___x_5784_);
v___x_5786_ = v___x_5776_;
goto v_reusejp_5785_;
}
else
{
lean_object* v_reuseFailAlloc_5787_; 
v_reuseFailAlloc_5787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5787_, 0, v___x_5784_);
v___x_5786_ = v_reuseFailAlloc_5787_;
goto v_reusejp_5785_;
}
v_reusejp_5785_:
{
return v___x_5786_;
}
}
}
}
}
else
{
return v___x_5773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5791_, lean_object* v_keys_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_){
_start:
{
lean_object* v_res_5798_; 
v_res_5798_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5791_, v_keys_5792_, v_a_5793_, v_a_5794_, v_a_5795_, v_a_5796_);
lean_dec(v_a_5796_);
lean_dec_ref(v_a_5795_);
lean_dec(v_a_5794_);
lean_dec_ref(v_a_5793_);
return v_res_5798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5799_, lean_object* v_t_5800_, lean_object* v_keys_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_){
_start:
{
lean_object* v___x_5807_; 
v___x_5807_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5800_, v_keys_5801_, v_a_5802_, v_a_5803_, v_a_5804_, v_a_5805_);
return v___x_5807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5808_, lean_object* v_t_5809_, lean_object* v_keys_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_){
_start:
{
lean_object* v_res_5816_; 
v_res_5816_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5808_, v_t_5809_, v_keys_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_);
lean_dec(v_a_5814_);
lean_dec_ref(v_a_5813_);
lean_dec(v_a_5812_);
lean_dec_ref(v_a_5811_);
return v_res_5816_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5817_, lean_object* v_as_5818_, lean_object* v_as_x27_5819_, lean_object* v_b_5820_, lean_object* v_a_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_){
_start:
{
lean_object* v___x_5827_; 
v___x_5827_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5819_, v_b_5820_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_);
return v___x_5827_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5828_, lean_object* v_as_5829_, lean_object* v_as_x27_5830_, lean_object* v_b_5831_, lean_object* v_a_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_){
_start:
{
lean_object* v_res_5838_; 
v_res_5838_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5828_, v_as_5829_, v_as_x27_5830_, v_b_5831_, v_a_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_);
lean_dec(v___y_5836_);
lean_dec_ref(v___y_5835_);
lean_dec(v___y_5834_);
lean_dec_ref(v___y_5833_);
lean_dec(v_as_5829_);
return v_res_5838_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5840_; lean_object* v___x_5841_; 
v___x_5840_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5841_ = l_Lean_stringToMessageData(v___x_5840_);
return v___x_5841_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5843_; lean_object* v___x_5844_; 
v___x_5843_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5844_ = l_Lean_stringToMessageData(v___x_5843_);
return v___x_5844_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5846_; lean_object* v___x_5847_; 
v___x_5846_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5847_ = l_Lean_stringToMessageData(v___x_5846_);
return v___x_5847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5848_, lean_object* v_inst_5849_, lean_object* v_inst_5850_, lean_object* v_inst_5851_, lean_object* v_f_5852_){
_start:
{
lean_object* v_module_5853_; lean_object* v_const_5854_; lean_object* v_exception_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; 
v_module_5853_ = lean_ctor_get(v_f_5852_, 0);
lean_inc(v_module_5853_);
v_const_5854_ = lean_ctor_get(v_f_5852_, 1);
lean_inc(v_const_5854_);
v_exception_5855_ = lean_ctor_get(v_f_5852_, 2);
lean_inc_ref(v_exception_5855_);
lean_dec_ref(v_f_5852_);
v___x_5856_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5857_ = l_Lean_MessageData_ofName(v_const_5854_);
v___x_5858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5856_);
lean_ctor_set(v___x_5858_, 1, v___x_5857_);
v___x_5859_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5860_, 0, v___x_5858_);
lean_ctor_set(v___x_5860_, 1, v___x_5859_);
v___x_5861_ = l_Lean_MessageData_ofName(v_module_5853_);
v___x_5862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5862_, 0, v___x_5860_);
lean_ctor_set(v___x_5862_, 1, v___x_5861_);
v___x_5863_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5862_);
lean_ctor_set(v___x_5864_, 1, v___x_5863_);
v___x_5865_ = l_Lean_Exception_toMessageData(v_exception_5855_);
v___x_5866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5866_, 0, v___x_5864_);
lean_ctor_set(v___x_5866_, 1, v___x_5865_);
v___x_5867_ = l_Lean_logError___redArg(v_inst_5848_, v_inst_5849_, v_inst_5850_, v_inst_5851_, v___x_5866_);
return v___x_5867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5868_, lean_object* v_inst_5869_, lean_object* v_inst_5870_, lean_object* v_inst_5871_, lean_object* v_inst_5872_, lean_object* v_f_5873_){
_start:
{
lean_object* v___x_5874_; 
v___x_5874_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5869_, v_inst_5870_, v_inst_5871_, v_inst_5872_, v_f_5873_);
return v___x_5874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_toApplicative_5875_, lean_object* v_tasks_5876_, lean_object* v_t_5877_){
_start:
{
lean_object* v_toPure_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; 
v_toPure_5878_ = lean_ctor_get(v_toApplicative_5875_, 1);
lean_inc(v_toPure_5878_);
lean_dec_ref(v_toApplicative_5875_);
v___x_5879_ = lean_array_push(v_tasks_5876_, v_t_5877_);
v___x_5880_ = lean_apply_2(v_toPure_5878_, lean_box(0), v___x_5879_);
return v___x_5880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5881_, lean_object* v_inst_5882_, lean_object* v_cctx_5883_, lean_object* v_env_5884_, lean_object* v_act_5885_, lean_object* v_constantsPerTask_5886_, lean_object* v_n_5887_, lean_object* v_ngen_5888_, lean_object* v_tasks_5889_, lean_object* v_start_5890_, lean_object* v_cnt_5891_, lean_object* v_idx_5892_){
_start:
{
lean_object* v___x_5893_; lean_object* v_moduleData_5894_; lean_object* v___x_5895_; uint8_t v___x_5896_; 
v___x_5893_ = l_Lean_Environment_header(v_env_5884_);
v_moduleData_5894_ = lean_ctor_get(v___x_5893_, 6);
lean_inc_ref(v_moduleData_5894_);
lean_dec_ref(v___x_5893_);
v___x_5895_ = lean_array_get_size(v_moduleData_5894_);
v___x_5896_ = lean_nat_dec_lt(v_idx_5892_, v___x_5895_);
if (v___x_5896_ == 0)
{
uint8_t v___x_5897_; 
lean_dec_ref(v_moduleData_5894_);
lean_dec(v_idx_5892_);
lean_dec(v_cnt_5891_);
lean_dec(v_constantsPerTask_5886_);
v___x_5897_ = lean_nat_dec_lt(v_start_5890_, v_n_5887_);
if (v___x_5897_ == 0)
{
lean_object* v_toApplicative_5898_; lean_object* v_toPure_5899_; lean_object* v___x_5900_; 
lean_dec(v_start_5890_);
lean_dec_ref(v_ngen_5888_);
lean_dec(v_n_5887_);
lean_dec_ref(v_act_5885_);
lean_dec_ref(v_env_5884_);
lean_dec_ref(v_cctx_5883_);
lean_dec(v_inst_5882_);
v_toApplicative_5898_ = lean_ctor_get(v_inst_5881_, 0);
lean_inc_ref(v_toApplicative_5898_);
lean_dec_ref(v_inst_5881_);
v_toPure_5899_ = lean_ctor_get(v_toApplicative_5898_, 1);
lean_inc(v_toPure_5899_);
lean_dec_ref(v_toApplicative_5898_);
v___x_5900_ = lean_apply_2(v_toPure_5899_, lean_box(0), v_tasks_5889_);
return v___x_5900_;
}
else
{
lean_object* v_namePrefix_5901_; lean_object* v_idx_5902_; lean_object* v___x_5904_; uint8_t v_isShared_5905_; uint8_t v_isSharedCheck_5919_; 
v_namePrefix_5901_ = lean_ctor_get(v_ngen_5888_, 0);
v_idx_5902_ = lean_ctor_get(v_ngen_5888_, 1);
v_isSharedCheck_5919_ = !lean_is_exclusive(v_ngen_5888_);
if (v_isSharedCheck_5919_ == 0)
{
v___x_5904_ = v_ngen_5888_;
v_isShared_5905_ = v_isSharedCheck_5919_;
goto v_resetjp_5903_;
}
else
{
lean_inc(v_idx_5902_);
lean_inc(v_namePrefix_5901_);
lean_dec(v_ngen_5888_);
v___x_5904_ = lean_box(0);
v_isShared_5905_ = v_isSharedCheck_5919_;
goto v_resetjp_5903_;
}
v_resetjp_5903_:
{
lean_object* v_toApplicative_5906_; lean_object* v_toBind_5907_; lean_object* v___f_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5912_; 
v_toApplicative_5906_ = lean_ctor_get(v_inst_5881_, 0);
lean_inc_ref(v_toApplicative_5906_);
v_toBind_5907_ = lean_ctor_get(v_inst_5881_, 1);
lean_inc(v_toBind_5907_);
lean_dec_ref(v_inst_5881_);
v___f_5908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5908_, 0, v_toApplicative_5906_);
lean_closure_set(v___f_5908_, 1, v_tasks_5889_);
v___x_5909_ = l_Lean_Name_num___override(v_namePrefix_5901_, v_idx_5902_);
v___x_5910_ = lean_unsigned_to_nat(1u);
if (v_isShared_5905_ == 0)
{
lean_ctor_set(v___x_5904_, 1, v___x_5910_);
lean_ctor_set(v___x_5904_, 0, v___x_5909_);
v___x_5912_ = v___x_5904_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5918_; 
v_reuseFailAlloc_5918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5918_, 0, v___x_5909_);
lean_ctor_set(v_reuseFailAlloc_5918_, 1, v___x_5910_);
v___x_5912_ = v_reuseFailAlloc_5918_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v___x_5913_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5913_, 0, lean_box(0));
lean_closure_set(v___x_5913_, 1, v_cctx_5883_);
lean_closure_set(v___x_5913_, 2, v___x_5912_);
lean_closure_set(v___x_5913_, 3, v_env_5884_);
lean_closure_set(v___x_5913_, 4, v_act_5885_);
lean_closure_set(v___x_5913_, 5, v_start_5890_);
lean_closure_set(v___x_5913_, 6, v_n_5887_);
v___x_5914_ = lean_unsigned_to_nat(0u);
v___x_5915_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5915_, 0, lean_box(0));
lean_closure_set(v___x_5915_, 1, v___x_5913_);
lean_closure_set(v___x_5915_, 2, v___x_5914_);
v___x_5916_ = lean_apply_2(v_inst_5882_, lean_box(0), v___x_5915_);
v___x_5917_ = lean_apply_4(v_toBind_5907_, lean_box(0), lean_box(0), v___x_5916_, v___f_5908_);
return v___x_5917_;
}
}
}
}
else
{
lean_object* v_mdata_5920_; lean_object* v_constants_5921_; lean_object* v___x_5922_; lean_object* v_cnt_5923_; uint8_t v___x_5924_; 
v_mdata_5920_ = lean_array_fget(v_moduleData_5894_, v_idx_5892_);
lean_dec_ref(v_moduleData_5894_);
v_constants_5921_ = lean_ctor_get(v_mdata_5920_, 2);
lean_inc_ref(v_constants_5921_);
lean_dec(v_mdata_5920_);
v___x_5922_ = lean_array_get_size(v_constants_5921_);
lean_dec_ref(v_constants_5921_);
v_cnt_5923_ = lean_nat_add(v_cnt_5891_, v___x_5922_);
lean_dec(v_cnt_5891_);
v___x_5924_ = lean_nat_dec_lt(v_constantsPerTask_5886_, v_cnt_5923_);
if (v___x_5924_ == 0)
{
lean_object* v___x_5925_; lean_object* v___x_5926_; 
v___x_5925_ = lean_unsigned_to_nat(1u);
v___x_5926_ = lean_nat_add(v_idx_5892_, v___x_5925_);
lean_dec(v_idx_5892_);
v_cnt_5891_ = v_cnt_5923_;
v_idx_5892_ = v___x_5926_;
goto _start;
}
else
{
lean_object* v_namePrefix_5928_; lean_object* v_idx_5929_; lean_object* v___x_5931_; uint8_t v_isShared_5932_; uint8_t v_isSharedCheck_5948_; 
lean_dec(v_cnt_5923_);
v_namePrefix_5928_ = lean_ctor_get(v_ngen_5888_, 0);
v_idx_5929_ = lean_ctor_get(v_ngen_5888_, 1);
v_isSharedCheck_5948_ = !lean_is_exclusive(v_ngen_5888_);
if (v_isSharedCheck_5948_ == 0)
{
v___x_5931_ = v_ngen_5888_;
v_isShared_5932_ = v_isSharedCheck_5948_;
goto v_resetjp_5930_;
}
else
{
lean_inc(v_idx_5929_);
lean_inc(v_namePrefix_5928_);
lean_dec(v_ngen_5888_);
v___x_5931_ = lean_box(0);
v_isShared_5932_ = v_isSharedCheck_5948_;
goto v_resetjp_5930_;
}
v_resetjp_5930_:
{
lean_object* v_toBind_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5937_; 
v_toBind_5933_ = lean_ctor_get(v_inst_5881_, 1);
lean_inc(v_toBind_5933_);
lean_inc(v_idx_5929_);
lean_inc(v_namePrefix_5928_);
v___x_5934_ = l_Lean_Name_num___override(v_namePrefix_5928_, v_idx_5929_);
v___x_5935_ = lean_unsigned_to_nat(1u);
if (v_isShared_5932_ == 0)
{
lean_ctor_set(v___x_5931_, 1, v___x_5935_);
lean_ctor_set(v___x_5931_, 0, v___x_5934_);
v___x_5937_ = v___x_5931_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5947_; 
v_reuseFailAlloc_5947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5947_, 0, v___x_5934_);
lean_ctor_set(v_reuseFailAlloc_5947_, 1, v___x_5935_);
v___x_5937_ = v_reuseFailAlloc_5947_;
goto v_reusejp_5936_;
}
v_reusejp_5936_:
{
lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___f_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; 
v___x_5938_ = lean_nat_add(v_idx_5929_, v___x_5935_);
lean_dec(v_idx_5929_);
v___x_5939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5939_, 0, v_namePrefix_5928_);
lean_ctor_set(v___x_5939_, 1, v___x_5938_);
v___x_5940_ = lean_nat_add(v_idx_5892_, v___x_5935_);
lean_dec(v_idx_5892_);
lean_inc(v___x_5940_);
lean_inc_ref(v_act_5885_);
lean_inc_ref(v_env_5884_);
lean_inc_ref(v_cctx_5883_);
lean_inc(v_inst_5882_);
v___f_5941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5941_, 0, v_tasks_5889_);
lean_closure_set(v___f_5941_, 1, v_inst_5881_);
lean_closure_set(v___f_5941_, 2, v_inst_5882_);
lean_closure_set(v___f_5941_, 3, v_cctx_5883_);
lean_closure_set(v___f_5941_, 4, v_env_5884_);
lean_closure_set(v___f_5941_, 5, v_act_5885_);
lean_closure_set(v___f_5941_, 6, v_constantsPerTask_5886_);
lean_closure_set(v___f_5941_, 7, v_n_5887_);
lean_closure_set(v___f_5941_, 8, v___x_5939_);
lean_closure_set(v___f_5941_, 9, v___x_5940_);
v___x_5942_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5942_, 0, lean_box(0));
lean_closure_set(v___x_5942_, 1, v_cctx_5883_);
lean_closure_set(v___x_5942_, 2, v___x_5937_);
lean_closure_set(v___x_5942_, 3, v_env_5884_);
lean_closure_set(v___x_5942_, 4, v_act_5885_);
lean_closure_set(v___x_5942_, 5, v_start_5890_);
lean_closure_set(v___x_5942_, 6, v___x_5940_);
v___x_5943_ = lean_unsigned_to_nat(0u);
v___x_5944_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5944_, 0, lean_box(0));
lean_closure_set(v___x_5944_, 1, v___x_5942_);
lean_closure_set(v___x_5944_, 2, v___x_5943_);
v___x_5945_ = lean_apply_2(v_inst_5882_, lean_box(0), v___x_5944_);
v___x_5946_ = lean_apply_4(v_toBind_5933_, lean_box(0), lean_box(0), v___x_5945_, v___f_5941_);
return v___x_5946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5949_, lean_object* v_inst_5950_, lean_object* v_inst_5951_, lean_object* v_cctx_5952_, lean_object* v_env_5953_, lean_object* v_act_5954_, lean_object* v_constantsPerTask_5955_, lean_object* v_n_5956_, lean_object* v___x_5957_, lean_object* v___x_5958_, lean_object* v_t_5959_){
_start:
{
lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; 
v___x_5960_ = lean_array_push(v_tasks_5949_, v_t_5959_);
v___x_5961_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5958_);
v___x_5962_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5950_, v_inst_5951_, v_cctx_5952_, v_env_5953_, v_act_5954_, v_constantsPerTask_5955_, v_n_5956_, v___x_5957_, v___x_5960_, v___x_5958_, v___x_5961_, v___x_5958_);
return v___x_5962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5963_, lean_object* v_00_u03b1_5964_, lean_object* v_inst_5965_, lean_object* v_inst_5966_, lean_object* v_cctx_5967_, lean_object* v_env_5968_, lean_object* v_act_5969_, lean_object* v_constantsPerTask_5970_, lean_object* v_n_5971_, lean_object* v_ngen_5972_, lean_object* v_tasks_5973_, lean_object* v_start_5974_, lean_object* v_cnt_5975_, lean_object* v_idx_5976_){
_start:
{
lean_object* v___x_5977_; 
v___x_5977_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5965_, v_inst_5966_, v_cctx_5967_, v_env_5968_, v_act_5969_, v_constantsPerTask_5970_, v_n_5971_, v_ngen_5972_, v_tasks_5973_, v_start_5974_, v_cnt_5975_, v_idx_5976_);
return v___x_5977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5978_, lean_object* v_h__1_5979_){
_start:
{
lean_object* v_fst_5980_; lean_object* v_snd_5981_; lean_object* v___x_5982_; 
v_fst_5980_ = lean_ctor_get(v_x_5978_, 0);
lean_inc(v_fst_5980_);
v_snd_5981_ = lean_ctor_get(v_x_5978_, 1);
lean_inc(v_snd_5981_);
lean_dec_ref(v_x_5978_);
v___x_5982_ = lean_apply_2(v_h__1_5979_, v_fst_5980_, v_snd_5981_);
return v___x_5982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5983_, lean_object* v_x_5984_, lean_object* v_h__1_5985_){
_start:
{
lean_object* v_fst_5986_; lean_object* v_snd_5987_; lean_object* v___x_5988_; 
v_fst_5986_ = lean_ctor_get(v_x_5984_, 0);
lean_inc(v_fst_5986_);
v_snd_5987_ = lean_ctor_get(v_x_5984_, 1);
lean_inc(v_snd_5987_);
lean_dec_ref(v_x_5984_);
v___x_5988_ = lean_apply_2(v_h__1_5985_, v_fst_5986_, v_snd_5987_);
return v___x_5988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5989_, lean_object* v_inst_5990_, lean_object* v_inst_5991_, lean_object* v_inst_5992_, lean_object* v_x_5993_, lean_object* v___y_5994_){
_start:
{
lean_object* v___x_5995_; 
v___x_5995_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5989_, v_inst_5990_, v_inst_5991_, v_inst_5992_, v___y_5994_);
return v___x_5995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5996_, lean_object* v_toPure_5997_, lean_object* v_____r_5998_){
_start:
{
lean_object* v_tree_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
v_tree_5999_ = lean_ctor_get(v_r_5996_, 0);
lean_inc_ref(v_tree_5999_);
lean_dec_ref(v_r_5996_);
v___x_6000_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5999_);
v___x_6001_ = lean_apply_2(v_toPure_5997_, lean_box(0), v___x_6000_);
return v___x_6001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_6002_, lean_object* v___x_6003_, lean_object* v_toPure_6004_, lean_object* v_toBind_6005_, lean_object* v_inst_6006_, lean_object* v___f_6007_, lean_object* v_tasks_6008_){
_start:
{
lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v_r_6014_; lean_object* v_errors_6015_; lean_object* v___f_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; uint8_t v___x_6019_; 
v___x_6009_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_6002_);
v___x_6010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6002_);
lean_ctor_set(v___x_6010_, 1, v___x_6009_);
v___x_6011_ = lean_mk_empty_array_with_capacity(v___x_6002_);
lean_inc_ref(v___x_6011_);
v___x_6012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6010_);
lean_ctor_set(v___x_6012_, 1, v___x_6011_);
v___x_6013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
lean_ctor_set(v___x_6013_, 1, v___x_6011_);
v_r_6014_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_6003_, v___x_6013_, v_tasks_6008_);
v_errors_6015_ = lean_ctor_get(v_r_6014_, 1);
lean_inc_ref(v_errors_6015_);
lean_inc(v_toPure_6004_);
v___f_6016_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_6016_, 0, v_r_6014_);
lean_closure_set(v___f_6016_, 1, v_toPure_6004_);
v___x_6017_ = lean_array_get_size(v_errors_6015_);
v___x_6018_ = lean_box(0);
v___x_6019_ = lean_nat_dec_lt(v___x_6002_, v___x_6017_);
lean_dec(v___x_6002_);
if (v___x_6019_ == 0)
{
lean_object* v___x_6020_; lean_object* v___x_6021_; 
lean_dec_ref(v_errors_6015_);
lean_dec(v___f_6007_);
lean_dec_ref(v_inst_6006_);
v___x_6020_ = lean_apply_2(v_toPure_6004_, lean_box(0), v___x_6018_);
v___x_6021_ = lean_apply_4(v_toBind_6005_, lean_box(0), lean_box(0), v___x_6020_, v___f_6016_);
return v___x_6021_;
}
else
{
uint8_t v___x_6022_; 
v___x_6022_ = lean_nat_dec_le(v___x_6017_, v___x_6017_);
if (v___x_6022_ == 0)
{
if (v___x_6019_ == 0)
{
lean_object* v___x_6023_; lean_object* v___x_6024_; 
lean_dec_ref(v_errors_6015_);
lean_dec(v___f_6007_);
lean_dec_ref(v_inst_6006_);
v___x_6023_ = lean_apply_2(v_toPure_6004_, lean_box(0), v___x_6018_);
v___x_6024_ = lean_apply_4(v_toBind_6005_, lean_box(0), lean_box(0), v___x_6023_, v___f_6016_);
return v___x_6024_;
}
else
{
size_t v___x_6025_; size_t v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; 
lean_dec(v_toPure_6004_);
v___x_6025_ = ((size_t)0ULL);
v___x_6026_ = lean_usize_of_nat(v___x_6017_);
v___x_6027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_6006_, v___f_6007_, v_errors_6015_, v___x_6025_, v___x_6026_, v___x_6018_);
v___x_6028_ = lean_apply_4(v_toBind_6005_, lean_box(0), lean_box(0), v___x_6027_, v___f_6016_);
return v___x_6028_;
}
}
else
{
size_t v___x_6029_; size_t v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; 
lean_dec(v_toPure_6004_);
v___x_6029_ = ((size_t)0ULL);
v___x_6030_ = lean_usize_of_nat(v___x_6017_);
v___x_6031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_6006_, v___f_6007_, v_errors_6015_, v___x_6029_, v___x_6030_, v___x_6018_);
v___x_6032_ = lean_apply_4(v_toBind_6005_, lean_box(0), lean_box(0), v___x_6031_, v___f_6016_);
return v___x_6032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_6035_, lean_object* v_inst_6036_, lean_object* v_inst_6037_, lean_object* v_inst_6038_, lean_object* v_inst_6039_, lean_object* v_cctx_6040_, lean_object* v_ngen_6041_, lean_object* v_env_6042_, lean_object* v_act_6043_, lean_object* v_constantsPerTask_6044_){
_start:
{
lean_object* v___x_6045_; lean_object* v_moduleData_6046_; lean_object* v_toApplicative_6047_; lean_object* v_toBind_6048_; lean_object* v_n_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v_toPure_6053_; lean_object* v___f_6054_; lean_object* v___x_6055_; lean_object* v___f_6056_; lean_object* v___x_6057_; 
v___x_6045_ = l_Lean_Environment_header(v_env_6042_);
v_moduleData_6046_ = lean_ctor_get(v___x_6045_, 6);
lean_inc_ref(v_moduleData_6046_);
lean_dec_ref(v___x_6045_);
v_toApplicative_6047_ = lean_ctor_get(v_inst_6035_, 0);
v_toBind_6048_ = lean_ctor_get(v_inst_6035_, 1);
lean_inc(v_toBind_6048_);
v_n_6049_ = lean_array_get_size(v_moduleData_6046_);
lean_dec_ref(v_moduleData_6046_);
v___x_6050_ = lean_unsigned_to_nat(0u);
v___x_6051_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref(v_inst_6035_);
v___x_6052_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_6035_, v_inst_6039_, v_cctx_6040_, v_env_6042_, v_act_6043_, v_constantsPerTask_6044_, v_n_6049_, v_ngen_6041_, v___x_6051_, v___x_6050_, v___x_6050_, v___x_6050_);
v_toPure_6053_ = lean_ctor_get(v_toApplicative_6047_, 1);
lean_inc(v_toPure_6053_);
lean_inc_ref(v_inst_6035_);
v___f_6054_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_6054_, 0, v_inst_6035_);
lean_closure_set(v___f_6054_, 1, v_inst_6036_);
lean_closure_set(v___f_6054_, 2, v_inst_6037_);
lean_closure_set(v___f_6054_, 3, v_inst_6038_);
v___x_6055_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
lean_inc(v_toBind_6048_);
v___f_6056_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_6056_, 0, v___x_6050_);
lean_closure_set(v___f_6056_, 1, v___x_6055_);
lean_closure_set(v___f_6056_, 2, v_toPure_6053_);
lean_closure_set(v___f_6056_, 3, v_toBind_6048_);
lean_closure_set(v___f_6056_, 4, v_inst_6035_);
lean_closure_set(v___f_6056_, 5, v___f_6054_);
v___x_6057_ = lean_apply_4(v_toBind_6048_, lean_box(0), lean_box(0), v___x_6052_, v___f_6056_);
return v___x_6057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_6058_, lean_object* v_00_u03b1_6059_, lean_object* v_inst_6060_, lean_object* v_inst_6061_, lean_object* v_inst_6062_, lean_object* v_inst_6063_, lean_object* v_inst_6064_, lean_object* v_cctx_6065_, lean_object* v_ngen_6066_, lean_object* v_env_6067_, lean_object* v_act_6068_, lean_object* v_constantsPerTask_6069_){
_start:
{
lean_object* v___x_6070_; 
v___x_6070_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_6060_, v_inst_6061_, v_inst_6062_, v_inst_6063_, v_inst_6064_, v_cctx_6065_, v_ngen_6066_, v_env_6067_, v_act_6068_, v_constantsPerTask_6069_);
return v___x_6070_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6071_ = lean_box(0);
v___x_6072_ = lean_unsigned_to_nat(16u);
v___x_6073_ = lean_mk_array(v___x_6072_, v___x_6071_);
return v___x_6073_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6074_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_6075_ = lean_unsigned_to_nat(0u);
v___x_6076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6075_);
lean_ctor_set(v___x_6076_, 1, v___x_6074_);
return v___x_6076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_6077_){
_start:
{
lean_object* v_fileName_6078_; lean_object* v_fileMap_6079_; lean_object* v_options_6080_; lean_object* v_maxRecDepth_6081_; lean_object* v_ref_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6097_; 
v_fileName_6078_ = lean_ctor_get(v_ctx_6077_, 0);
v_fileMap_6079_ = lean_ctor_get(v_ctx_6077_, 1);
v_options_6080_ = lean_ctor_get(v_ctx_6077_, 2);
v_maxRecDepth_6081_ = lean_ctor_get(v_ctx_6077_, 4);
v_ref_6082_ = lean_ctor_get(v_ctx_6077_, 5);
v_isSharedCheck_6097_ = !lean_is_exclusive(v_ctx_6077_);
if (v_isSharedCheck_6097_ == 0)
{
lean_object* v_unused_6098_; lean_object* v_unused_6099_; lean_object* v_unused_6100_; lean_object* v_unused_6101_; lean_object* v_unused_6102_; lean_object* v_unused_6103_; lean_object* v_unused_6104_; lean_object* v_unused_6105_; lean_object* v_unused_6106_; 
v_unused_6098_ = lean_ctor_get(v_ctx_6077_, 13);
lean_dec(v_unused_6098_);
v_unused_6099_ = lean_ctor_get(v_ctx_6077_, 12);
lean_dec(v_unused_6099_);
v_unused_6100_ = lean_ctor_get(v_ctx_6077_, 11);
lean_dec(v_unused_6100_);
v_unused_6101_ = lean_ctor_get(v_ctx_6077_, 10);
lean_dec(v_unused_6101_);
v_unused_6102_ = lean_ctor_get(v_ctx_6077_, 9);
lean_dec(v_unused_6102_);
v_unused_6103_ = lean_ctor_get(v_ctx_6077_, 8);
lean_dec(v_unused_6103_);
v_unused_6104_ = lean_ctor_get(v_ctx_6077_, 7);
lean_dec(v_unused_6104_);
v_unused_6105_ = lean_ctor_get(v_ctx_6077_, 6);
lean_dec(v_unused_6105_);
v_unused_6106_ = lean_ctor_get(v_ctx_6077_, 3);
lean_dec(v_unused_6106_);
v___x_6084_ = v_ctx_6077_;
v_isShared_6085_ = v_isSharedCheck_6097_;
goto v_resetjp_6083_;
}
else
{
lean_inc(v_ref_6082_);
lean_inc(v_maxRecDepth_6081_);
lean_inc(v_options_6080_);
lean_inc(v_fileMap_6079_);
lean_inc(v_fileName_6078_);
lean_dec(v_ctx_6077_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6097_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; uint8_t v___x_6090_; lean_object* v___x_6091_; uint8_t v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6095_; 
v___x_6086_ = lean_unsigned_to_nat(0u);
v___x_6087_ = lean_box(0);
v___x_6088_ = lean_box(0);
v___x_6089_ = l_Lean_firstFrontendMacroScope;
v___x_6090_ = l_Lean_getDiag(v_options_6080_);
v___x_6091_ = lean_box(0);
v___x_6092_ = 0;
v___x_6093_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
if (v_isShared_6085_ == 0)
{
lean_ctor_set(v___x_6084_, 13, v___x_6093_);
lean_ctor_set(v___x_6084_, 12, v___x_6091_);
lean_ctor_set(v___x_6084_, 11, v___x_6089_);
lean_ctor_set(v___x_6084_, 10, v___x_6087_);
lean_ctor_set(v___x_6084_, 9, v___x_6086_);
lean_ctor_set(v___x_6084_, 8, v___x_6086_);
lean_ctor_set(v___x_6084_, 7, v___x_6088_);
lean_ctor_set(v___x_6084_, 6, v___x_6087_);
lean_ctor_set(v___x_6084_, 3, v___x_6086_);
v___x_6095_ = v___x_6084_;
goto v_reusejp_6094_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v_fileName_6078_);
lean_ctor_set(v_reuseFailAlloc_6096_, 1, v_fileMap_6079_);
lean_ctor_set(v_reuseFailAlloc_6096_, 2, v_options_6080_);
lean_ctor_set(v_reuseFailAlloc_6096_, 3, v___x_6086_);
lean_ctor_set(v_reuseFailAlloc_6096_, 4, v_maxRecDepth_6081_);
lean_ctor_set(v_reuseFailAlloc_6096_, 5, v_ref_6082_);
lean_ctor_set(v_reuseFailAlloc_6096_, 6, v___x_6087_);
lean_ctor_set(v_reuseFailAlloc_6096_, 7, v___x_6088_);
lean_ctor_set(v_reuseFailAlloc_6096_, 8, v___x_6086_);
lean_ctor_set(v_reuseFailAlloc_6096_, 9, v___x_6086_);
lean_ctor_set(v_reuseFailAlloc_6096_, 10, v___x_6087_);
lean_ctor_set(v_reuseFailAlloc_6096_, 11, v___x_6089_);
lean_ctor_set(v_reuseFailAlloc_6096_, 12, v___x_6091_);
lean_ctor_set(v_reuseFailAlloc_6096_, 13, v___x_6093_);
v___x_6095_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6094_;
}
v_reusejp_6094_:
{
lean_ctor_set_uint8(v___x_6095_, sizeof(void*)*14, v___x_6090_);
lean_ctor_set_uint8(v___x_6095_, sizeof(void*)*14 + 1, v___x_6092_);
return v___x_6095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_6107_, lean_object* v_opts_6108_, lean_object* v_act_6109_, lean_object* v_decl_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; 
lean_inc(v___y_6114_);
lean_inc_ref(v___y_6113_);
lean_inc(v___y_6112_);
lean_inc_ref(v___y_6111_);
v___x_6116_ = lean_apply_4(v_act_6109_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
v___x_6117_ = l_Lean_profileitIOUnsafe___redArg(v_category_6107_, v_opts_6108_, v___x_6116_, v_decl_6110_);
return v___x_6117_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_6118_, lean_object* v_opts_6119_, lean_object* v_act_6120_, lean_object* v_decl_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_){
_start:
{
lean_object* v_res_6127_; 
v_res_6127_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6118_, v_opts_6119_, v_act_6120_, v_decl_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
lean_dec(v___y_6125_);
lean_dec_ref(v___y_6124_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
lean_dec_ref(v_opts_6119_);
lean_dec_ref(v_category_6118_);
return v_res_6127_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_6128_, lean_object* v_category_6129_, lean_object* v_opts_6130_, lean_object* v_act_6131_, lean_object* v_decl_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_){
_start:
{
lean_object* v___x_6138_; 
v___x_6138_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6129_, v_opts_6130_, v_act_6131_, v_decl_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_);
return v___x_6138_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6139_, lean_object* v_category_6140_, lean_object* v_opts_6141_, lean_object* v_act_6142_, lean_object* v_decl_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_){
_start:
{
lean_object* v_res_6149_; 
v_res_6149_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6139_, v_category_6140_, v_opts_6141_, v_act_6142_, v_decl_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
lean_dec_ref(v_opts_6141_);
lean_dec_ref(v_category_6140_);
return v_res_6149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6150_, lean_object* v_env_6151_, lean_object* v_act_6152_, lean_object* v_constantsPerTask_6153_, lean_object* v_n_6154_, lean_object* v_ngen_6155_, lean_object* v_tasks_6156_, lean_object* v_start_6157_, lean_object* v_cnt_6158_, lean_object* v_idx_6159_){
_start:
{
lean_object* v___x_6161_; lean_object* v_moduleData_6162_; lean_object* v___x_6163_; uint8_t v___x_6164_; 
v___x_6161_ = l_Lean_Environment_header(v_env_6151_);
v_moduleData_6162_ = lean_ctor_get(v___x_6161_, 6);
lean_inc_ref(v_moduleData_6162_);
lean_dec_ref(v___x_6161_);
v___x_6163_ = lean_array_get_size(v_moduleData_6162_);
v___x_6164_ = lean_nat_dec_lt(v_idx_6159_, v___x_6163_);
if (v___x_6164_ == 0)
{
uint8_t v___x_6165_; 
lean_dec_ref(v_moduleData_6162_);
lean_dec(v_idx_6159_);
lean_dec(v_cnt_6158_);
v___x_6165_ = lean_nat_dec_lt(v_start_6157_, v_n_6154_);
if (v___x_6165_ == 0)
{
lean_object* v___x_6166_; 
lean_dec(v_start_6157_);
lean_dec_ref(v_ngen_6155_);
lean_dec(v_n_6154_);
lean_dec_ref(v_act_6152_);
lean_dec_ref(v_env_6151_);
lean_dec_ref(v_cctx_6150_);
v___x_6166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6166_, 0, v_tasks_6156_);
return v___x_6166_;
}
else
{
lean_object* v_namePrefix_6167_; lean_object* v_idx_6168_; lean_object* v___x_6170_; uint8_t v_isShared_6171_; uint8_t v_isSharedCheck_6182_; 
v_namePrefix_6167_ = lean_ctor_get(v_ngen_6155_, 0);
v_idx_6168_ = lean_ctor_get(v_ngen_6155_, 1);
v_isSharedCheck_6182_ = !lean_is_exclusive(v_ngen_6155_);
if (v_isSharedCheck_6182_ == 0)
{
v___x_6170_ = v_ngen_6155_;
v_isShared_6171_ = v_isSharedCheck_6182_;
goto v_resetjp_6169_;
}
else
{
lean_inc(v_idx_6168_);
lean_inc(v_namePrefix_6167_);
lean_dec(v_ngen_6155_);
v___x_6170_ = lean_box(0);
v_isShared_6171_ = v_isSharedCheck_6182_;
goto v_resetjp_6169_;
}
v_resetjp_6169_:
{
lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6175_; 
v___x_6172_ = l_Lean_Name_num___override(v_namePrefix_6167_, v_idx_6168_);
v___x_6173_ = lean_unsigned_to_nat(1u);
if (v_isShared_6171_ == 0)
{
lean_ctor_set(v___x_6170_, 1, v___x_6173_);
lean_ctor_set(v___x_6170_, 0, v___x_6172_);
v___x_6175_ = v___x_6170_;
goto v_reusejp_6174_;
}
else
{
lean_object* v_reuseFailAlloc_6181_; 
v_reuseFailAlloc_6181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6181_, 0, v___x_6172_);
lean_ctor_set(v_reuseFailAlloc_6181_, 1, v___x_6173_);
v___x_6175_ = v_reuseFailAlloc_6181_;
goto v_reusejp_6174_;
}
v_reusejp_6174_:
{
lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; 
v___x_6176_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6176_, 0, lean_box(0));
lean_closure_set(v___x_6176_, 1, v_cctx_6150_);
lean_closure_set(v___x_6176_, 2, v___x_6175_);
lean_closure_set(v___x_6176_, 3, v_env_6151_);
lean_closure_set(v___x_6176_, 4, v_act_6152_);
lean_closure_set(v___x_6176_, 5, v_start_6157_);
lean_closure_set(v___x_6176_, 6, v_n_6154_);
v___x_6177_ = lean_unsigned_to_nat(0u);
v___x_6178_ = lean_io_as_task(v___x_6176_, v___x_6177_);
v___x_6179_ = lean_array_push(v_tasks_6156_, v___x_6178_);
v___x_6180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6180_, 0, v___x_6179_);
return v___x_6180_;
}
}
}
}
else
{
lean_object* v_mdata_6183_; lean_object* v_constants_6184_; lean_object* v___x_6185_; lean_object* v_cnt_6186_; uint8_t v___x_6187_; 
v_mdata_6183_ = lean_array_fget(v_moduleData_6162_, v_idx_6159_);
lean_dec_ref(v_moduleData_6162_);
v_constants_6184_ = lean_ctor_get(v_mdata_6183_, 2);
lean_inc_ref(v_constants_6184_);
lean_dec(v_mdata_6183_);
v___x_6185_ = lean_array_get_size(v_constants_6184_);
lean_dec_ref(v_constants_6184_);
v_cnt_6186_ = lean_nat_add(v_cnt_6158_, v___x_6185_);
lean_dec(v_cnt_6158_);
v___x_6187_ = lean_nat_dec_lt(v_constantsPerTask_6153_, v_cnt_6186_);
if (v___x_6187_ == 0)
{
lean_object* v___x_6188_; lean_object* v___x_6189_; 
v___x_6188_ = lean_unsigned_to_nat(1u);
v___x_6189_ = lean_nat_add(v_idx_6159_, v___x_6188_);
lean_dec(v_idx_6159_);
v_cnt_6158_ = v_cnt_6186_;
v_idx_6159_ = v___x_6189_;
goto _start;
}
else
{
lean_object* v_namePrefix_6191_; lean_object* v_idx_6192_; lean_object* v___x_6194_; uint8_t v_isShared_6195_; uint8_t v_isSharedCheck_6209_; 
lean_dec(v_cnt_6186_);
v_namePrefix_6191_ = lean_ctor_get(v_ngen_6155_, 0);
v_idx_6192_ = lean_ctor_get(v_ngen_6155_, 1);
v_isSharedCheck_6209_ = !lean_is_exclusive(v_ngen_6155_);
if (v_isSharedCheck_6209_ == 0)
{
v___x_6194_ = v_ngen_6155_;
v_isShared_6195_ = v_isSharedCheck_6209_;
goto v_resetjp_6193_;
}
else
{
lean_inc(v_idx_6192_);
lean_inc(v_namePrefix_6191_);
lean_dec(v_ngen_6155_);
v___x_6194_ = lean_box(0);
v_isShared_6195_ = v_isSharedCheck_6209_;
goto v_resetjp_6193_;
}
v_resetjp_6193_:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6199_; 
lean_inc(v_idx_6192_);
lean_inc(v_namePrefix_6191_);
v___x_6196_ = l_Lean_Name_num___override(v_namePrefix_6191_, v_idx_6192_);
v___x_6197_ = lean_unsigned_to_nat(1u);
if (v_isShared_6195_ == 0)
{
lean_ctor_set(v___x_6194_, 1, v___x_6197_);
lean_ctor_set(v___x_6194_, 0, v___x_6196_);
v___x_6199_ = v___x_6194_;
goto v_reusejp_6198_;
}
else
{
lean_object* v_reuseFailAlloc_6208_; 
v_reuseFailAlloc_6208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6208_, 0, v___x_6196_);
lean_ctor_set(v_reuseFailAlloc_6208_, 1, v___x_6197_);
v___x_6199_ = v_reuseFailAlloc_6208_;
goto v_reusejp_6198_;
}
v_reusejp_6198_:
{
lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; 
v___x_6200_ = lean_nat_add(v_idx_6159_, v___x_6197_);
lean_dec(v_idx_6159_);
lean_inc(v___x_6200_);
lean_inc_ref(v_act_6152_);
lean_inc_ref(v_env_6151_);
lean_inc_ref(v_cctx_6150_);
v___x_6201_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6201_, 0, lean_box(0));
lean_closure_set(v___x_6201_, 1, v_cctx_6150_);
lean_closure_set(v___x_6201_, 2, v___x_6199_);
lean_closure_set(v___x_6201_, 3, v_env_6151_);
lean_closure_set(v___x_6201_, 4, v_act_6152_);
lean_closure_set(v___x_6201_, 5, v_start_6157_);
lean_closure_set(v___x_6201_, 6, v___x_6200_);
v___x_6202_ = lean_unsigned_to_nat(0u);
v___x_6203_ = lean_io_as_task(v___x_6201_, v___x_6202_);
v___x_6204_ = lean_nat_add(v_idx_6192_, v___x_6197_);
lean_dec(v_idx_6192_);
v___x_6205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6205_, 0, v_namePrefix_6191_);
lean_ctor_set(v___x_6205_, 1, v___x_6204_);
v___x_6206_ = lean_array_push(v_tasks_6156_, v___x_6203_);
lean_inc(v___x_6200_);
v_ngen_6155_ = v___x_6205_;
v_tasks_6156_ = v___x_6206_;
v_start_6157_ = v___x_6200_;
v_cnt_6158_ = v___x_6202_;
v_idx_6159_ = v___x_6200_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6210_, lean_object* v_env_6211_, lean_object* v_act_6212_, lean_object* v_constantsPerTask_6213_, lean_object* v_n_6214_, lean_object* v_ngen_6215_, lean_object* v_tasks_6216_, lean_object* v_start_6217_, lean_object* v_cnt_6218_, lean_object* v_idx_6219_, lean_object* v___y_6220_){
_start:
{
lean_object* v_res_6221_; 
v_res_6221_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6210_, v_env_6211_, v_act_6212_, v_constantsPerTask_6213_, v_n_6214_, v_ngen_6215_, v_tasks_6216_, v_start_6217_, v_cnt_6218_, v_idx_6219_);
lean_dec(v_constantsPerTask_6213_);
return v_res_6221_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v___y_6230_, uint8_t v_suppressElabErrors_6231_, lean_object* v_x_6232_){
_start:
{
if (lean_obj_tag(v_x_6232_) == 1)
{
lean_object* v_pre_6233_; 
v_pre_6233_ = lean_ctor_get(v_x_6232_, 0);
switch(lean_obj_tag(v_pre_6233_))
{
case 1:
{
lean_object* v_pre_6234_; 
v_pre_6234_ = lean_ctor_get(v_pre_6233_, 0);
switch(lean_obj_tag(v_pre_6234_))
{
case 0:
{
lean_object* v_str_6235_; lean_object* v_str_6236_; lean_object* v___x_6237_; uint8_t v___x_6238_; 
v_str_6235_ = lean_ctor_get(v_x_6232_, 1);
v_str_6236_ = lean_ctor_get(v_pre_6233_, 1);
v___x_6237_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6238_ = lean_string_dec_eq(v_str_6236_, v___x_6237_);
if (v___x_6238_ == 0)
{
lean_object* v___x_6239_; uint8_t v___x_6240_; 
v___x_6239_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6240_ = lean_string_dec_eq(v_str_6236_, v___x_6239_);
if (v___x_6240_ == 0)
{
return v___y_6230_;
}
else
{
lean_object* v___x_6241_; uint8_t v___x_6242_; 
v___x_6241_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6242_ = lean_string_dec_eq(v_str_6235_, v___x_6241_);
if (v___x_6242_ == 0)
{
return v___y_6230_;
}
else
{
return v_suppressElabErrors_6231_;
}
}
}
else
{
lean_object* v___x_6243_; uint8_t v___x_6244_; 
v___x_6243_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6244_ = lean_string_dec_eq(v_str_6235_, v___x_6243_);
if (v___x_6244_ == 0)
{
return v___y_6230_;
}
else
{
return v_suppressElabErrors_6231_;
}
}
}
case 1:
{
lean_object* v_pre_6245_; 
v_pre_6245_ = lean_ctor_get(v_pre_6234_, 0);
if (lean_obj_tag(v_pre_6245_) == 0)
{
lean_object* v_str_6246_; lean_object* v_str_6247_; lean_object* v_str_6248_; lean_object* v___x_6249_; uint8_t v___x_6250_; 
v_str_6246_ = lean_ctor_get(v_x_6232_, 1);
v_str_6247_ = lean_ctor_get(v_pre_6233_, 1);
v_str_6248_ = lean_ctor_get(v_pre_6234_, 1);
v___x_6249_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6250_ = lean_string_dec_eq(v_str_6248_, v___x_6249_);
if (v___x_6250_ == 0)
{
return v___y_6230_;
}
else
{
lean_object* v___x_6251_; uint8_t v___x_6252_; 
v___x_6251_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6252_ = lean_string_dec_eq(v_str_6247_, v___x_6251_);
if (v___x_6252_ == 0)
{
return v___y_6230_;
}
else
{
lean_object* v___x_6253_; uint8_t v___x_6254_; 
v___x_6253_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6254_ = lean_string_dec_eq(v_str_6246_, v___x_6253_);
if (v___x_6254_ == 0)
{
return v___y_6230_;
}
else
{
return v_suppressElabErrors_6231_;
}
}
}
}
else
{
return v___y_6230_;
}
}
default: 
{
return v___y_6230_;
}
}
}
case 0:
{
lean_object* v_str_6255_; lean_object* v___x_6256_; uint8_t v___x_6257_; 
v_str_6255_ = lean_ctor_get(v_x_6232_, 1);
v___x_6256_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6257_ = lean_string_dec_eq(v_str_6255_, v___x_6256_);
if (v___x_6257_ == 0)
{
return v___y_6230_;
}
else
{
return v_suppressElabErrors_6231_;
}
}
default: 
{
return v___y_6230_;
}
}
}
else
{
return v___y_6230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v___y_6258_, lean_object* v_suppressElabErrors_6259_, lean_object* v_x_6260_){
_start:
{
uint8_t v___y_8412__boxed_6261_; uint8_t v_suppressElabErrors_boxed_6262_; uint8_t v_res_6263_; lean_object* v_r_6264_; 
v___y_8412__boxed_6261_ = lean_unbox(v___y_6258_);
v_suppressElabErrors_boxed_6262_ = lean_unbox(v_suppressElabErrors_6259_);
v_res_6263_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v___y_8412__boxed_6261_, v_suppressElabErrors_boxed_6262_, v_x_6260_);
lean_dec(v_x_6260_);
v_r_6264_ = lean_box(v_res_6263_);
return v_r_6264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6266_, lean_object* v_msgData_6267_, uint8_t v_severity_6268_, uint8_t v_isSilent_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_){
_start:
{
lean_object* v___y_6276_; lean_object* v___y_6277_; uint8_t v___y_6278_; lean_object* v___y_6279_; uint8_t v___y_6280_; lean_object* v___y_6281_; lean_object* v___y_6282_; lean_object* v___y_6283_; lean_object* v___y_6284_; lean_object* v___y_6312_; lean_object* v___y_6313_; lean_object* v___y_6314_; uint8_t v___y_6315_; lean_object* v___y_6316_; uint8_t v___y_6317_; uint8_t v___y_6318_; lean_object* v___y_6319_; lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___y_6339_; uint8_t v___y_6340_; uint8_t v___y_6341_; uint8_t v___y_6342_; lean_object* v___y_6343_; lean_object* v___y_6344_; lean_object* v___y_6348_; lean_object* v___y_6349_; lean_object* v___y_6350_; uint8_t v___y_6351_; lean_object* v___y_6352_; uint8_t v___y_6353_; uint8_t v___y_6354_; uint8_t v___x_6359_; lean_object* v___y_6361_; lean_object* v___y_6362_; lean_object* v___y_6363_; lean_object* v___y_6364_; uint8_t v___y_6365_; uint8_t v___y_6366_; uint8_t v___y_6367_; uint8_t v___y_6369_; uint8_t v___x_6384_; 
v___x_6359_ = 2;
v___x_6384_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6268_, v___x_6359_);
if (v___x_6384_ == 0)
{
v___y_6369_ = v___x_6384_;
goto v___jp_6368_;
}
else
{
uint8_t v___x_6385_; 
lean_inc_ref(v_msgData_6267_);
v___x_6385_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6267_);
v___y_6369_ = v___x_6385_;
goto v___jp_6368_;
}
v___jp_6275_:
{
lean_object* v___x_6285_; lean_object* v_currNamespace_6286_; lean_object* v_openDecls_6287_; lean_object* v_env_6288_; lean_object* v_nextMacroScope_6289_; lean_object* v_ngen_6290_; lean_object* v_auxDeclNGen_6291_; lean_object* v_traceState_6292_; lean_object* v_cache_6293_; lean_object* v_messages_6294_; lean_object* v_infoState_6295_; lean_object* v_snapshotTasks_6296_; lean_object* v___x_6298_; uint8_t v_isShared_6299_; uint8_t v_isSharedCheck_6310_; 
v___x_6285_ = lean_st_ref_take(v___y_6284_);
v_currNamespace_6286_ = lean_ctor_get(v___y_6283_, 6);
v_openDecls_6287_ = lean_ctor_get(v___y_6283_, 7);
v_env_6288_ = lean_ctor_get(v___x_6285_, 0);
v_nextMacroScope_6289_ = lean_ctor_get(v___x_6285_, 1);
v_ngen_6290_ = lean_ctor_get(v___x_6285_, 2);
v_auxDeclNGen_6291_ = lean_ctor_get(v___x_6285_, 3);
v_traceState_6292_ = lean_ctor_get(v___x_6285_, 4);
v_cache_6293_ = lean_ctor_get(v___x_6285_, 5);
v_messages_6294_ = lean_ctor_get(v___x_6285_, 6);
v_infoState_6295_ = lean_ctor_get(v___x_6285_, 7);
v_snapshotTasks_6296_ = lean_ctor_get(v___x_6285_, 8);
v_isSharedCheck_6310_ = !lean_is_exclusive(v___x_6285_);
if (v_isSharedCheck_6310_ == 0)
{
v___x_6298_ = v___x_6285_;
v_isShared_6299_ = v_isSharedCheck_6310_;
goto v_resetjp_6297_;
}
else
{
lean_inc(v_snapshotTasks_6296_);
lean_inc(v_infoState_6295_);
lean_inc(v_messages_6294_);
lean_inc(v_cache_6293_);
lean_inc(v_traceState_6292_);
lean_inc(v_auxDeclNGen_6291_);
lean_inc(v_ngen_6290_);
lean_inc(v_nextMacroScope_6289_);
lean_inc(v_env_6288_);
lean_dec(v___x_6285_);
v___x_6298_ = lean_box(0);
v_isShared_6299_ = v_isSharedCheck_6310_;
goto v_resetjp_6297_;
}
v_resetjp_6297_:
{
lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6305_; 
lean_inc(v_openDecls_6287_);
lean_inc(v_currNamespace_6286_);
v___x_6300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6300_, 0, v_currNamespace_6286_);
lean_ctor_set(v___x_6300_, 1, v_openDecls_6287_);
v___x_6301_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6301_, 0, v___x_6300_);
lean_ctor_set(v___x_6301_, 1, v___y_6281_);
lean_inc_ref(v___y_6276_);
v___x_6302_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6302_, 0, v___y_6276_);
lean_ctor_set(v___x_6302_, 1, v___y_6277_);
lean_ctor_set(v___x_6302_, 2, v___y_6282_);
lean_ctor_set(v___x_6302_, 3, v___y_6279_);
lean_ctor_set(v___x_6302_, 4, v___x_6301_);
lean_ctor_set_uint8(v___x_6302_, sizeof(void*)*5, v___y_6278_);
lean_ctor_set_uint8(v___x_6302_, sizeof(void*)*5 + 1, v___y_6280_);
lean_ctor_set_uint8(v___x_6302_, sizeof(void*)*5 + 2, v_isSilent_6269_);
v___x_6303_ = l_Lean_MessageLog_add(v___x_6302_, v_messages_6294_);
if (v_isShared_6299_ == 0)
{
lean_ctor_set(v___x_6298_, 6, v___x_6303_);
v___x_6305_ = v___x_6298_;
goto v_reusejp_6304_;
}
else
{
lean_object* v_reuseFailAlloc_6309_; 
v_reuseFailAlloc_6309_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_env_6288_);
lean_ctor_set(v_reuseFailAlloc_6309_, 1, v_nextMacroScope_6289_);
lean_ctor_set(v_reuseFailAlloc_6309_, 2, v_ngen_6290_);
lean_ctor_set(v_reuseFailAlloc_6309_, 3, v_auxDeclNGen_6291_);
lean_ctor_set(v_reuseFailAlloc_6309_, 4, v_traceState_6292_);
lean_ctor_set(v_reuseFailAlloc_6309_, 5, v_cache_6293_);
lean_ctor_set(v_reuseFailAlloc_6309_, 6, v___x_6303_);
lean_ctor_set(v_reuseFailAlloc_6309_, 7, v_infoState_6295_);
lean_ctor_set(v_reuseFailAlloc_6309_, 8, v_snapshotTasks_6296_);
v___x_6305_ = v_reuseFailAlloc_6309_;
goto v_reusejp_6304_;
}
v_reusejp_6304_:
{
lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; 
v___x_6306_ = lean_st_ref_set(v___y_6284_, v___x_6305_);
v___x_6307_ = lean_box(0);
v___x_6308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6308_, 0, v___x_6307_);
return v___x_6308_;
}
}
}
v___jp_6311_:
{
lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v_a_6322_; lean_object* v___x_6324_; uint8_t v_isShared_6325_; uint8_t v_isSharedCheck_6335_; 
v___x_6320_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6267_);
v___x_6321_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6320_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_);
v_a_6322_ = lean_ctor_get(v___x_6321_, 0);
v_isSharedCheck_6335_ = !lean_is_exclusive(v___x_6321_);
if (v_isSharedCheck_6335_ == 0)
{
v___x_6324_ = v___x_6321_;
v_isShared_6325_ = v_isSharedCheck_6335_;
goto v_resetjp_6323_;
}
else
{
lean_inc(v_a_6322_);
lean_dec(v___x_6321_);
v___x_6324_ = lean_box(0);
v_isShared_6325_ = v_isSharedCheck_6335_;
goto v_resetjp_6323_;
}
v_resetjp_6323_:
{
lean_object* v___x_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; lean_object* v___x_6329_; 
lean_inc_ref(v___y_6316_);
v___x_6326_ = l_Lean_FileMap_toPosition(v___y_6316_, v___y_6314_);
lean_dec(v___y_6314_);
lean_inc_ref(v___y_6316_);
v___x_6327_ = l_Lean_FileMap_toPosition(v___y_6316_, v___y_6319_);
lean_dec(v___y_6319_);
v___x_6328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6328_, 0, v___x_6327_);
v___x_6329_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6317_ == 0)
{
lean_del_object(v___x_6324_);
lean_dec_ref(v___y_6312_);
v___y_6276_ = v___y_6313_;
v___y_6277_ = v___x_6326_;
v___y_6278_ = v___y_6315_;
v___y_6279_ = v___x_6329_;
v___y_6280_ = v___y_6318_;
v___y_6281_ = v_a_6322_;
v___y_6282_ = v___x_6328_;
v___y_6283_ = v___y_6272_;
v___y_6284_ = v___y_6273_;
goto v___jp_6275_;
}
else
{
uint8_t v___x_6330_; 
lean_inc(v_a_6322_);
v___x_6330_ = l_Lean_MessageData_hasTag(v___y_6312_, v_a_6322_);
if (v___x_6330_ == 0)
{
lean_object* v___x_6331_; lean_object* v___x_6333_; 
lean_dec_ref(v___x_6328_);
lean_dec_ref(v___x_6326_);
lean_dec(v_a_6322_);
v___x_6331_ = lean_box(0);
if (v_isShared_6325_ == 0)
{
lean_ctor_set(v___x_6324_, 0, v___x_6331_);
v___x_6333_ = v___x_6324_;
goto v_reusejp_6332_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v___x_6331_);
v___x_6333_ = v_reuseFailAlloc_6334_;
goto v_reusejp_6332_;
}
v_reusejp_6332_:
{
return v___x_6333_;
}
}
else
{
lean_del_object(v___x_6324_);
v___y_6276_ = v___y_6313_;
v___y_6277_ = v___x_6326_;
v___y_6278_ = v___y_6315_;
v___y_6279_ = v___x_6329_;
v___y_6280_ = v___y_6318_;
v___y_6281_ = v_a_6322_;
v___y_6282_ = v___x_6328_;
v___y_6283_ = v___y_6272_;
v___y_6284_ = v___y_6273_;
goto v___jp_6275_;
}
}
}
}
v___jp_6336_:
{
lean_object* v___x_6345_; 
v___x_6345_ = l_Lean_Syntax_getTailPos_x3f(v___y_6343_, v___y_6340_);
lean_dec(v___y_6343_);
if (lean_obj_tag(v___x_6345_) == 0)
{
lean_inc(v___y_6344_);
v___y_6312_ = v___y_6337_;
v___y_6313_ = v___y_6338_;
v___y_6314_ = v___y_6344_;
v___y_6315_ = v___y_6340_;
v___y_6316_ = v___y_6339_;
v___y_6317_ = v___y_6341_;
v___y_6318_ = v___y_6342_;
v___y_6319_ = v___y_6344_;
goto v___jp_6311_;
}
else
{
lean_object* v_val_6346_; 
v_val_6346_ = lean_ctor_get(v___x_6345_, 0);
lean_inc(v_val_6346_);
lean_dec_ref(v___x_6345_);
v___y_6312_ = v___y_6337_;
v___y_6313_ = v___y_6338_;
v___y_6314_ = v___y_6344_;
v___y_6315_ = v___y_6340_;
v___y_6316_ = v___y_6339_;
v___y_6317_ = v___y_6341_;
v___y_6318_ = v___y_6342_;
v___y_6319_ = v_val_6346_;
goto v___jp_6311_;
}
}
v___jp_6347_:
{
lean_object* v_ref_6355_; lean_object* v___x_6356_; 
v_ref_6355_ = l_Lean_replaceRef(v_ref_6266_, v___y_6350_);
v___x_6356_ = l_Lean_Syntax_getPos_x3f(v_ref_6355_, v___y_6351_);
if (lean_obj_tag(v___x_6356_) == 0)
{
lean_object* v___x_6357_; 
v___x_6357_ = lean_unsigned_to_nat(0u);
v___y_6337_ = v___y_6348_;
v___y_6338_ = v___y_6349_;
v___y_6339_ = v___y_6352_;
v___y_6340_ = v___y_6351_;
v___y_6341_ = v___y_6353_;
v___y_6342_ = v___y_6354_;
v___y_6343_ = v_ref_6355_;
v___y_6344_ = v___x_6357_;
goto v___jp_6336_;
}
else
{
lean_object* v_val_6358_; 
v_val_6358_ = lean_ctor_get(v___x_6356_, 0);
lean_inc(v_val_6358_);
lean_dec_ref(v___x_6356_);
v___y_6337_ = v___y_6348_;
v___y_6338_ = v___y_6349_;
v___y_6339_ = v___y_6352_;
v___y_6340_ = v___y_6351_;
v___y_6341_ = v___y_6353_;
v___y_6342_ = v___y_6354_;
v___y_6343_ = v_ref_6355_;
v___y_6344_ = v_val_6358_;
goto v___jp_6336_;
}
}
v___jp_6360_:
{
if (v___y_6367_ == 0)
{
v___y_6348_ = v___y_6361_;
v___y_6349_ = v___y_6362_;
v___y_6350_ = v___y_6363_;
v___y_6351_ = v___y_6366_;
v___y_6352_ = v___y_6364_;
v___y_6353_ = v___y_6365_;
v___y_6354_ = v_severity_6268_;
goto v___jp_6347_;
}
else
{
v___y_6348_ = v___y_6361_;
v___y_6349_ = v___y_6362_;
v___y_6350_ = v___y_6363_;
v___y_6351_ = v___y_6366_;
v___y_6352_ = v___y_6364_;
v___y_6353_ = v___y_6365_;
v___y_6354_ = v___x_6359_;
goto v___jp_6347_;
}
}
v___jp_6368_:
{
if (v___y_6369_ == 0)
{
lean_object* v_fileName_6370_; lean_object* v_fileMap_6371_; lean_object* v_options_6372_; lean_object* v_ref_6373_; uint8_t v_suppressElabErrors_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___f_6377_; uint8_t v___x_6378_; uint8_t v___x_6379_; 
v_fileName_6370_ = lean_ctor_get(v___y_6272_, 0);
v_fileMap_6371_ = lean_ctor_get(v___y_6272_, 1);
v_options_6372_ = lean_ctor_get(v___y_6272_, 2);
v_ref_6373_ = lean_ctor_get(v___y_6272_, 5);
v_suppressElabErrors_6374_ = lean_ctor_get_uint8(v___y_6272_, sizeof(void*)*14 + 1);
v___x_6375_ = lean_box(v___y_6369_);
v___x_6376_ = lean_box(v_suppressElabErrors_6374_);
v___f_6377_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6377_, 0, v___x_6375_);
lean_closure_set(v___f_6377_, 1, v___x_6376_);
v___x_6378_ = 1;
v___x_6379_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6268_, v___x_6378_);
if (v___x_6379_ == 0)
{
v___y_6361_ = v___f_6377_;
v___y_6362_ = v_fileName_6370_;
v___y_6363_ = v_ref_6373_;
v___y_6364_ = v_fileMap_6371_;
v___y_6365_ = v_suppressElabErrors_6374_;
v___y_6366_ = v___y_6369_;
v___y_6367_ = v___x_6379_;
goto v___jp_6360_;
}
else
{
lean_object* v___x_6380_; uint8_t v___x_6381_; 
v___x_6380_ = l_Lean_warningAsError;
v___x_6381_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6372_, v___x_6380_);
v___y_6361_ = v___f_6377_;
v___y_6362_ = v_fileName_6370_;
v___y_6363_ = v_ref_6373_;
v___y_6364_ = v_fileMap_6371_;
v___y_6365_ = v_suppressElabErrors_6374_;
v___y_6366_ = v___y_6369_;
v___y_6367_ = v___x_6381_;
goto v___jp_6360_;
}
}
else
{
lean_object* v___x_6382_; lean_object* v___x_6383_; 
lean_dec_ref(v_msgData_6267_);
v___x_6382_ = lean_box(0);
v___x_6383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6383_, 0, v___x_6382_);
return v___x_6383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6386_, lean_object* v_msgData_6387_, lean_object* v_severity_6388_, lean_object* v_isSilent_6389_, lean_object* v___y_6390_, lean_object* v___y_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_, lean_object* v___y_6394_){
_start:
{
uint8_t v_severity_boxed_6395_; uint8_t v_isSilent_boxed_6396_; lean_object* v_res_6397_; 
v_severity_boxed_6395_ = lean_unbox(v_severity_6388_);
v_isSilent_boxed_6396_ = lean_unbox(v_isSilent_6389_);
v_res_6397_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6386_, v_msgData_6387_, v_severity_boxed_6395_, v_isSilent_boxed_6396_, v___y_6390_, v___y_6391_, v___y_6392_, v___y_6393_);
lean_dec(v___y_6393_);
lean_dec_ref(v___y_6392_);
lean_dec(v___y_6391_);
lean_dec_ref(v___y_6390_);
lean_dec(v_ref_6386_);
return v_res_6397_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6398_, uint8_t v_severity_6399_, uint8_t v_isSilent_6400_, lean_object* v___y_6401_, lean_object* v___y_6402_, lean_object* v___y_6403_, lean_object* v___y_6404_){
_start:
{
lean_object* v_ref_6406_; lean_object* v___x_6407_; 
v_ref_6406_ = lean_ctor_get(v___y_6403_, 5);
v___x_6407_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6406_, v_msgData_6398_, v_severity_6399_, v_isSilent_6400_, v___y_6401_, v___y_6402_, v___y_6403_, v___y_6404_);
return v___x_6407_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6408_, lean_object* v_severity_6409_, lean_object* v_isSilent_6410_, lean_object* v___y_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_){
_start:
{
uint8_t v_severity_boxed_6416_; uint8_t v_isSilent_boxed_6417_; lean_object* v_res_6418_; 
v_severity_boxed_6416_ = lean_unbox(v_severity_6409_);
v_isSilent_boxed_6417_ = lean_unbox(v_isSilent_6410_);
v_res_6418_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6408_, v_severity_boxed_6416_, v_isSilent_boxed_6417_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
lean_dec(v___y_6414_);
lean_dec_ref(v___y_6413_);
lean_dec(v___y_6412_);
lean_dec_ref(v___y_6411_);
return v_res_6418_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6419_, lean_object* v___y_6420_, lean_object* v___y_6421_, lean_object* v___y_6422_, lean_object* v___y_6423_){
_start:
{
uint8_t v___x_6425_; uint8_t v___x_6426_; lean_object* v___x_6427_; 
v___x_6425_ = 2;
v___x_6426_ = 0;
v___x_6427_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6419_, v___x_6425_, v___x_6426_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_);
return v___x_6427_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_, lean_object* v___y_6432_, lean_object* v___y_6433_){
_start:
{
lean_object* v_res_6434_; 
v_res_6434_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6428_, v___y_6429_, v___y_6430_, v___y_6431_, v___y_6432_);
lean_dec(v___y_6432_);
lean_dec_ref(v___y_6431_);
lean_dec(v___y_6430_);
lean_dec_ref(v___y_6429_);
return v_res_6434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_, lean_object* v___y_6439_){
_start:
{
lean_object* v_module_6441_; lean_object* v_const_6442_; lean_object* v_exception_6443_; lean_object* v___x_6444_; lean_object* v___x_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; lean_object* v___x_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; 
v_module_6441_ = lean_ctor_get(v_f_6435_, 0);
lean_inc(v_module_6441_);
v_const_6442_ = lean_ctor_get(v_f_6435_, 1);
lean_inc(v_const_6442_);
v_exception_6443_ = lean_ctor_get(v_f_6435_, 2);
lean_inc_ref(v_exception_6443_);
lean_dec_ref(v_f_6435_);
v___x_6444_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6445_ = l_Lean_MessageData_ofName(v_const_6442_);
v___x_6446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6446_, 0, v___x_6444_);
lean_ctor_set(v___x_6446_, 1, v___x_6445_);
v___x_6447_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6448_, 0, v___x_6446_);
lean_ctor_set(v___x_6448_, 1, v___x_6447_);
v___x_6449_ = l_Lean_MessageData_ofName(v_module_6441_);
v___x_6450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6450_, 0, v___x_6448_);
lean_ctor_set(v___x_6450_, 1, v___x_6449_);
v___x_6451_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6452_, 0, v___x_6450_);
lean_ctor_set(v___x_6452_, 1, v___x_6451_);
v___x_6453_ = l_Lean_Exception_toMessageData(v_exception_6443_);
v___x_6454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6454_, 0, v___x_6452_);
lean_ctor_set(v___x_6454_, 1, v___x_6453_);
v___x_6455_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6454_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_);
return v___x_6455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_){
_start:
{
lean_object* v_res_6462_; 
v_res_6462_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_);
lean_dec(v___y_6460_);
lean_dec_ref(v___y_6459_);
lean_dec(v___y_6458_);
lean_dec_ref(v___y_6457_);
return v_res_6462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6463_, size_t v_i_6464_, size_t v_stop_6465_, lean_object* v_b_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_){
_start:
{
uint8_t v___x_6472_; 
v___x_6472_ = lean_usize_dec_eq(v_i_6464_, v_stop_6465_);
if (v___x_6472_ == 0)
{
lean_object* v___x_6473_; lean_object* v___x_6474_; 
v___x_6473_ = lean_array_uget_borrowed(v_as_6463_, v_i_6464_);
lean_inc(v___x_6473_);
v___x_6474_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6473_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_);
if (lean_obj_tag(v___x_6474_) == 0)
{
lean_object* v_a_6475_; size_t v___x_6476_; size_t v___x_6477_; 
v_a_6475_ = lean_ctor_get(v___x_6474_, 0);
lean_inc(v_a_6475_);
lean_dec_ref(v___x_6474_);
v___x_6476_ = ((size_t)1ULL);
v___x_6477_ = lean_usize_add(v_i_6464_, v___x_6476_);
v_i_6464_ = v___x_6477_;
v_b_6466_ = v_a_6475_;
goto _start;
}
else
{
return v___x_6474_;
}
}
else
{
lean_object* v___x_6479_; 
v___x_6479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6479_, 0, v_b_6466_);
return v___x_6479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6480_, lean_object* v_i_6481_, lean_object* v_stop_6482_, lean_object* v_b_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_){
_start:
{
size_t v_i_boxed_6489_; size_t v_stop_boxed_6490_; lean_object* v_res_6491_; 
v_i_boxed_6489_ = lean_unbox_usize(v_i_6481_);
lean_dec(v_i_6481_);
v_stop_boxed_6490_ = lean_unbox_usize(v_stop_6482_);
lean_dec(v_stop_6482_);
v_res_6491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6480_, v_i_boxed_6489_, v_stop_boxed_6490_, v_b_6483_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_);
lean_dec(v___y_6487_);
lean_dec_ref(v___y_6486_);
lean_dec(v___y_6485_);
lean_dec_ref(v___y_6484_);
lean_dec_ref(v_as_6480_);
return v_res_6491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6492_, size_t v_i_6493_, size_t v_stop_6494_, lean_object* v_b_6495_){
_start:
{
uint8_t v___x_6496_; 
v___x_6496_ = lean_usize_dec_eq(v_i_6493_, v_stop_6494_);
if (v___x_6496_ == 0)
{
lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; size_t v___x_6500_; size_t v___x_6501_; 
v___x_6497_ = lean_array_uget_borrowed(v_as_6492_, v_i_6493_);
lean_inc(v___x_6497_);
v___x_6498_ = lean_task_get_own(v___x_6497_);
v___x_6499_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6495_, v___x_6498_);
v___x_6500_ = ((size_t)1ULL);
v___x_6501_ = lean_usize_add(v_i_6493_, v___x_6500_);
v_i_6493_ = v___x_6501_;
v_b_6495_ = v___x_6499_;
goto _start;
}
else
{
return v_b_6495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6503_, lean_object* v_i_6504_, lean_object* v_stop_6505_, lean_object* v_b_6506_){
_start:
{
size_t v_i_boxed_6507_; size_t v_stop_boxed_6508_; lean_object* v_res_6509_; 
v_i_boxed_6507_ = lean_unbox_usize(v_i_6504_);
lean_dec(v_i_6504_);
v_stop_boxed_6508_ = lean_unbox_usize(v_stop_6505_);
lean_dec(v_stop_6505_);
v_res_6509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6503_, v_i_boxed_6507_, v_stop_boxed_6508_, v_b_6506_);
lean_dec_ref(v_as_6503_);
return v_res_6509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6510_, lean_object* v_tasks_6511_){
_start:
{
lean_object* v___x_6512_; lean_object* v___x_6513_; uint8_t v___x_6514_; 
v___x_6512_ = lean_unsigned_to_nat(0u);
v___x_6513_ = lean_array_get_size(v_tasks_6511_);
v___x_6514_ = lean_nat_dec_lt(v___x_6512_, v___x_6513_);
if (v___x_6514_ == 0)
{
return v_z_6510_;
}
else
{
uint8_t v___x_6515_; 
v___x_6515_ = lean_nat_dec_le(v___x_6513_, v___x_6513_);
if (v___x_6515_ == 0)
{
if (v___x_6514_ == 0)
{
return v_z_6510_;
}
else
{
size_t v___x_6516_; size_t v___x_6517_; lean_object* v___x_6518_; 
v___x_6516_ = ((size_t)0ULL);
v___x_6517_ = lean_usize_of_nat(v___x_6513_);
v___x_6518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6511_, v___x_6516_, v___x_6517_, v_z_6510_);
return v___x_6518_;
}
}
else
{
size_t v___x_6519_; size_t v___x_6520_; lean_object* v___x_6521_; 
v___x_6519_ = ((size_t)0ULL);
v___x_6520_ = lean_usize_of_nat(v___x_6513_);
v___x_6521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6511_, v___x_6519_, v___x_6520_, v_z_6510_);
return v___x_6521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6522_, lean_object* v_tasks_6523_){
_start:
{
lean_object* v_res_6524_; 
v_res_6524_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6522_, v_tasks_6523_);
lean_dec_ref(v_tasks_6523_);
return v_res_6524_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; 
v___x_6525_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6526_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6527_, 0, v___x_6526_);
lean_ctor_set(v___x_6527_, 1, v___x_6525_);
return v___x_6527_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; 
v___x_6528_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6529_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6530_, 0, v___x_6529_);
lean_ctor_set(v___x_6530_, 1, v___x_6528_);
return v___x_6530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6531_, lean_object* v_ngen_6532_, lean_object* v_env_6533_, lean_object* v_act_6534_, lean_object* v_constantsPerTask_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_){
_start:
{
lean_object* v___x_6541_; lean_object* v_moduleData_6542_; lean_object* v_n_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v_a_6547_; lean_object* v___x_6549_; uint8_t v_isShared_6550_; uint8_t v_isSharedCheck_6589_; 
v___x_6541_ = l_Lean_Environment_header(v_env_6533_);
v_moduleData_6542_ = lean_ctor_get(v___x_6541_, 6);
lean_inc_ref(v_moduleData_6542_);
lean_dec_ref(v___x_6541_);
v_n_6543_ = lean_array_get_size(v_moduleData_6542_);
lean_dec_ref(v_moduleData_6542_);
v___x_6544_ = lean_unsigned_to_nat(0u);
v___x_6545_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6546_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6531_, v_env_6533_, v_act_6534_, v_constantsPerTask_6535_, v_n_6543_, v_ngen_6532_, v___x_6545_, v___x_6544_, v___x_6544_, v___x_6544_);
v_a_6547_ = lean_ctor_get(v___x_6546_, 0);
v_isSharedCheck_6589_ = !lean_is_exclusive(v___x_6546_);
if (v_isSharedCheck_6589_ == 0)
{
v___x_6549_ = v___x_6546_;
v_isShared_6550_ = v_isSharedCheck_6589_;
goto v_resetjp_6548_;
}
else
{
lean_inc(v_a_6547_);
lean_dec(v___x_6546_);
v___x_6549_ = lean_box(0);
v_isShared_6550_ = v_isSharedCheck_6589_;
goto v_resetjp_6548_;
}
v_resetjp_6548_:
{
lean_object* v___x_6551_; lean_object* v_r_6552_; lean_object* v_tree_6559_; lean_object* v_errors_6560_; lean_object* v___x_6561_; uint8_t v___x_6562_; 
v___x_6551_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6552_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6551_, v_a_6547_);
lean_dec(v_a_6547_);
v_tree_6559_ = lean_ctor_get(v_r_6552_, 0);
lean_inc_ref(v_tree_6559_);
v_errors_6560_ = lean_ctor_get(v_r_6552_, 1);
lean_inc_ref(v_errors_6560_);
v___x_6561_ = lean_array_get_size(v_errors_6560_);
v___x_6562_ = lean_nat_dec_lt(v___x_6544_, v___x_6561_);
if (v___x_6562_ == 0)
{
lean_object* v___x_6563_; lean_object* v___x_6564_; 
lean_dec_ref(v_errors_6560_);
lean_dec_ref(v_r_6552_);
lean_del_object(v___x_6549_);
v___x_6563_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6559_);
v___x_6564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6564_, 0, v___x_6563_);
return v___x_6564_;
}
else
{
lean_object* v___x_6565_; uint8_t v___x_6566_; 
lean_dec_ref(v_tree_6559_);
v___x_6565_ = lean_box(0);
v___x_6566_ = lean_nat_dec_le(v___x_6561_, v___x_6561_);
if (v___x_6566_ == 0)
{
if (v___x_6562_ == 0)
{
lean_dec_ref(v_errors_6560_);
goto v___jp_6553_;
}
else
{
size_t v___x_6567_; size_t v___x_6568_; lean_object* v___x_6569_; 
v___x_6567_ = ((size_t)0ULL);
v___x_6568_ = lean_usize_of_nat(v___x_6561_);
v___x_6569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6560_, v___x_6567_, v___x_6568_, v___x_6565_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_);
lean_dec_ref(v_errors_6560_);
if (lean_obj_tag(v___x_6569_) == 0)
{
lean_dec_ref(v___x_6569_);
goto v___jp_6553_;
}
else
{
lean_object* v_a_6570_; lean_object* v___x_6572_; uint8_t v_isShared_6573_; uint8_t v_isSharedCheck_6577_; 
lean_dec_ref(v_r_6552_);
lean_del_object(v___x_6549_);
v_a_6570_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6577_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6577_ == 0)
{
v___x_6572_ = v___x_6569_;
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
else
{
lean_inc(v_a_6570_);
lean_dec(v___x_6569_);
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
}
else
{
size_t v___x_6578_; size_t v___x_6579_; lean_object* v___x_6580_; 
v___x_6578_ = ((size_t)0ULL);
v___x_6579_ = lean_usize_of_nat(v___x_6561_);
v___x_6580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6560_, v___x_6578_, v___x_6579_, v___x_6565_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_);
lean_dec_ref(v_errors_6560_);
if (lean_obj_tag(v___x_6580_) == 0)
{
lean_dec_ref(v___x_6580_);
goto v___jp_6553_;
}
else
{
lean_object* v_a_6581_; lean_object* v___x_6583_; uint8_t v_isShared_6584_; uint8_t v_isSharedCheck_6588_; 
lean_dec_ref(v_r_6552_);
lean_del_object(v___x_6549_);
v_a_6581_ = lean_ctor_get(v___x_6580_, 0);
v_isSharedCheck_6588_ = !lean_is_exclusive(v___x_6580_);
if (v_isSharedCheck_6588_ == 0)
{
v___x_6583_ = v___x_6580_;
v_isShared_6584_ = v_isSharedCheck_6588_;
goto v_resetjp_6582_;
}
else
{
lean_inc(v_a_6581_);
lean_dec(v___x_6580_);
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
}
v___jp_6553_:
{
lean_object* v_tree_6554_; lean_object* v___x_6555_; lean_object* v___x_6557_; 
v_tree_6554_ = lean_ctor_get(v_r_6552_, 0);
lean_inc_ref(v_tree_6554_);
lean_dec_ref(v_r_6552_);
v___x_6555_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6554_);
if (v_isShared_6550_ == 0)
{
lean_ctor_set(v___x_6549_, 0, v___x_6555_);
v___x_6557_ = v___x_6549_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6558_; 
v_reuseFailAlloc_6558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6558_, 0, v___x_6555_);
v___x_6557_ = v_reuseFailAlloc_6558_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
return v___x_6557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6590_, lean_object* v_ngen_6591_, lean_object* v_env_6592_, lean_object* v_act_6593_, lean_object* v_constantsPerTask_6594_, lean_object* v___y_6595_, lean_object* v___y_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_){
_start:
{
lean_object* v_res_6600_; 
v_res_6600_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6590_, v_ngen_6591_, v_env_6592_, v_act_6593_, v_constantsPerTask_6594_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
lean_dec(v___y_6598_);
lean_dec_ref(v___y_6597_);
lean_dec(v___y_6596_);
lean_dec_ref(v___y_6595_);
lean_dec(v_constantsPerTask_6594_);
return v_res_6600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6601_, lean_object* v___x_6602_, lean_object* v_addEntry_6603_, lean_object* v_constantsPerTask_6604_, lean_object* v_droppedEntriesRef_6605_, lean_object* v_droppedKeys_6606_, lean_object* v___y_6607_, lean_object* v___y_6608_, lean_object* v___y_6609_, lean_object* v___y_6610_){
_start:
{
lean_object* v___x_6612_; lean_object* v_env_6613_; lean_object* v___x_6614_; lean_object* v___x_6615_; 
v___x_6612_ = lean_st_ref_get(v___y_6610_);
v_env_6613_ = lean_ctor_get(v___x_6612_, 0);
lean_inc_ref(v_env_6613_);
lean_dec(v___x_6612_);
lean_inc_ref(v_a_6601_);
v___x_6614_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6601_);
v___x_6615_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6614_, v___x_6602_, v_env_6613_, v_addEntry_6603_, v_constantsPerTask_6604_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
if (lean_obj_tag(v___x_6615_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6605_) == 1)
{
lean_object* v_a_6616_; lean_object* v_val_6617_; lean_object* v___x_6619_; uint8_t v_isShared_6620_; uint8_t v_isSharedCheck_6650_; 
v_a_6616_ = lean_ctor_get(v___x_6615_, 0);
lean_inc(v_a_6616_);
lean_dec_ref(v___x_6615_);
v_val_6617_ = lean_ctor_get(v_droppedEntriesRef_6605_, 0);
v_isSharedCheck_6650_ = !lean_is_exclusive(v_droppedEntriesRef_6605_);
if (v_isSharedCheck_6650_ == 0)
{
v___x_6619_ = v_droppedEntriesRef_6605_;
v_isShared_6620_ = v_isSharedCheck_6650_;
goto v_resetjp_6618_;
}
else
{
lean_inc(v_val_6617_);
lean_dec(v_droppedEntriesRef_6605_);
v___x_6619_ = lean_box(0);
v_isShared_6620_ = v_isSharedCheck_6650_;
goto v_resetjp_6618_;
}
v_resetjp_6618_:
{
lean_object* v___x_6621_; 
v___x_6621_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6616_, v_droppedKeys_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
if (lean_obj_tag(v___x_6621_) == 0)
{
lean_object* v_a_6622_; lean_object* v___x_6624_; uint8_t v_isShared_6625_; uint8_t v_isSharedCheck_6641_; 
v_a_6622_ = lean_ctor_get(v___x_6621_, 0);
v_isSharedCheck_6641_ = !lean_is_exclusive(v___x_6621_);
if (v_isSharedCheck_6641_ == 0)
{
v___x_6624_ = v___x_6621_;
v_isShared_6625_ = v_isSharedCheck_6641_;
goto v_resetjp_6623_;
}
else
{
lean_inc(v_a_6622_);
lean_dec(v___x_6621_);
v___x_6624_ = lean_box(0);
v_isShared_6625_ = v_isSharedCheck_6641_;
goto v_resetjp_6623_;
}
v_resetjp_6623_:
{
lean_object* v_fst_6626_; lean_object* v_snd_6627_; lean_object* v___x_6628_; lean_object* v___y_6630_; 
v_fst_6626_ = lean_ctor_get(v_a_6622_, 0);
lean_inc(v_fst_6626_);
v_snd_6627_ = lean_ctor_get(v_a_6622_, 1);
lean_inc(v_snd_6627_);
lean_dec(v_a_6622_);
v___x_6628_ = lean_st_ref_get(v_val_6617_);
if (lean_obj_tag(v___x_6628_) == 0)
{
lean_object* v___x_6639_; 
v___x_6639_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6630_ = v___x_6639_;
goto v___jp_6629_;
}
else
{
lean_object* v_val_6640_; 
v_val_6640_ = lean_ctor_get(v___x_6628_, 0);
lean_inc(v_val_6640_);
lean_dec_ref(v___x_6628_);
v___y_6630_ = v_val_6640_;
goto v___jp_6629_;
}
v___jp_6629_:
{
lean_object* v___x_6631_; lean_object* v___x_6633_; 
v___x_6631_ = l_Array_append___redArg(v___y_6630_, v_fst_6626_);
lean_dec(v_fst_6626_);
if (v_isShared_6620_ == 0)
{
lean_ctor_set(v___x_6619_, 0, v___x_6631_);
v___x_6633_ = v___x_6619_;
goto v_reusejp_6632_;
}
else
{
lean_object* v_reuseFailAlloc_6638_; 
v_reuseFailAlloc_6638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6638_, 0, v___x_6631_);
v___x_6633_ = v_reuseFailAlloc_6638_;
goto v_reusejp_6632_;
}
v_reusejp_6632_:
{
lean_object* v___x_6634_; lean_object* v___x_6636_; 
v___x_6634_ = lean_st_ref_set(v_val_6617_, v___x_6633_);
lean_dec(v_val_6617_);
if (v_isShared_6625_ == 0)
{
lean_ctor_set(v___x_6624_, 0, v_snd_6627_);
v___x_6636_ = v___x_6624_;
goto v_reusejp_6635_;
}
else
{
lean_object* v_reuseFailAlloc_6637_; 
v_reuseFailAlloc_6637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6637_, 0, v_snd_6627_);
v___x_6636_ = v_reuseFailAlloc_6637_;
goto v_reusejp_6635_;
}
v_reusejp_6635_:
{
return v___x_6636_;
}
}
}
}
}
else
{
lean_object* v_a_6642_; lean_object* v___x_6644_; uint8_t v_isShared_6645_; uint8_t v_isSharedCheck_6649_; 
lean_del_object(v___x_6619_);
lean_dec(v_val_6617_);
v_a_6642_ = lean_ctor_get(v___x_6621_, 0);
v_isSharedCheck_6649_ = !lean_is_exclusive(v___x_6621_);
if (v_isSharedCheck_6649_ == 0)
{
v___x_6644_ = v___x_6621_;
v_isShared_6645_ = v_isSharedCheck_6649_;
goto v_resetjp_6643_;
}
else
{
lean_inc(v_a_6642_);
lean_dec(v___x_6621_);
v___x_6644_ = lean_box(0);
v_isShared_6645_ = v_isSharedCheck_6649_;
goto v_resetjp_6643_;
}
v_resetjp_6643_:
{
lean_object* v___x_6647_; 
if (v_isShared_6645_ == 0)
{
v___x_6647_ = v___x_6644_;
goto v_reusejp_6646_;
}
else
{
lean_object* v_reuseFailAlloc_6648_; 
v_reuseFailAlloc_6648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6648_, 0, v_a_6642_);
v___x_6647_ = v_reuseFailAlloc_6648_;
goto v_reusejp_6646_;
}
v_reusejp_6646_:
{
return v___x_6647_;
}
}
}
}
}
else
{
lean_object* v_a_6651_; lean_object* v___x_6652_; 
lean_dec(v_droppedEntriesRef_6605_);
v_a_6651_ = lean_ctor_get(v___x_6615_, 0);
lean_inc(v_a_6651_);
lean_dec_ref(v___x_6615_);
v___x_6652_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6651_, v_droppedKeys_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
return v___x_6652_;
}
}
else
{
lean_dec(v_droppedKeys_6606_);
lean_dec(v_droppedEntriesRef_6605_);
return v___x_6615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6653_, lean_object* v___x_6654_, lean_object* v_addEntry_6655_, lean_object* v_constantsPerTask_6656_, lean_object* v_droppedEntriesRef_6657_, lean_object* v_droppedKeys_6658_, lean_object* v___y_6659_, lean_object* v___y_6660_, lean_object* v___y_6661_, lean_object* v___y_6662_, lean_object* v___y_6663_){
_start:
{
lean_object* v_res_6664_; 
v_res_6664_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6653_, v___x_6654_, v_addEntry_6655_, v_constantsPerTask_6656_, v_droppedEntriesRef_6657_, v_droppedKeys_6658_, v___y_6659_, v___y_6660_, v___y_6661_, v___y_6662_);
lean_dec(v___y_6662_);
lean_dec_ref(v___y_6661_);
lean_dec(v___y_6660_);
lean_dec_ref(v___y_6659_);
lean_dec(v_constantsPerTask_6656_);
lean_dec_ref(v_a_6653_);
return v_res_6664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ext_6666_, lean_object* v_addEntry_6667_, lean_object* v_droppedKeys_6668_, lean_object* v_constantsPerTask_6669_, lean_object* v_droppedEntriesRef_6670_, lean_object* v_ty_6671_, lean_object* v_a_6672_, lean_object* v_a_6673_, lean_object* v_a_6674_, lean_object* v_a_6675_){
_start:
{
lean_object* v___x_6677_; lean_object* v_ngen_6678_; lean_object* v_namePrefix_6679_; lean_object* v_idx_6680_; lean_object* v___x_6682_; uint8_t v_isShared_6683_; uint8_t v_isSharedCheck_6754_; 
v___x_6677_ = lean_st_ref_get(v_a_6675_);
v_ngen_6678_ = lean_ctor_get(v___x_6677_, 2);
lean_inc_ref(v_ngen_6678_);
lean_dec(v___x_6677_);
v_namePrefix_6679_ = lean_ctor_get(v_ngen_6678_, 0);
v_idx_6680_ = lean_ctor_get(v_ngen_6678_, 1);
v_isSharedCheck_6754_ = !lean_is_exclusive(v_ngen_6678_);
if (v_isSharedCheck_6754_ == 0)
{
v___x_6682_ = v_ngen_6678_;
v_isShared_6683_ = v_isSharedCheck_6754_;
goto v_resetjp_6681_;
}
else
{
lean_inc(v_idx_6680_);
lean_inc(v_namePrefix_6679_);
lean_dec(v_ngen_6678_);
v___x_6682_ = lean_box(0);
v_isShared_6683_ = v_isSharedCheck_6754_;
goto v_resetjp_6681_;
}
v_resetjp_6681_:
{
lean_object* v___x_6684_; lean_object* v_env_6685_; lean_object* v_nextMacroScope_6686_; lean_object* v_auxDeclNGen_6687_; lean_object* v_traceState_6688_; lean_object* v_cache_6689_; lean_object* v_messages_6690_; lean_object* v_infoState_6691_; lean_object* v_snapshotTasks_6692_; lean_object* v___x_6694_; uint8_t v_isShared_6695_; uint8_t v_isSharedCheck_6752_; 
v___x_6684_ = lean_st_ref_take(v_a_6675_);
v_env_6685_ = lean_ctor_get(v___x_6684_, 0);
v_nextMacroScope_6686_ = lean_ctor_get(v___x_6684_, 1);
v_auxDeclNGen_6687_ = lean_ctor_get(v___x_6684_, 3);
v_traceState_6688_ = lean_ctor_get(v___x_6684_, 4);
v_cache_6689_ = lean_ctor_get(v___x_6684_, 5);
v_messages_6690_ = lean_ctor_get(v___x_6684_, 6);
v_infoState_6691_ = lean_ctor_get(v___x_6684_, 7);
v_snapshotTasks_6692_ = lean_ctor_get(v___x_6684_, 8);
v_isSharedCheck_6752_ = !lean_is_exclusive(v___x_6684_);
if (v_isSharedCheck_6752_ == 0)
{
lean_object* v_unused_6753_; 
v_unused_6753_ = lean_ctor_get(v___x_6684_, 2);
lean_dec(v_unused_6753_);
v___x_6694_ = v___x_6684_;
v_isShared_6695_ = v_isSharedCheck_6752_;
goto v_resetjp_6693_;
}
else
{
lean_inc(v_snapshotTasks_6692_);
lean_inc(v_infoState_6691_);
lean_inc(v_messages_6690_);
lean_inc(v_cache_6689_);
lean_inc(v_traceState_6688_);
lean_inc(v_auxDeclNGen_6687_);
lean_inc(v_nextMacroScope_6686_);
lean_inc(v_env_6685_);
lean_dec(v___x_6684_);
v___x_6694_ = lean_box(0);
v_isShared_6695_ = v_isSharedCheck_6752_;
goto v_resetjp_6693_;
}
v_resetjp_6693_:
{
lean_object* v___x_6696_; lean_object* v___x_6697_; lean_object* v___x_6698_; lean_object* v___x_6700_; 
lean_inc(v_idx_6680_);
lean_inc(v_namePrefix_6679_);
v___x_6696_ = l_Lean_Name_num___override(v_namePrefix_6679_, v_idx_6680_);
v___x_6697_ = lean_unsigned_to_nat(1u);
v___x_6698_ = lean_nat_add(v_idx_6680_, v___x_6697_);
lean_dec(v_idx_6680_);
if (v_isShared_6683_ == 0)
{
lean_ctor_set(v___x_6682_, 1, v___x_6698_);
v___x_6700_ = v___x_6682_;
goto v_reusejp_6699_;
}
else
{
lean_object* v_reuseFailAlloc_6751_; 
v_reuseFailAlloc_6751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6751_, 0, v_namePrefix_6679_);
lean_ctor_set(v_reuseFailAlloc_6751_, 1, v___x_6698_);
v___x_6700_ = v_reuseFailAlloc_6751_;
goto v_reusejp_6699_;
}
v_reusejp_6699_:
{
lean_object* v___x_6702_; 
if (v_isShared_6695_ == 0)
{
lean_ctor_set(v___x_6694_, 2, v___x_6700_);
v___x_6702_ = v___x_6694_;
goto v_reusejp_6701_;
}
else
{
lean_object* v_reuseFailAlloc_6750_; 
v_reuseFailAlloc_6750_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_env_6685_);
lean_ctor_set(v_reuseFailAlloc_6750_, 1, v_nextMacroScope_6686_);
lean_ctor_set(v_reuseFailAlloc_6750_, 2, v___x_6700_);
lean_ctor_set(v_reuseFailAlloc_6750_, 3, v_auxDeclNGen_6687_);
lean_ctor_set(v_reuseFailAlloc_6750_, 4, v_traceState_6688_);
lean_ctor_set(v_reuseFailAlloc_6750_, 5, v_cache_6689_);
lean_ctor_set(v_reuseFailAlloc_6750_, 6, v_messages_6690_);
lean_ctor_set(v_reuseFailAlloc_6750_, 7, v_infoState_6691_);
lean_ctor_set(v_reuseFailAlloc_6750_, 8, v_snapshotTasks_6692_);
v___x_6702_ = v_reuseFailAlloc_6750_;
goto v_reusejp_6701_;
}
v_reusejp_6701_:
{
lean_object* v___x_6703_; lean_object* v___x_6704_; lean_object* v___x_6705_; lean_object* v___x_6706_; lean_object* v_env_6707_; lean_object* v_asyncMode_6708_; lean_object* v___x_6709_; lean_object* v___x_6710_; lean_object* v_a_6712_; lean_object* v___x_6734_; 
v___x_6703_ = lean_st_ref_set(v_a_6675_, v___x_6702_);
v___x_6704_ = lean_box(0);
v___x_6705_ = lean_st_mk_ref(v___x_6704_);
v___x_6706_ = lean_st_ref_get(v_a_6675_);
v_env_6707_ = lean_ctor_get(v___x_6706_, 0);
lean_inc_ref(v_env_6707_);
lean_dec(v___x_6706_);
v_asyncMode_6708_ = lean_ctor_get(v_ext_6666_, 2);
v___x_6709_ = lean_box(0);
v___x_6710_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_6705_, v_ext_6666_, v_env_6707_, v_asyncMode_6708_, v___x_6709_);
v___x_6734_ = lean_st_ref_get(v___x_6710_);
if (lean_obj_tag(v___x_6734_) == 0)
{
lean_object* v_options_6735_; lean_object* v___x_6736_; lean_object* v___f_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; 
v_options_6735_ = lean_ctor_get(v_a_6674_, 2);
v___x_6736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6736_, 0, v___x_6696_);
lean_ctor_set(v___x_6736_, 1, v___x_6697_);
lean_inc_ref(v_a_6674_);
v___f_6737_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6737_, 0, v_a_6674_);
lean_closure_set(v___f_6737_, 1, v___x_6736_);
lean_closure_set(v___f_6737_, 2, v_addEntry_6667_);
lean_closure_set(v___f_6737_, 3, v_constantsPerTask_6669_);
lean_closure_set(v___f_6737_, 4, v_droppedEntriesRef_6670_);
lean_closure_set(v___f_6737_, 5, v_droppedKeys_6668_);
v___x_6738_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6739_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6738_, v_options_6735_, v___f_6737_, v___x_6709_, v_a_6672_, v_a_6673_, v_a_6674_, v_a_6675_);
if (lean_obj_tag(v___x_6739_) == 0)
{
lean_object* v_a_6740_; 
v_a_6740_ = lean_ctor_get(v___x_6739_, 0);
lean_inc(v_a_6740_);
lean_dec_ref(v___x_6739_);
v_a_6712_ = v_a_6740_;
goto v___jp_6711_;
}
else
{
lean_object* v_a_6741_; lean_object* v___x_6743_; uint8_t v_isShared_6744_; uint8_t v_isSharedCheck_6748_; 
lean_dec(v___x_6710_);
lean_dec_ref(v_ty_6671_);
v_a_6741_ = lean_ctor_get(v___x_6739_, 0);
v_isSharedCheck_6748_ = !lean_is_exclusive(v___x_6739_);
if (v_isSharedCheck_6748_ == 0)
{
v___x_6743_ = v___x_6739_;
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
else
{
lean_inc(v_a_6741_);
lean_dec(v___x_6739_);
v___x_6743_ = lean_box(0);
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
v_resetjp_6742_:
{
lean_object* v___x_6746_; 
if (v_isShared_6744_ == 0)
{
v___x_6746_ = v___x_6743_;
goto v_reusejp_6745_;
}
else
{
lean_object* v_reuseFailAlloc_6747_; 
v_reuseFailAlloc_6747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6747_, 0, v_a_6741_);
v___x_6746_ = v_reuseFailAlloc_6747_;
goto v_reusejp_6745_;
}
v_reusejp_6745_:
{
return v___x_6746_;
}
}
}
}
else
{
lean_object* v_val_6749_; 
lean_dec(v___x_6696_);
lean_dec(v_droppedEntriesRef_6670_);
lean_dec(v_constantsPerTask_6669_);
lean_dec(v_droppedKeys_6668_);
lean_dec_ref(v_addEntry_6667_);
v_val_6749_ = lean_ctor_get(v___x_6734_, 0);
lean_inc(v_val_6749_);
lean_dec_ref(v___x_6734_);
v_a_6712_ = v_val_6749_;
goto v___jp_6711_;
}
v___jp_6711_:
{
lean_object* v___x_6713_; 
v___x_6713_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6712_, v_ty_6671_, v_a_6672_, v_a_6673_, v_a_6674_, v_a_6675_);
if (lean_obj_tag(v___x_6713_) == 0)
{
lean_object* v_a_6714_; lean_object* v___x_6716_; uint8_t v_isShared_6717_; uint8_t v_isSharedCheck_6725_; 
v_a_6714_ = lean_ctor_get(v___x_6713_, 0);
v_isSharedCheck_6725_ = !lean_is_exclusive(v___x_6713_);
if (v_isSharedCheck_6725_ == 0)
{
v___x_6716_ = v___x_6713_;
v_isShared_6717_ = v_isSharedCheck_6725_;
goto v_resetjp_6715_;
}
else
{
lean_inc(v_a_6714_);
lean_dec(v___x_6713_);
v___x_6716_ = lean_box(0);
v_isShared_6717_ = v_isSharedCheck_6725_;
goto v_resetjp_6715_;
}
v_resetjp_6715_:
{
lean_object* v_fst_6718_; lean_object* v_snd_6719_; lean_object* v___x_6720_; lean_object* v___x_6721_; lean_object* v___x_6723_; 
v_fst_6718_ = lean_ctor_get(v_a_6714_, 0);
lean_inc(v_fst_6718_);
v_snd_6719_ = lean_ctor_get(v_a_6714_, 1);
lean_inc(v_snd_6719_);
lean_dec(v_a_6714_);
v___x_6720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6720_, 0, v_snd_6719_);
v___x_6721_ = lean_st_ref_set(v___x_6710_, v___x_6720_);
lean_dec(v___x_6710_);
if (v_isShared_6717_ == 0)
{
lean_ctor_set(v___x_6716_, 0, v_fst_6718_);
v___x_6723_ = v___x_6716_;
goto v_reusejp_6722_;
}
else
{
lean_object* v_reuseFailAlloc_6724_; 
v_reuseFailAlloc_6724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_fst_6718_);
v___x_6723_ = v_reuseFailAlloc_6724_;
goto v_reusejp_6722_;
}
v_reusejp_6722_:
{
return v___x_6723_;
}
}
}
else
{
lean_object* v_a_6726_; lean_object* v___x_6728_; uint8_t v_isShared_6729_; uint8_t v_isSharedCheck_6733_; 
lean_dec(v___x_6710_);
v_a_6726_ = lean_ctor_get(v___x_6713_, 0);
v_isSharedCheck_6733_ = !lean_is_exclusive(v___x_6713_);
if (v_isSharedCheck_6733_ == 0)
{
v___x_6728_ = v___x_6713_;
v_isShared_6729_ = v_isSharedCheck_6733_;
goto v_resetjp_6727_;
}
else
{
lean_inc(v_a_6726_);
lean_dec(v___x_6713_);
v___x_6728_ = lean_box(0);
v_isShared_6729_ = v_isSharedCheck_6733_;
goto v_resetjp_6727_;
}
v_resetjp_6727_:
{
lean_object* v___x_6731_; 
if (v_isShared_6729_ == 0)
{
v___x_6731_ = v___x_6728_;
goto v_reusejp_6730_;
}
else
{
lean_object* v_reuseFailAlloc_6732_; 
v_reuseFailAlloc_6732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6732_, 0, v_a_6726_);
v___x_6731_ = v_reuseFailAlloc_6732_;
goto v_reusejp_6730_;
}
v_reusejp_6730_:
{
return v___x_6731_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ext_6755_, lean_object* v_addEntry_6756_, lean_object* v_droppedKeys_6757_, lean_object* v_constantsPerTask_6758_, lean_object* v_droppedEntriesRef_6759_, lean_object* v_ty_6760_, lean_object* v_a_6761_, lean_object* v_a_6762_, lean_object* v_a_6763_, lean_object* v_a_6764_, lean_object* v_a_6765_){
_start:
{
lean_object* v_res_6766_; 
v_res_6766_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ext_6755_, v_addEntry_6756_, v_droppedKeys_6757_, v_constantsPerTask_6758_, v_droppedEntriesRef_6759_, v_ty_6760_, v_a_6761_, v_a_6762_, v_a_6763_, v_a_6764_);
lean_dec(v_a_6764_);
lean_dec_ref(v_a_6763_);
lean_dec(v_a_6762_);
lean_dec_ref(v_a_6761_);
lean_dec_ref(v_ext_6755_);
return v_res_6766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6767_, lean_object* v_ext_6768_, lean_object* v_addEntry_6769_, lean_object* v_droppedKeys_6770_, lean_object* v_constantsPerTask_6771_, lean_object* v_droppedEntriesRef_6772_, lean_object* v_ty_6773_, lean_object* v_a_6774_, lean_object* v_a_6775_, lean_object* v_a_6776_, lean_object* v_a_6777_){
_start:
{
lean_object* v___x_6779_; 
v___x_6779_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ext_6768_, v_addEntry_6769_, v_droppedKeys_6770_, v_constantsPerTask_6771_, v_droppedEntriesRef_6772_, v_ty_6773_, v_a_6774_, v_a_6775_, v_a_6776_, v_a_6777_);
return v___x_6779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6780_, lean_object* v_ext_6781_, lean_object* v_addEntry_6782_, lean_object* v_droppedKeys_6783_, lean_object* v_constantsPerTask_6784_, lean_object* v_droppedEntriesRef_6785_, lean_object* v_ty_6786_, lean_object* v_a_6787_, lean_object* v_a_6788_, lean_object* v_a_6789_, lean_object* v_a_6790_, lean_object* v_a_6791_){
_start:
{
lean_object* v_res_6792_; 
v_res_6792_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6780_, v_ext_6781_, v_addEntry_6782_, v_droppedKeys_6783_, v_constantsPerTask_6784_, v_droppedEntriesRef_6785_, v_ty_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_);
lean_dec(v_a_6790_);
lean_dec_ref(v_a_6789_);
lean_dec(v_a_6788_);
lean_dec_ref(v_a_6787_);
lean_dec_ref(v_ext_6781_);
return v_res_6792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6793_, lean_object* v_cctx_6794_, lean_object* v_ngen_6795_, lean_object* v_env_6796_, lean_object* v_act_6797_, lean_object* v_constantsPerTask_6798_, lean_object* v___y_6799_, lean_object* v___y_6800_, lean_object* v___y_6801_, lean_object* v___y_6802_){
_start:
{
lean_object* v___x_6804_; 
v___x_6804_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6794_, v_ngen_6795_, v_env_6796_, v_act_6797_, v_constantsPerTask_6798_, v___y_6799_, v___y_6800_, v___y_6801_, v___y_6802_);
return v___x_6804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6805_, lean_object* v_cctx_6806_, lean_object* v_ngen_6807_, lean_object* v_env_6808_, lean_object* v_act_6809_, lean_object* v_constantsPerTask_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_, lean_object* v___y_6815_){
_start:
{
lean_object* v_res_6816_; 
v_res_6816_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6805_, v_cctx_6806_, v_ngen_6807_, v_env_6808_, v_act_6809_, v_constantsPerTask_6810_, v___y_6811_, v___y_6812_, v___y_6813_, v___y_6814_);
lean_dec(v___y_6814_);
lean_dec_ref(v___y_6813_);
lean_dec(v___y_6812_);
lean_dec_ref(v___y_6811_);
lean_dec(v_constantsPerTask_6810_);
return v_res_6816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6817_, lean_object* v_cctx_6818_, lean_object* v_env_6819_, lean_object* v_act_6820_, lean_object* v_constantsPerTask_6821_, lean_object* v_n_6822_, lean_object* v_ngen_6823_, lean_object* v_tasks_6824_, lean_object* v_start_6825_, lean_object* v_cnt_6826_, lean_object* v_idx_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_){
_start:
{
lean_object* v___x_6833_; 
v___x_6833_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6818_, v_env_6819_, v_act_6820_, v_constantsPerTask_6821_, v_n_6822_, v_ngen_6823_, v_tasks_6824_, v_start_6825_, v_cnt_6826_, v_idx_6827_);
return v___x_6833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6834_, lean_object* v_cctx_6835_, lean_object* v_env_6836_, lean_object* v_act_6837_, lean_object* v_constantsPerTask_6838_, lean_object* v_n_6839_, lean_object* v_ngen_6840_, lean_object* v_tasks_6841_, lean_object* v_start_6842_, lean_object* v_cnt_6843_, lean_object* v_idx_6844_, lean_object* v___y_6845_, lean_object* v___y_6846_, lean_object* v___y_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_){
_start:
{
lean_object* v_res_6850_; 
v_res_6850_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6834_, v_cctx_6835_, v_env_6836_, v_act_6837_, v_constantsPerTask_6838_, v_n_6839_, v_ngen_6840_, v_tasks_6841_, v_start_6842_, v_cnt_6843_, v_idx_6844_, v___y_6845_, v___y_6846_, v___y_6847_, v___y_6848_);
lean_dec(v___y_6848_);
lean_dec_ref(v___y_6847_);
lean_dec(v___y_6846_);
lean_dec_ref(v___y_6845_);
lean_dec(v_constantsPerTask_6838_);
return v_res_6850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6851_, lean_object* v_z_6852_, lean_object* v_tasks_6853_){
_start:
{
lean_object* v___x_6854_; 
v___x_6854_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6852_, v_tasks_6853_);
return v___x_6854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6855_, lean_object* v_z_6856_, lean_object* v_tasks_6857_){
_start:
{
lean_object* v_res_6858_; 
v_res_6858_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6855_, v_z_6856_, v_tasks_6857_);
lean_dec_ref(v_tasks_6857_);
return v_res_6858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6859_, lean_object* v_as_6860_, size_t v_i_6861_, size_t v_stop_6862_, lean_object* v_b_6863_){
_start:
{
lean_object* v___x_6864_; 
v___x_6864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6860_, v_i_6861_, v_stop_6862_, v_b_6863_);
return v___x_6864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6865_, lean_object* v_as_6866_, lean_object* v_i_6867_, lean_object* v_stop_6868_, lean_object* v_b_6869_){
_start:
{
size_t v_i_boxed_6870_; size_t v_stop_boxed_6871_; lean_object* v_res_6872_; 
v_i_boxed_6870_ = lean_unbox_usize(v_i_6867_);
lean_dec(v_i_6867_);
v_stop_boxed_6871_ = lean_unbox_usize(v_stop_6868_);
lean_dec(v_stop_6868_);
v_res_6872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6865_, v_as_6866_, v_i_boxed_6870_, v_stop_boxed_6871_, v_b_6869_);
lean_dec_ref(v_as_6866_);
return v_res_6872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6873_){
_start:
{
lean_object* v___x_6875_; lean_object* v_ngen_6876_; lean_object* v_namePrefix_6877_; lean_object* v_idx_6878_; lean_object* v___x_6880_; uint8_t v_isShared_6881_; uint8_t v_isSharedCheck_6908_; 
v___x_6875_ = lean_st_ref_get(v___y_6873_);
v_ngen_6876_ = lean_ctor_get(v___x_6875_, 2);
lean_inc_ref(v_ngen_6876_);
lean_dec(v___x_6875_);
v_namePrefix_6877_ = lean_ctor_get(v_ngen_6876_, 0);
v_idx_6878_ = lean_ctor_get(v_ngen_6876_, 1);
v_isSharedCheck_6908_ = !lean_is_exclusive(v_ngen_6876_);
if (v_isSharedCheck_6908_ == 0)
{
v___x_6880_ = v_ngen_6876_;
v_isShared_6881_ = v_isSharedCheck_6908_;
goto v_resetjp_6879_;
}
else
{
lean_inc(v_idx_6878_);
lean_inc(v_namePrefix_6877_);
lean_dec(v_ngen_6876_);
v___x_6880_ = lean_box(0);
v_isShared_6881_ = v_isSharedCheck_6908_;
goto v_resetjp_6879_;
}
v_resetjp_6879_:
{
lean_object* v___x_6882_; lean_object* v_env_6883_; lean_object* v_nextMacroScope_6884_; lean_object* v_auxDeclNGen_6885_; lean_object* v_traceState_6886_; lean_object* v_cache_6887_; lean_object* v_messages_6888_; lean_object* v_infoState_6889_; lean_object* v_snapshotTasks_6890_; lean_object* v___x_6892_; uint8_t v_isShared_6893_; uint8_t v_isSharedCheck_6906_; 
v___x_6882_ = lean_st_ref_take(v___y_6873_);
v_env_6883_ = lean_ctor_get(v___x_6882_, 0);
v_nextMacroScope_6884_ = lean_ctor_get(v___x_6882_, 1);
v_auxDeclNGen_6885_ = lean_ctor_get(v___x_6882_, 3);
v_traceState_6886_ = lean_ctor_get(v___x_6882_, 4);
v_cache_6887_ = lean_ctor_get(v___x_6882_, 5);
v_messages_6888_ = lean_ctor_get(v___x_6882_, 6);
v_infoState_6889_ = lean_ctor_get(v___x_6882_, 7);
v_snapshotTasks_6890_ = lean_ctor_get(v___x_6882_, 8);
v_isSharedCheck_6906_ = !lean_is_exclusive(v___x_6882_);
if (v_isSharedCheck_6906_ == 0)
{
lean_object* v_unused_6907_; 
v_unused_6907_ = lean_ctor_get(v___x_6882_, 2);
lean_dec(v_unused_6907_);
v___x_6892_ = v___x_6882_;
v_isShared_6893_ = v_isSharedCheck_6906_;
goto v_resetjp_6891_;
}
else
{
lean_inc(v_snapshotTasks_6890_);
lean_inc(v_infoState_6889_);
lean_inc(v_messages_6888_);
lean_inc(v_cache_6887_);
lean_inc(v_traceState_6886_);
lean_inc(v_auxDeclNGen_6885_);
lean_inc(v_nextMacroScope_6884_);
lean_inc(v_env_6883_);
lean_dec(v___x_6882_);
v___x_6892_ = lean_box(0);
v_isShared_6893_ = v_isSharedCheck_6906_;
goto v_resetjp_6891_;
}
v_resetjp_6891_:
{
lean_object* v___x_6894_; lean_object* v___x_6895_; lean_object* v___x_6896_; lean_object* v___x_6898_; 
lean_inc(v_idx_6878_);
lean_inc(v_namePrefix_6877_);
v___x_6894_ = l_Lean_Name_num___override(v_namePrefix_6877_, v_idx_6878_);
v___x_6895_ = lean_unsigned_to_nat(1u);
v___x_6896_ = lean_nat_add(v_idx_6878_, v___x_6895_);
lean_dec(v_idx_6878_);
if (v_isShared_6881_ == 0)
{
lean_ctor_set(v___x_6880_, 1, v___x_6896_);
v___x_6898_ = v___x_6880_;
goto v_reusejp_6897_;
}
else
{
lean_object* v_reuseFailAlloc_6905_; 
v_reuseFailAlloc_6905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6905_, 0, v_namePrefix_6877_);
lean_ctor_set(v_reuseFailAlloc_6905_, 1, v___x_6896_);
v___x_6898_ = v_reuseFailAlloc_6905_;
goto v_reusejp_6897_;
}
v_reusejp_6897_:
{
lean_object* v___x_6900_; 
if (v_isShared_6893_ == 0)
{
lean_ctor_set(v___x_6892_, 2, v___x_6898_);
v___x_6900_ = v___x_6892_;
goto v_reusejp_6899_;
}
else
{
lean_object* v_reuseFailAlloc_6904_; 
v_reuseFailAlloc_6904_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6904_, 0, v_env_6883_);
lean_ctor_set(v_reuseFailAlloc_6904_, 1, v_nextMacroScope_6884_);
lean_ctor_set(v_reuseFailAlloc_6904_, 2, v___x_6898_);
lean_ctor_set(v_reuseFailAlloc_6904_, 3, v_auxDeclNGen_6885_);
lean_ctor_set(v_reuseFailAlloc_6904_, 4, v_traceState_6886_);
lean_ctor_set(v_reuseFailAlloc_6904_, 5, v_cache_6887_);
lean_ctor_set(v_reuseFailAlloc_6904_, 6, v_messages_6888_);
lean_ctor_set(v_reuseFailAlloc_6904_, 7, v_infoState_6889_);
lean_ctor_set(v_reuseFailAlloc_6904_, 8, v_snapshotTasks_6890_);
v___x_6900_ = v_reuseFailAlloc_6904_;
goto v_reusejp_6899_;
}
v_reusejp_6899_:
{
lean_object* v___x_6901_; lean_object* v___x_6902_; lean_object* v___x_6903_; 
v___x_6901_ = lean_st_ref_set(v___y_6873_, v___x_6900_);
v___x_6902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6902_, 0, v___x_6894_);
lean_ctor_set(v___x_6902_, 1, v___x_6895_);
v___x_6903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6903_, 0, v___x_6902_);
return v___x_6903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6909_, lean_object* v___y_6910_){
_start:
{
lean_object* v_res_6911_; 
v_res_6911_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6909_);
lean_dec(v___y_6909_);
return v_res_6911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6912_, lean_object* v___y_6913_){
_start:
{
lean_object* v___x_6915_; 
v___x_6915_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6913_);
return v___x_6915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_){
_start:
{
lean_object* v_res_6919_; 
v_res_6919_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6916_, v___y_6917_);
lean_dec(v___y_6917_);
lean_dec_ref(v___y_6916_);
return v_res_6919_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6920_; lean_object* v___x_6921_; lean_object* v___x_6922_; 
v___x_6920_ = lean_unsigned_to_nat(32u);
v___x_6921_ = lean_mk_empty_array_with_capacity(v___x_6920_);
v___x_6922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6922_, 0, v___x_6921_);
return v___x_6922_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6923_; lean_object* v___x_6924_; lean_object* v___x_6925_; lean_object* v___x_6926_; lean_object* v___x_6927_; lean_object* v___x_6928_; 
v___x_6923_ = ((size_t)5ULL);
v___x_6924_ = lean_unsigned_to_nat(0u);
v___x_6925_ = lean_unsigned_to_nat(32u);
v___x_6926_ = lean_mk_empty_array_with_capacity(v___x_6925_);
v___x_6927_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6928_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6928_, 0, v___x_6927_);
lean_ctor_set(v___x_6928_, 1, v___x_6926_);
lean_ctor_set(v___x_6928_, 2, v___x_6924_);
lean_ctor_set(v___x_6928_, 3, v___x_6924_);
lean_ctor_set_usize(v___x_6928_, 4, v___x_6923_);
return v___x_6928_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6929_; lean_object* v___x_6930_; lean_object* v___x_6931_; lean_object* v___x_6932_; 
v___x_6929_ = lean_box(1);
v___x_6930_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6931_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6932_, 0, v___x_6931_);
lean_ctor_set(v___x_6932_, 1, v___x_6930_);
lean_ctor_set(v___x_6932_, 2, v___x_6929_);
return v___x_6932_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6933_, lean_object* v___y_6934_, lean_object* v___y_6935_){
_start:
{
lean_object* v___x_6937_; lean_object* v_env_6938_; lean_object* v_options_6939_; lean_object* v___x_6940_; lean_object* v___x_6941_; lean_object* v___x_6942_; lean_object* v___x_6943_; lean_object* v___x_6944_; 
v___x_6937_ = lean_st_ref_get(v___y_6935_);
v_env_6938_ = lean_ctor_get(v___x_6937_, 0);
lean_inc_ref(v_env_6938_);
lean_dec(v___x_6937_);
v_options_6939_ = lean_ctor_get(v___y_6934_, 2);
v___x_6940_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_6941_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6939_);
v___x_6942_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6942_, 0, v_env_6938_);
lean_ctor_set(v___x_6942_, 1, v___x_6940_);
lean_ctor_set(v___x_6942_, 2, v___x_6941_);
lean_ctor_set(v___x_6942_, 3, v_options_6939_);
v___x_6943_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6943_, 0, v___x_6942_);
lean_ctor_set(v___x_6943_, 1, v_msgData_6933_);
v___x_6944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6944_, 0, v___x_6943_);
return v___x_6944_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6945_, lean_object* v___y_6946_, lean_object* v___y_6947_, lean_object* v___y_6948_){
_start:
{
lean_object* v_res_6949_; 
v_res_6949_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6945_, v___y_6946_, v___y_6947_);
lean_dec(v___y_6947_);
lean_dec_ref(v___y_6946_);
return v_res_6949_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6950_, lean_object* v_msgData_6951_, uint8_t v_severity_6952_, uint8_t v_isSilent_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_){
_start:
{
uint8_t v___y_6958_; lean_object* v___y_6959_; lean_object* v___y_6960_; lean_object* v___y_6961_; uint8_t v___y_6962_; lean_object* v___y_6963_; lean_object* v___y_6964_; lean_object* v___y_6965_; lean_object* v___y_6966_; lean_object* v___y_6994_; uint8_t v___y_6995_; uint8_t v___y_6996_; uint8_t v___y_6997_; lean_object* v___y_6998_; lean_object* v___y_6999_; lean_object* v___y_7000_; lean_object* v___y_7001_; lean_object* v___y_7019_; uint8_t v___y_7020_; uint8_t v___y_7021_; lean_object* v___y_7022_; uint8_t v___y_7023_; lean_object* v___y_7024_; lean_object* v___y_7025_; lean_object* v___y_7026_; lean_object* v___y_7030_; uint8_t v___y_7031_; uint8_t v___y_7032_; lean_object* v___y_7033_; lean_object* v___y_7034_; lean_object* v___y_7035_; uint8_t v___y_7036_; uint8_t v___x_7041_; uint8_t v___y_7043_; lean_object* v___y_7044_; lean_object* v___y_7045_; lean_object* v___y_7046_; lean_object* v___y_7047_; uint8_t v___y_7048_; uint8_t v___y_7049_; uint8_t v___y_7051_; uint8_t v___x_7066_; 
v___x_7041_ = 2;
v___x_7066_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6952_, v___x_7041_);
if (v___x_7066_ == 0)
{
v___y_7051_ = v___x_7066_;
goto v___jp_7050_;
}
else
{
uint8_t v___x_7067_; 
lean_inc_ref(v_msgData_6951_);
v___x_7067_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6951_);
v___y_7051_ = v___x_7067_;
goto v___jp_7050_;
}
v___jp_6957_:
{
lean_object* v___x_6967_; lean_object* v_currNamespace_6968_; lean_object* v_openDecls_6969_; lean_object* v_env_6970_; lean_object* v_nextMacroScope_6971_; lean_object* v_ngen_6972_; lean_object* v_auxDeclNGen_6973_; lean_object* v_traceState_6974_; lean_object* v_cache_6975_; lean_object* v_messages_6976_; lean_object* v_infoState_6977_; lean_object* v_snapshotTasks_6978_; lean_object* v___x_6980_; uint8_t v_isShared_6981_; uint8_t v_isSharedCheck_6992_; 
v___x_6967_ = lean_st_ref_take(v___y_6966_);
v_currNamespace_6968_ = lean_ctor_get(v___y_6965_, 6);
v_openDecls_6969_ = lean_ctor_get(v___y_6965_, 7);
v_env_6970_ = lean_ctor_get(v___x_6967_, 0);
v_nextMacroScope_6971_ = lean_ctor_get(v___x_6967_, 1);
v_ngen_6972_ = lean_ctor_get(v___x_6967_, 2);
v_auxDeclNGen_6973_ = lean_ctor_get(v___x_6967_, 3);
v_traceState_6974_ = lean_ctor_get(v___x_6967_, 4);
v_cache_6975_ = lean_ctor_get(v___x_6967_, 5);
v_messages_6976_ = lean_ctor_get(v___x_6967_, 6);
v_infoState_6977_ = lean_ctor_get(v___x_6967_, 7);
v_snapshotTasks_6978_ = lean_ctor_get(v___x_6967_, 8);
v_isSharedCheck_6992_ = !lean_is_exclusive(v___x_6967_);
if (v_isSharedCheck_6992_ == 0)
{
v___x_6980_ = v___x_6967_;
v_isShared_6981_ = v_isSharedCheck_6992_;
goto v_resetjp_6979_;
}
else
{
lean_inc(v_snapshotTasks_6978_);
lean_inc(v_infoState_6977_);
lean_inc(v_messages_6976_);
lean_inc(v_cache_6975_);
lean_inc(v_traceState_6974_);
lean_inc(v_auxDeclNGen_6973_);
lean_inc(v_ngen_6972_);
lean_inc(v_nextMacroScope_6971_);
lean_inc(v_env_6970_);
lean_dec(v___x_6967_);
v___x_6980_ = lean_box(0);
v_isShared_6981_ = v_isSharedCheck_6992_;
goto v_resetjp_6979_;
}
v_resetjp_6979_:
{
lean_object* v___x_6982_; lean_object* v___x_6983_; lean_object* v___x_6984_; lean_object* v___x_6985_; lean_object* v___x_6987_; 
lean_inc(v_openDecls_6969_);
lean_inc(v_currNamespace_6968_);
v___x_6982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6982_, 0, v_currNamespace_6968_);
lean_ctor_set(v___x_6982_, 1, v_openDecls_6969_);
v___x_6983_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6983_, 0, v___x_6982_);
lean_ctor_set(v___x_6983_, 1, v___y_6961_);
lean_inc_ref(v___y_6963_);
v___x_6984_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6984_, 0, v___y_6963_);
lean_ctor_set(v___x_6984_, 1, v___y_6964_);
lean_ctor_set(v___x_6984_, 2, v___y_6959_);
lean_ctor_set(v___x_6984_, 3, v___y_6960_);
lean_ctor_set(v___x_6984_, 4, v___x_6983_);
lean_ctor_set_uint8(v___x_6984_, sizeof(void*)*5, v___y_6958_);
lean_ctor_set_uint8(v___x_6984_, sizeof(void*)*5 + 1, v___y_6962_);
lean_ctor_set_uint8(v___x_6984_, sizeof(void*)*5 + 2, v_isSilent_6953_);
v___x_6985_ = l_Lean_MessageLog_add(v___x_6984_, v_messages_6976_);
if (v_isShared_6981_ == 0)
{
lean_ctor_set(v___x_6980_, 6, v___x_6985_);
v___x_6987_ = v___x_6980_;
goto v_reusejp_6986_;
}
else
{
lean_object* v_reuseFailAlloc_6991_; 
v_reuseFailAlloc_6991_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6991_, 0, v_env_6970_);
lean_ctor_set(v_reuseFailAlloc_6991_, 1, v_nextMacroScope_6971_);
lean_ctor_set(v_reuseFailAlloc_6991_, 2, v_ngen_6972_);
lean_ctor_set(v_reuseFailAlloc_6991_, 3, v_auxDeclNGen_6973_);
lean_ctor_set(v_reuseFailAlloc_6991_, 4, v_traceState_6974_);
lean_ctor_set(v_reuseFailAlloc_6991_, 5, v_cache_6975_);
lean_ctor_set(v_reuseFailAlloc_6991_, 6, v___x_6985_);
lean_ctor_set(v_reuseFailAlloc_6991_, 7, v_infoState_6977_);
lean_ctor_set(v_reuseFailAlloc_6991_, 8, v_snapshotTasks_6978_);
v___x_6987_ = v_reuseFailAlloc_6991_;
goto v_reusejp_6986_;
}
v_reusejp_6986_:
{
lean_object* v___x_6988_; lean_object* v___x_6989_; lean_object* v___x_6990_; 
v___x_6988_ = lean_st_ref_set(v___y_6966_, v___x_6987_);
v___x_6989_ = lean_box(0);
v___x_6990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6990_, 0, v___x_6989_);
return v___x_6990_;
}
}
}
v___jp_6993_:
{
lean_object* v___x_7002_; lean_object* v___x_7003_; lean_object* v_a_7004_; lean_object* v___x_7006_; uint8_t v_isShared_7007_; uint8_t v_isSharedCheck_7017_; 
v___x_7002_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6951_);
v___x_7003_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_7002_, v___y_6954_, v___y_6955_);
v_a_7004_ = lean_ctor_get(v___x_7003_, 0);
v_isSharedCheck_7017_ = !lean_is_exclusive(v___x_7003_);
if (v_isSharedCheck_7017_ == 0)
{
v___x_7006_ = v___x_7003_;
v_isShared_7007_ = v_isSharedCheck_7017_;
goto v_resetjp_7005_;
}
else
{
lean_inc(v_a_7004_);
lean_dec(v___x_7003_);
v___x_7006_ = lean_box(0);
v_isShared_7007_ = v_isSharedCheck_7017_;
goto v_resetjp_7005_;
}
v_resetjp_7005_:
{
lean_object* v___x_7008_; lean_object* v___x_7009_; lean_object* v___x_7010_; lean_object* v___x_7011_; 
lean_inc_ref(v___y_6998_);
v___x_7008_ = l_Lean_FileMap_toPosition(v___y_6998_, v___y_7000_);
lean_dec(v___y_7000_);
lean_inc_ref(v___y_6998_);
v___x_7009_ = l_Lean_FileMap_toPosition(v___y_6998_, v___y_7001_);
lean_dec(v___y_7001_);
v___x_7010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7010_, 0, v___x_7009_);
v___x_7011_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6995_ == 0)
{
lean_del_object(v___x_7006_);
lean_dec_ref(v___y_6994_);
v___y_6958_ = v___y_6996_;
v___y_6959_ = v___x_7010_;
v___y_6960_ = v___x_7011_;
v___y_6961_ = v_a_7004_;
v___y_6962_ = v___y_6997_;
v___y_6963_ = v___y_6999_;
v___y_6964_ = v___x_7008_;
v___y_6965_ = v___y_6954_;
v___y_6966_ = v___y_6955_;
goto v___jp_6957_;
}
else
{
uint8_t v___x_7012_; 
lean_inc(v_a_7004_);
v___x_7012_ = l_Lean_MessageData_hasTag(v___y_6994_, v_a_7004_);
if (v___x_7012_ == 0)
{
lean_object* v___x_7013_; lean_object* v___x_7015_; 
lean_dec_ref(v___x_7010_);
lean_dec_ref(v___x_7008_);
lean_dec(v_a_7004_);
v___x_7013_ = lean_box(0);
if (v_isShared_7007_ == 0)
{
lean_ctor_set(v___x_7006_, 0, v___x_7013_);
v___x_7015_ = v___x_7006_;
goto v_reusejp_7014_;
}
else
{
lean_object* v_reuseFailAlloc_7016_; 
v_reuseFailAlloc_7016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7016_, 0, v___x_7013_);
v___x_7015_ = v_reuseFailAlloc_7016_;
goto v_reusejp_7014_;
}
v_reusejp_7014_:
{
return v___x_7015_;
}
}
else
{
lean_del_object(v___x_7006_);
v___y_6958_ = v___y_6996_;
v___y_6959_ = v___x_7010_;
v___y_6960_ = v___x_7011_;
v___y_6961_ = v_a_7004_;
v___y_6962_ = v___y_6997_;
v___y_6963_ = v___y_6999_;
v___y_6964_ = v___x_7008_;
v___y_6965_ = v___y_6954_;
v___y_6966_ = v___y_6955_;
goto v___jp_6957_;
}
}
}
}
v___jp_7018_:
{
lean_object* v___x_7027_; 
v___x_7027_ = l_Lean_Syntax_getTailPos_x3f(v___y_7025_, v___y_7020_);
lean_dec(v___y_7025_);
if (lean_obj_tag(v___x_7027_) == 0)
{
lean_inc(v___y_7026_);
v___y_6994_ = v___y_7019_;
v___y_6995_ = v___y_7021_;
v___y_6996_ = v___y_7020_;
v___y_6997_ = v___y_7023_;
v___y_6998_ = v___y_7022_;
v___y_6999_ = v___y_7024_;
v___y_7000_ = v___y_7026_;
v___y_7001_ = v___y_7026_;
goto v___jp_6993_;
}
else
{
lean_object* v_val_7028_; 
v_val_7028_ = lean_ctor_get(v___x_7027_, 0);
lean_inc(v_val_7028_);
lean_dec_ref(v___x_7027_);
v___y_6994_ = v___y_7019_;
v___y_6995_ = v___y_7021_;
v___y_6996_ = v___y_7020_;
v___y_6997_ = v___y_7023_;
v___y_6998_ = v___y_7022_;
v___y_6999_ = v___y_7024_;
v___y_7000_ = v___y_7026_;
v___y_7001_ = v_val_7028_;
goto v___jp_6993_;
}
}
v___jp_7029_:
{
lean_object* v_ref_7037_; lean_object* v___x_7038_; 
v_ref_7037_ = l_Lean_replaceRef(v_ref_6950_, v___y_7035_);
v___x_7038_ = l_Lean_Syntax_getPos_x3f(v_ref_7037_, v___y_7032_);
if (lean_obj_tag(v___x_7038_) == 0)
{
lean_object* v___x_7039_; 
v___x_7039_ = lean_unsigned_to_nat(0u);
v___y_7019_ = v___y_7030_;
v___y_7020_ = v___y_7032_;
v___y_7021_ = v___y_7031_;
v___y_7022_ = v___y_7033_;
v___y_7023_ = v___y_7036_;
v___y_7024_ = v___y_7034_;
v___y_7025_ = v_ref_7037_;
v___y_7026_ = v___x_7039_;
goto v___jp_7018_;
}
else
{
lean_object* v_val_7040_; 
v_val_7040_ = lean_ctor_get(v___x_7038_, 0);
lean_inc(v_val_7040_);
lean_dec_ref(v___x_7038_);
v___y_7019_ = v___y_7030_;
v___y_7020_ = v___y_7032_;
v___y_7021_ = v___y_7031_;
v___y_7022_ = v___y_7033_;
v___y_7023_ = v___y_7036_;
v___y_7024_ = v___y_7034_;
v___y_7025_ = v_ref_7037_;
v___y_7026_ = v_val_7040_;
goto v___jp_7018_;
}
}
v___jp_7042_:
{
if (v___y_7049_ == 0)
{
v___y_7030_ = v___y_7047_;
v___y_7031_ = v___y_7043_;
v___y_7032_ = v___y_7048_;
v___y_7033_ = v___y_7044_;
v___y_7034_ = v___y_7046_;
v___y_7035_ = v___y_7045_;
v___y_7036_ = v_severity_6952_;
goto v___jp_7029_;
}
else
{
v___y_7030_ = v___y_7047_;
v___y_7031_ = v___y_7043_;
v___y_7032_ = v___y_7048_;
v___y_7033_ = v___y_7044_;
v___y_7034_ = v___y_7046_;
v___y_7035_ = v___y_7045_;
v___y_7036_ = v___x_7041_;
goto v___jp_7029_;
}
}
v___jp_7050_:
{
if (v___y_7051_ == 0)
{
lean_object* v_fileName_7052_; lean_object* v_fileMap_7053_; lean_object* v_options_7054_; lean_object* v_ref_7055_; uint8_t v_suppressElabErrors_7056_; lean_object* v___x_7057_; lean_object* v___x_7058_; lean_object* v___f_7059_; uint8_t v___x_7060_; uint8_t v___x_7061_; 
v_fileName_7052_ = lean_ctor_get(v___y_6954_, 0);
v_fileMap_7053_ = lean_ctor_get(v___y_6954_, 1);
v_options_7054_ = lean_ctor_get(v___y_6954_, 2);
v_ref_7055_ = lean_ctor_get(v___y_6954_, 5);
v_suppressElabErrors_7056_ = lean_ctor_get_uint8(v___y_6954_, sizeof(void*)*14 + 1);
v___x_7057_ = lean_box(v___y_7051_);
v___x_7058_ = lean_box(v_suppressElabErrors_7056_);
v___f_7059_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_7059_, 0, v___x_7057_);
lean_closure_set(v___f_7059_, 1, v___x_7058_);
v___x_7060_ = 1;
v___x_7061_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6952_, v___x_7060_);
if (v___x_7061_ == 0)
{
v___y_7043_ = v_suppressElabErrors_7056_;
v___y_7044_ = v_fileMap_7053_;
v___y_7045_ = v_ref_7055_;
v___y_7046_ = v_fileName_7052_;
v___y_7047_ = v___f_7059_;
v___y_7048_ = v___y_7051_;
v___y_7049_ = v___x_7061_;
goto v___jp_7042_;
}
else
{
lean_object* v___x_7062_; uint8_t v___x_7063_; 
v___x_7062_ = l_Lean_warningAsError;
v___x_7063_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_7054_, v___x_7062_);
v___y_7043_ = v_suppressElabErrors_7056_;
v___y_7044_ = v_fileMap_7053_;
v___y_7045_ = v_ref_7055_;
v___y_7046_ = v_fileName_7052_;
v___y_7047_ = v___f_7059_;
v___y_7048_ = v___y_7051_;
v___y_7049_ = v___x_7063_;
goto v___jp_7042_;
}
}
else
{
lean_object* v___x_7064_; lean_object* v___x_7065_; 
lean_dec_ref(v_msgData_6951_);
v___x_7064_ = lean_box(0);
v___x_7065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7065_, 0, v___x_7064_);
return v___x_7065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_7068_, lean_object* v_msgData_7069_, lean_object* v_severity_7070_, lean_object* v_isSilent_7071_, lean_object* v___y_7072_, lean_object* v___y_7073_, lean_object* v___y_7074_){
_start:
{
uint8_t v_severity_boxed_7075_; uint8_t v_isSilent_boxed_7076_; lean_object* v_res_7077_; 
v_severity_boxed_7075_ = lean_unbox(v_severity_7070_);
v_isSilent_boxed_7076_ = lean_unbox(v_isSilent_7071_);
v_res_7077_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_7068_, v_msgData_7069_, v_severity_boxed_7075_, v_isSilent_boxed_7076_, v___y_7072_, v___y_7073_);
lean_dec(v___y_7073_);
lean_dec_ref(v___y_7072_);
lean_dec(v_ref_7068_);
return v_res_7077_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_7078_, uint8_t v_severity_7079_, uint8_t v_isSilent_7080_, lean_object* v___y_7081_, lean_object* v___y_7082_){
_start:
{
lean_object* v_ref_7084_; lean_object* v___x_7085_; 
v_ref_7084_ = lean_ctor_get(v___y_7081_, 5);
v___x_7085_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_7084_, v_msgData_7078_, v_severity_7079_, v_isSilent_7080_, v___y_7081_, v___y_7082_);
return v___x_7085_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_7086_, lean_object* v_severity_7087_, lean_object* v_isSilent_7088_, lean_object* v___y_7089_, lean_object* v___y_7090_, lean_object* v___y_7091_){
_start:
{
uint8_t v_severity_boxed_7092_; uint8_t v_isSilent_boxed_7093_; lean_object* v_res_7094_; 
v_severity_boxed_7092_ = lean_unbox(v_severity_7087_);
v_isSilent_boxed_7093_ = lean_unbox(v_isSilent_7088_);
v_res_7094_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_7086_, v_severity_boxed_7092_, v_isSilent_boxed_7093_, v___y_7089_, v___y_7090_);
lean_dec(v___y_7090_);
lean_dec_ref(v___y_7089_);
return v_res_7094_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_7095_, lean_object* v___y_7096_, lean_object* v___y_7097_){
_start:
{
uint8_t v___x_7099_; uint8_t v___x_7100_; lean_object* v___x_7101_; 
v___x_7099_ = 2;
v___x_7100_ = 0;
v___x_7101_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_7095_, v___x_7099_, v___x_7100_, v___y_7096_, v___y_7097_);
return v___x_7101_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_7102_, lean_object* v___y_7103_, lean_object* v___y_7104_, lean_object* v___y_7105_){
_start:
{
lean_object* v_res_7106_; 
v_res_7106_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_7102_, v___y_7103_, v___y_7104_);
lean_dec(v___y_7104_);
lean_dec_ref(v___y_7103_);
return v_res_7106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_7107_, lean_object* v___y_7108_, lean_object* v___y_7109_){
_start:
{
lean_object* v_module_7111_; lean_object* v_const_7112_; lean_object* v_exception_7113_; lean_object* v___x_7114_; lean_object* v___x_7115_; lean_object* v___x_7116_; lean_object* v___x_7117_; lean_object* v___x_7118_; lean_object* v___x_7119_; lean_object* v___x_7120_; lean_object* v___x_7121_; lean_object* v___x_7122_; lean_object* v___x_7123_; lean_object* v___x_7124_; lean_object* v___x_7125_; 
v_module_7111_ = lean_ctor_get(v_f_7107_, 0);
lean_inc(v_module_7111_);
v_const_7112_ = lean_ctor_get(v_f_7107_, 1);
lean_inc(v_const_7112_);
v_exception_7113_ = lean_ctor_get(v_f_7107_, 2);
lean_inc_ref(v_exception_7113_);
lean_dec_ref(v_f_7107_);
v___x_7114_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_7115_ = l_Lean_MessageData_ofName(v_const_7112_);
v___x_7116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7116_, 0, v___x_7114_);
lean_ctor_set(v___x_7116_, 1, v___x_7115_);
v___x_7117_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_7118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7118_, 0, v___x_7116_);
lean_ctor_set(v___x_7118_, 1, v___x_7117_);
v___x_7119_ = l_Lean_MessageData_ofName(v_module_7111_);
v___x_7120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7120_, 0, v___x_7118_);
lean_ctor_set(v___x_7120_, 1, v___x_7119_);
v___x_7121_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_7122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7122_, 0, v___x_7120_);
lean_ctor_set(v___x_7122_, 1, v___x_7121_);
v___x_7123_ = l_Lean_Exception_toMessageData(v_exception_7113_);
v___x_7124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7124_, 0, v___x_7122_);
lean_ctor_set(v___x_7124_, 1, v___x_7123_);
v___x_7125_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_7124_, v___y_7108_, v___y_7109_);
return v___x_7125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_7126_, lean_object* v___y_7127_, lean_object* v___y_7128_, lean_object* v___y_7129_){
_start:
{
lean_object* v_res_7130_; 
v_res_7130_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_7126_, v___y_7127_, v___y_7128_);
lean_dec(v___y_7128_);
lean_dec_ref(v___y_7127_);
return v_res_7130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_7131_, size_t v_i_7132_, size_t v_stop_7133_, lean_object* v_b_7134_, lean_object* v___y_7135_, lean_object* v___y_7136_){
_start:
{
uint8_t v___x_7138_; 
v___x_7138_ = lean_usize_dec_eq(v_i_7132_, v_stop_7133_);
if (v___x_7138_ == 0)
{
lean_object* v___x_7139_; lean_object* v___x_7140_; 
v___x_7139_ = lean_array_uget_borrowed(v_as_7131_, v_i_7132_);
lean_inc(v___x_7139_);
v___x_7140_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_7139_, v___y_7135_, v___y_7136_);
if (lean_obj_tag(v___x_7140_) == 0)
{
lean_object* v_a_7141_; size_t v___x_7142_; size_t v___x_7143_; 
v_a_7141_ = lean_ctor_get(v___x_7140_, 0);
lean_inc(v_a_7141_);
lean_dec_ref(v___x_7140_);
v___x_7142_ = ((size_t)1ULL);
v___x_7143_ = lean_usize_add(v_i_7132_, v___x_7142_);
v_i_7132_ = v___x_7143_;
v_b_7134_ = v_a_7141_;
goto _start;
}
else
{
return v___x_7140_;
}
}
else
{
lean_object* v___x_7145_; 
v___x_7145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7145_, 0, v_b_7134_);
return v___x_7145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_7146_, lean_object* v_i_7147_, lean_object* v_stop_7148_, lean_object* v_b_7149_, lean_object* v___y_7150_, lean_object* v___y_7151_, lean_object* v___y_7152_){
_start:
{
size_t v_i_boxed_7153_; size_t v_stop_boxed_7154_; lean_object* v_res_7155_; 
v_i_boxed_7153_ = lean_unbox_usize(v_i_7147_);
lean_dec(v_i_7147_);
v_stop_boxed_7154_ = lean_unbox_usize(v_stop_7148_);
lean_dec(v_stop_7148_);
v_res_7155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_7146_, v_i_boxed_7153_, v_stop_boxed_7154_, v_b_7149_, v___y_7150_, v___y_7151_);
lean_dec(v___y_7151_);
lean_dec_ref(v___y_7150_);
lean_dec_ref(v_as_7146_);
return v_res_7155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7156_, lean_object* v_a_7157_, lean_object* v_a_7158_){
_start:
{
lean_object* v___x_7160_; lean_object* v___x_7161_; lean_object* v_a_7162_; lean_object* v___x_7164_; uint8_t v_isShared_7165_; uint8_t v_isSharedCheck_7196_; 
v___x_7160_ = lean_st_ref_get(v_a_7158_);
v___x_7161_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7158_);
v_a_7162_ = lean_ctor_get(v___x_7161_, 0);
v_isSharedCheck_7196_ = !lean_is_exclusive(v___x_7161_);
if (v_isSharedCheck_7196_ == 0)
{
v___x_7164_ = v___x_7161_;
v_isShared_7165_ = v_isSharedCheck_7196_;
goto v_resetjp_7163_;
}
else
{
lean_inc(v_a_7162_);
lean_dec(v___x_7161_);
v___x_7164_ = lean_box(0);
v_isShared_7165_ = v_isSharedCheck_7196_;
goto v_resetjp_7163_;
}
v_resetjp_7163_:
{
lean_object* v___x_7166_; lean_object* v_env_7167_; lean_object* v___x_7168_; lean_object* v___y_7175_; lean_object* v___x_7184_; lean_object* v___x_7185_; lean_object* v___x_7186_; uint8_t v___x_7187_; 
v___x_7166_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v_env_7167_ = lean_ctor_get(v___x_7160_, 0);
lean_inc_ref(v_env_7167_);
lean_dec(v___x_7160_);
lean_inc(v___x_7166_);
lean_inc_ref(v_a_7157_);
v___x_7168_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7157_, v_a_7162_, v_env_7167_, v___x_7166_, v_entriesForConst_7156_);
v___x_7184_ = lean_st_ref_get(v___x_7166_);
lean_dec(v___x_7166_);
v___x_7185_ = lean_unsigned_to_nat(0u);
v___x_7186_ = lean_array_get_size(v___x_7184_);
v___x_7187_ = lean_nat_dec_lt(v___x_7185_, v___x_7186_);
if (v___x_7187_ == 0)
{
lean_dec(v___x_7184_);
goto v___jp_7169_;
}
else
{
lean_object* v___x_7188_; uint8_t v___x_7189_; 
v___x_7188_ = lean_box(0);
v___x_7189_ = lean_nat_dec_le(v___x_7186_, v___x_7186_);
if (v___x_7189_ == 0)
{
if (v___x_7187_ == 0)
{
lean_dec(v___x_7184_);
goto v___jp_7169_;
}
else
{
size_t v___x_7190_; size_t v___x_7191_; lean_object* v___x_7192_; 
v___x_7190_ = ((size_t)0ULL);
v___x_7191_ = lean_usize_of_nat(v___x_7186_);
v___x_7192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7184_, v___x_7190_, v___x_7191_, v___x_7188_, v_a_7157_, v_a_7158_);
lean_dec(v___x_7184_);
v___y_7175_ = v___x_7192_;
goto v___jp_7174_;
}
}
else
{
size_t v___x_7193_; size_t v___x_7194_; lean_object* v___x_7195_; 
v___x_7193_ = ((size_t)0ULL);
v___x_7194_ = lean_usize_of_nat(v___x_7186_);
v___x_7195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7184_, v___x_7193_, v___x_7194_, v___x_7188_, v_a_7157_, v_a_7158_);
lean_dec(v___x_7184_);
v___y_7175_ = v___x_7195_;
goto v___jp_7174_;
}
}
v___jp_7169_:
{
lean_object* v___x_7170_; lean_object* v___x_7172_; 
v___x_7170_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7168_);
if (v_isShared_7165_ == 0)
{
lean_ctor_set(v___x_7164_, 0, v___x_7170_);
v___x_7172_ = v___x_7164_;
goto v_reusejp_7171_;
}
else
{
lean_object* v_reuseFailAlloc_7173_; 
v_reuseFailAlloc_7173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7173_, 0, v___x_7170_);
v___x_7172_ = v_reuseFailAlloc_7173_;
goto v_reusejp_7171_;
}
v_reusejp_7171_:
{
return v___x_7172_;
}
}
v___jp_7174_:
{
if (lean_obj_tag(v___y_7175_) == 0)
{
lean_dec_ref(v___y_7175_);
goto v___jp_7169_;
}
else
{
lean_object* v_a_7176_; lean_object* v___x_7178_; uint8_t v_isShared_7179_; uint8_t v_isSharedCheck_7183_; 
lean_dec_ref(v___x_7168_);
lean_del_object(v___x_7164_);
v_a_7176_ = lean_ctor_get(v___y_7175_, 0);
v_isSharedCheck_7183_ = !lean_is_exclusive(v___y_7175_);
if (v_isSharedCheck_7183_ == 0)
{
v___x_7178_ = v___y_7175_;
v_isShared_7179_ = v_isSharedCheck_7183_;
goto v_resetjp_7177_;
}
else
{
lean_inc(v_a_7176_);
lean_dec(v___y_7175_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7197_, lean_object* v_a_7198_, lean_object* v_a_7199_, lean_object* v_a_7200_){
_start:
{
lean_object* v_res_7201_; 
v_res_7201_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7197_, v_a_7198_, v_a_7199_);
lean_dec(v_a_7199_);
lean_dec_ref(v_a_7198_);
return v_res_7201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7202_, lean_object* v_entriesForConst_7203_, lean_object* v_a_7204_, lean_object* v_a_7205_){
_start:
{
lean_object* v___x_7207_; 
v___x_7207_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7203_, v_a_7204_, v_a_7205_);
return v___x_7207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7208_, lean_object* v_entriesForConst_7209_, lean_object* v_a_7210_, lean_object* v_a_7211_, lean_object* v_a_7212_){
_start:
{
lean_object* v_res_7213_; 
v_res_7213_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7208_, v_entriesForConst_7209_, v_a_7210_, v_a_7211_);
lean_dec(v_a_7211_);
lean_dec_ref(v_a_7210_);
return v_res_7213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7214_, lean_object* v_droppedEntriesRef_7215_, lean_object* v_droppedKeys_7216_, lean_object* v___y_7217_, lean_object* v___y_7218_, lean_object* v___y_7219_, lean_object* v___y_7220_){
_start:
{
lean_object* v_t_7223_; lean_object* v___x_7226_; 
v___x_7226_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7214_, v___y_7219_, v___y_7220_);
if (lean_obj_tag(v___x_7226_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7215_) == 1)
{
lean_object* v_a_7227_; lean_object* v_val_7228_; lean_object* v___x_7230_; uint8_t v_isShared_7231_; uint8_t v_isSharedCheck_7254_; 
v_a_7227_ = lean_ctor_get(v___x_7226_, 0);
lean_inc(v_a_7227_);
lean_dec_ref(v___x_7226_);
v_val_7228_ = lean_ctor_get(v_droppedEntriesRef_7215_, 0);
v_isSharedCheck_7254_ = !lean_is_exclusive(v_droppedEntriesRef_7215_);
if (v_isSharedCheck_7254_ == 0)
{
v___x_7230_ = v_droppedEntriesRef_7215_;
v_isShared_7231_ = v_isSharedCheck_7254_;
goto v_resetjp_7229_;
}
else
{
lean_inc(v_val_7228_);
lean_dec(v_droppedEntriesRef_7215_);
v___x_7230_ = lean_box(0);
v_isShared_7231_ = v_isSharedCheck_7254_;
goto v_resetjp_7229_;
}
v_resetjp_7229_:
{
lean_object* v___x_7232_; 
v___x_7232_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7227_, v_droppedKeys_7216_, v___y_7217_, v___y_7218_, v___y_7219_, v___y_7220_);
if (lean_obj_tag(v___x_7232_) == 0)
{
lean_object* v_a_7233_; lean_object* v_fst_7234_; lean_object* v_snd_7235_; lean_object* v___x_7236_; lean_object* v___y_7238_; 
v_a_7233_ = lean_ctor_get(v___x_7232_, 0);
lean_inc(v_a_7233_);
lean_dec_ref(v___x_7232_);
v_fst_7234_ = lean_ctor_get(v_a_7233_, 0);
lean_inc(v_fst_7234_);
v_snd_7235_ = lean_ctor_get(v_a_7233_, 1);
lean_inc(v_snd_7235_);
lean_dec(v_a_7233_);
v___x_7236_ = lean_st_ref_get(v_val_7228_);
if (lean_obj_tag(v___x_7236_) == 0)
{
lean_object* v___x_7244_; 
v___x_7244_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_7238_ = v___x_7244_;
goto v___jp_7237_;
}
else
{
lean_object* v_val_7245_; 
v_val_7245_ = lean_ctor_get(v___x_7236_, 0);
lean_inc(v_val_7245_);
lean_dec_ref(v___x_7236_);
v___y_7238_ = v_val_7245_;
goto v___jp_7237_;
}
v___jp_7237_:
{
lean_object* v___x_7239_; lean_object* v___x_7241_; 
v___x_7239_ = l_Array_append___redArg(v___y_7238_, v_fst_7234_);
lean_dec(v_fst_7234_);
if (v_isShared_7231_ == 0)
{
lean_ctor_set(v___x_7230_, 0, v___x_7239_);
v___x_7241_ = v___x_7230_;
goto v_reusejp_7240_;
}
else
{
lean_object* v_reuseFailAlloc_7243_; 
v_reuseFailAlloc_7243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7243_, 0, v___x_7239_);
v___x_7241_ = v_reuseFailAlloc_7243_;
goto v_reusejp_7240_;
}
v_reusejp_7240_:
{
lean_object* v___x_7242_; 
v___x_7242_ = lean_st_ref_set(v_val_7228_, v___x_7241_);
lean_dec(v_val_7228_);
v_t_7223_ = v_snd_7235_;
goto v___jp_7222_;
}
}
}
else
{
lean_object* v_a_7246_; lean_object* v___x_7248_; uint8_t v_isShared_7249_; uint8_t v_isSharedCheck_7253_; 
lean_del_object(v___x_7230_);
lean_dec(v_val_7228_);
v_a_7246_ = lean_ctor_get(v___x_7232_, 0);
v_isSharedCheck_7253_ = !lean_is_exclusive(v___x_7232_);
if (v_isSharedCheck_7253_ == 0)
{
v___x_7248_ = v___x_7232_;
v_isShared_7249_ = v_isSharedCheck_7253_;
goto v_resetjp_7247_;
}
else
{
lean_inc(v_a_7246_);
lean_dec(v___x_7232_);
v___x_7248_ = lean_box(0);
v_isShared_7249_ = v_isSharedCheck_7253_;
goto v_resetjp_7247_;
}
v_resetjp_7247_:
{
lean_object* v___x_7251_; 
if (v_isShared_7249_ == 0)
{
v___x_7251_ = v___x_7248_;
goto v_reusejp_7250_;
}
else
{
lean_object* v_reuseFailAlloc_7252_; 
v_reuseFailAlloc_7252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7252_, 0, v_a_7246_);
v___x_7251_ = v_reuseFailAlloc_7252_;
goto v_reusejp_7250_;
}
v_reusejp_7250_:
{
return v___x_7251_;
}
}
}
}
}
else
{
lean_object* v_a_7255_; lean_object* v___x_7256_; 
lean_dec(v_droppedEntriesRef_7215_);
v_a_7255_ = lean_ctor_get(v___x_7226_, 0);
lean_inc(v_a_7255_);
lean_dec_ref(v___x_7226_);
v___x_7256_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7255_, v_droppedKeys_7216_, v___y_7217_, v___y_7218_, v___y_7219_, v___y_7220_);
if (lean_obj_tag(v___x_7256_) == 0)
{
lean_object* v_a_7257_; 
v_a_7257_ = lean_ctor_get(v___x_7256_, 0);
lean_inc(v_a_7257_);
lean_dec_ref(v___x_7256_);
v_t_7223_ = v_a_7257_;
goto v___jp_7222_;
}
else
{
lean_object* v_a_7258_; lean_object* v___x_7260_; uint8_t v_isShared_7261_; uint8_t v_isSharedCheck_7265_; 
v_a_7258_ = lean_ctor_get(v___x_7256_, 0);
v_isSharedCheck_7265_ = !lean_is_exclusive(v___x_7256_);
if (v_isSharedCheck_7265_ == 0)
{
v___x_7260_ = v___x_7256_;
v_isShared_7261_ = v_isSharedCheck_7265_;
goto v_resetjp_7259_;
}
else
{
lean_inc(v_a_7258_);
lean_dec(v___x_7256_);
v___x_7260_ = lean_box(0);
v_isShared_7261_ = v_isSharedCheck_7265_;
goto v_resetjp_7259_;
}
v_resetjp_7259_:
{
lean_object* v___x_7263_; 
if (v_isShared_7261_ == 0)
{
v___x_7263_ = v___x_7260_;
goto v_reusejp_7262_;
}
else
{
lean_object* v_reuseFailAlloc_7264_; 
v_reuseFailAlloc_7264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7264_, 0, v_a_7258_);
v___x_7263_ = v_reuseFailAlloc_7264_;
goto v_reusejp_7262_;
}
v_reusejp_7262_:
{
return v___x_7263_;
}
}
}
}
}
else
{
lean_object* v_a_7266_; lean_object* v___x_7268_; uint8_t v_isShared_7269_; uint8_t v_isSharedCheck_7273_; 
lean_dec(v_droppedKeys_7216_);
lean_dec(v_droppedEntriesRef_7215_);
v_a_7266_ = lean_ctor_get(v___x_7226_, 0);
v_isSharedCheck_7273_ = !lean_is_exclusive(v___x_7226_);
if (v_isSharedCheck_7273_ == 0)
{
v___x_7268_ = v___x_7226_;
v_isShared_7269_ = v_isSharedCheck_7273_;
goto v_resetjp_7267_;
}
else
{
lean_inc(v_a_7266_);
lean_dec(v___x_7226_);
v___x_7268_ = lean_box(0);
v_isShared_7269_ = v_isSharedCheck_7273_;
goto v_resetjp_7267_;
}
v_resetjp_7267_:
{
lean_object* v___x_7271_; 
if (v_isShared_7269_ == 0)
{
v___x_7271_ = v___x_7268_;
goto v_reusejp_7270_;
}
else
{
lean_object* v_reuseFailAlloc_7272_; 
v_reuseFailAlloc_7272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7272_, 0, v_a_7266_);
v___x_7271_ = v_reuseFailAlloc_7272_;
goto v_reusejp_7270_;
}
v_reusejp_7270_:
{
return v___x_7271_;
}
}
}
v___jp_7222_:
{
lean_object* v___x_7224_; lean_object* v___x_7225_; 
v___x_7224_ = lean_st_mk_ref(v_t_7223_);
v___x_7225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7225_, 0, v___x_7224_);
return v___x_7225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7274_, lean_object* v_droppedEntriesRef_7275_, lean_object* v_droppedKeys_7276_, lean_object* v___y_7277_, lean_object* v___y_7278_, lean_object* v___y_7279_, lean_object* v___y_7280_, lean_object* v___y_7281_){
_start:
{
lean_object* v_res_7282_; 
v_res_7282_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7274_, v_droppedEntriesRef_7275_, v_droppedKeys_7276_, v___y_7277_, v___y_7278_, v___y_7279_, v___y_7280_);
lean_dec(v___y_7280_);
lean_dec_ref(v___y_7279_);
lean_dec(v___y_7278_);
lean_dec_ref(v___y_7277_);
return v_res_7282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7284_, lean_object* v_droppedKeys_7285_, lean_object* v_droppedEntriesRef_7286_, lean_object* v_a_7287_, lean_object* v_a_7288_, lean_object* v_a_7289_, lean_object* v_a_7290_){
_start:
{
lean_object* v_options_7292_; lean_object* v___f_7293_; lean_object* v___x_7294_; lean_object* v___x_7295_; lean_object* v___x_7296_; 
v_options_7292_ = lean_ctor_get(v_a_7289_, 2);
v___f_7293_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7293_, 0, v_entriesForConst_7284_);
lean_closure_set(v___f_7293_, 1, v_droppedEntriesRef_7286_);
lean_closure_set(v___f_7293_, 2, v_droppedKeys_7285_);
v___x_7294_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7295_ = lean_box(0);
v___x_7296_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7294_, v_options_7292_, v___f_7293_, v___x_7295_, v_a_7287_, v_a_7288_, v_a_7289_, v_a_7290_);
return v___x_7296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7297_, lean_object* v_droppedKeys_7298_, lean_object* v_droppedEntriesRef_7299_, lean_object* v_a_7300_, lean_object* v_a_7301_, lean_object* v_a_7302_, lean_object* v_a_7303_, lean_object* v_a_7304_){
_start:
{
lean_object* v_res_7305_; 
v_res_7305_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7297_, v_droppedKeys_7298_, v_droppedEntriesRef_7299_, v_a_7300_, v_a_7301_, v_a_7302_, v_a_7303_);
lean_dec(v_a_7303_);
lean_dec_ref(v_a_7302_);
lean_dec(v_a_7301_);
lean_dec_ref(v_a_7300_);
return v_res_7305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7306_, lean_object* v_entriesForConst_7307_, lean_object* v_droppedKeys_7308_, lean_object* v_droppedEntriesRef_7309_, lean_object* v_a_7310_, lean_object* v_a_7311_, lean_object* v_a_7312_, lean_object* v_a_7313_){
_start:
{
lean_object* v___x_7315_; 
v___x_7315_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7307_, v_droppedKeys_7308_, v_droppedEntriesRef_7309_, v_a_7310_, v_a_7311_, v_a_7312_, v_a_7313_);
return v___x_7315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7316_, lean_object* v_entriesForConst_7317_, lean_object* v_droppedKeys_7318_, lean_object* v_droppedEntriesRef_7319_, lean_object* v_a_7320_, lean_object* v_a_7321_, lean_object* v_a_7322_, lean_object* v_a_7323_, lean_object* v_a_7324_){
_start:
{
lean_object* v_res_7325_; 
v_res_7325_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7316_, v_entriesForConst_7317_, v_droppedKeys_7318_, v_droppedEntriesRef_7319_, v_a_7320_, v_a_7321_, v_a_7322_, v_a_7323_);
lean_dec(v_a_7323_);
lean_dec_ref(v_a_7322_);
lean_dec(v_a_7321_);
lean_dec_ref(v_a_7320_);
return v_res_7325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7326_, lean_object* v_ty_7327_, lean_object* v___y_7328_, lean_object* v___y_7329_, lean_object* v___y_7330_, lean_object* v___y_7331_){
_start:
{
lean_object* v___x_7333_; lean_object* v___x_7334_; 
v___x_7333_ = lean_st_ref_get(v_moduleRef_7326_);
v___x_7334_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7333_, v_ty_7327_, v___y_7328_, v___y_7329_, v___y_7330_, v___y_7331_);
if (lean_obj_tag(v___x_7334_) == 0)
{
lean_object* v_a_7335_; lean_object* v___x_7337_; uint8_t v_isShared_7338_; uint8_t v_isSharedCheck_7345_; 
v_a_7335_ = lean_ctor_get(v___x_7334_, 0);
v_isSharedCheck_7345_ = !lean_is_exclusive(v___x_7334_);
if (v_isSharedCheck_7345_ == 0)
{
v___x_7337_ = v___x_7334_;
v_isShared_7338_ = v_isSharedCheck_7345_;
goto v_resetjp_7336_;
}
else
{
lean_inc(v_a_7335_);
lean_dec(v___x_7334_);
v___x_7337_ = lean_box(0);
v_isShared_7338_ = v_isSharedCheck_7345_;
goto v_resetjp_7336_;
}
v_resetjp_7336_:
{
lean_object* v_fst_7339_; lean_object* v_snd_7340_; lean_object* v___x_7341_; lean_object* v___x_7343_; 
v_fst_7339_ = lean_ctor_get(v_a_7335_, 0);
lean_inc(v_fst_7339_);
v_snd_7340_ = lean_ctor_get(v_a_7335_, 1);
lean_inc(v_snd_7340_);
lean_dec(v_a_7335_);
v___x_7341_ = lean_st_ref_set(v_moduleRef_7326_, v_snd_7340_);
if (v_isShared_7338_ == 0)
{
lean_ctor_set(v___x_7337_, 0, v_fst_7339_);
v___x_7343_ = v___x_7337_;
goto v_reusejp_7342_;
}
else
{
lean_object* v_reuseFailAlloc_7344_; 
v_reuseFailAlloc_7344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7344_, 0, v_fst_7339_);
v___x_7343_ = v_reuseFailAlloc_7344_;
goto v_reusejp_7342_;
}
v_reusejp_7342_:
{
return v___x_7343_;
}
}
}
else
{
lean_object* v_a_7346_; lean_object* v___x_7348_; uint8_t v_isShared_7349_; uint8_t v_isSharedCheck_7353_; 
v_a_7346_ = lean_ctor_get(v___x_7334_, 0);
v_isSharedCheck_7353_ = !lean_is_exclusive(v___x_7334_);
if (v_isSharedCheck_7353_ == 0)
{
v___x_7348_ = v___x_7334_;
v_isShared_7349_ = v_isSharedCheck_7353_;
goto v_resetjp_7347_;
}
else
{
lean_inc(v_a_7346_);
lean_dec(v___x_7334_);
v___x_7348_ = lean_box(0);
v_isShared_7349_ = v_isSharedCheck_7353_;
goto v_resetjp_7347_;
}
v_resetjp_7347_:
{
lean_object* v___x_7351_; 
if (v_isShared_7349_ == 0)
{
v___x_7351_ = v___x_7348_;
goto v_reusejp_7350_;
}
else
{
lean_object* v_reuseFailAlloc_7352_; 
v_reuseFailAlloc_7352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7352_, 0, v_a_7346_);
v___x_7351_ = v_reuseFailAlloc_7352_;
goto v_reusejp_7350_;
}
v_reusejp_7350_:
{
return v___x_7351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7354_, lean_object* v_ty_7355_, lean_object* v___y_7356_, lean_object* v___y_7357_, lean_object* v___y_7358_, lean_object* v___y_7359_, lean_object* v___y_7360_){
_start:
{
lean_object* v_res_7361_; 
v_res_7361_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7354_, v_ty_7355_, v___y_7356_, v___y_7357_, v___y_7358_, v___y_7359_);
lean_dec(v___y_7359_);
lean_dec_ref(v___y_7358_);
lean_dec(v___y_7357_);
lean_dec_ref(v___y_7356_);
lean_dec(v_moduleRef_7354_);
return v_res_7361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7363_, lean_object* v_ty_7364_, lean_object* v_a_7365_, lean_object* v_a_7366_, lean_object* v_a_7367_, lean_object* v_a_7368_){
_start:
{
lean_object* v_options_7370_; lean_object* v___f_7371_; lean_object* v___x_7372_; lean_object* v___x_7373_; lean_object* v___x_7374_; 
v_options_7370_ = lean_ctor_get(v_a_7367_, 2);
v___f_7371_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7371_, 0, v_moduleRef_7363_);
lean_closure_set(v___f_7371_, 1, v_ty_7364_);
v___x_7372_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7373_ = lean_box(0);
v___x_7374_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7372_, v_options_7370_, v___f_7371_, v___x_7373_, v_a_7365_, v_a_7366_, v_a_7367_, v_a_7368_);
return v___x_7374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7375_, lean_object* v_ty_7376_, lean_object* v_a_7377_, lean_object* v_a_7378_, lean_object* v_a_7379_, lean_object* v_a_7380_, lean_object* v_a_7381_){
_start:
{
lean_object* v_res_7382_; 
v_res_7382_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7375_, v_ty_7376_, v_a_7377_, v_a_7378_, v_a_7379_, v_a_7380_);
lean_dec(v_a_7380_);
lean_dec_ref(v_a_7379_);
lean_dec(v_a_7378_);
lean_dec_ref(v_a_7377_);
return v_res_7382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7383_, lean_object* v_moduleRef_7384_, lean_object* v_ty_7385_, lean_object* v_a_7386_, lean_object* v_a_7387_, lean_object* v_a_7388_, lean_object* v_a_7389_){
_start:
{
lean_object* v___x_7391_; 
v___x_7391_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7384_, v_ty_7385_, v_a_7386_, v_a_7387_, v_a_7388_, v_a_7389_);
return v___x_7391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7392_, lean_object* v_moduleRef_7393_, lean_object* v_ty_7394_, lean_object* v_a_7395_, lean_object* v_a_7396_, lean_object* v_a_7397_, lean_object* v_a_7398_, lean_object* v_a_7399_){
_start:
{
lean_object* v_res_7400_; 
v_res_7400_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7392_, v_moduleRef_7393_, v_ty_7394_, v_a_7395_, v_a_7396_, v_a_7397_, v_a_7398_);
lean_dec(v_a_7398_);
lean_dec_ref(v_a_7397_);
lean_dec(v_a_7396_);
lean_dec_ref(v_a_7395_);
return v_res_7400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7401_, lean_object* v_j_7402_, size_t v_sz_7403_, size_t v_i_7404_, lean_object* v_bs_7405_){
_start:
{
uint8_t v___x_7406_; 
v___x_7406_ = lean_usize_dec_lt(v_i_7404_, v_sz_7403_);
if (v___x_7406_ == 0)
{
lean_dec(v_j_7402_);
lean_dec(v_adjustResult_7401_);
return v_bs_7405_;
}
else
{
lean_object* v_v_7407_; lean_object* v___x_7408_; lean_object* v_bs_x27_7409_; lean_object* v___x_7410_; size_t v___x_7411_; size_t v___x_7412_; lean_object* v___x_7413_; 
v_v_7407_ = lean_array_uget(v_bs_7405_, v_i_7404_);
v___x_7408_ = lean_unsigned_to_nat(0u);
v_bs_x27_7409_ = lean_array_uset(v_bs_7405_, v_i_7404_, v___x_7408_);
lean_inc(v_adjustResult_7401_);
lean_inc(v_j_7402_);
v___x_7410_ = lean_apply_2(v_adjustResult_7401_, v_j_7402_, v_v_7407_);
v___x_7411_ = ((size_t)1ULL);
v___x_7412_ = lean_usize_add(v_i_7404_, v___x_7411_);
v___x_7413_ = lean_array_uset(v_bs_x27_7409_, v_i_7404_, v___x_7410_);
v_i_7404_ = v___x_7412_;
v_bs_7405_ = v___x_7413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7415_, lean_object* v_j_7416_, lean_object* v_sz_7417_, lean_object* v_i_7418_, lean_object* v_bs_7419_){
_start:
{
size_t v_sz_boxed_7420_; size_t v_i_boxed_7421_; lean_object* v_res_7422_; 
v_sz_boxed_7420_ = lean_unbox_usize(v_sz_7417_);
lean_dec(v_sz_7417_);
v_i_boxed_7421_ = lean_unbox_usize(v_i_7418_);
lean_dec(v_i_7418_);
v_res_7422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7415_, v_j_7416_, v_sz_boxed_7420_, v_i_boxed_7421_, v_bs_7419_);
return v_res_7422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7423_, lean_object* v_j_7424_, lean_object* v_as_7425_, size_t v_i_7426_, size_t v_stop_7427_, lean_object* v_b_7428_){
_start:
{
uint8_t v___x_7429_; 
v___x_7429_ = lean_usize_dec_eq(v_i_7426_, v_stop_7427_);
if (v___x_7429_ == 0)
{
lean_object* v___x_7430_; size_t v_sz_7431_; size_t v___x_7432_; lean_object* v___x_7433_; lean_object* v___x_7434_; size_t v___x_7435_; size_t v___x_7436_; 
v___x_7430_ = lean_array_uget_borrowed(v_as_7425_, v_i_7426_);
v_sz_7431_ = lean_array_size(v___x_7430_);
v___x_7432_ = ((size_t)0ULL);
lean_inc(v___x_7430_);
lean_inc(v_j_7424_);
lean_inc(v_adjustResult_7423_);
v___x_7433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7423_, v_j_7424_, v_sz_7431_, v___x_7432_, v___x_7430_);
v___x_7434_ = l_Array_append___redArg(v_b_7428_, v___x_7433_);
lean_dec_ref(v___x_7433_);
v___x_7435_ = ((size_t)1ULL);
v___x_7436_ = lean_usize_add(v_i_7426_, v___x_7435_);
v_i_7426_ = v___x_7436_;
v_b_7428_ = v___x_7434_;
goto _start;
}
else
{
lean_dec(v_j_7424_);
lean_dec(v_adjustResult_7423_);
return v_b_7428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7438_, lean_object* v_j_7439_, lean_object* v_as_7440_, lean_object* v_i_7441_, lean_object* v_stop_7442_, lean_object* v_b_7443_){
_start:
{
size_t v_i_boxed_7444_; size_t v_stop_boxed_7445_; lean_object* v_res_7446_; 
v_i_boxed_7444_ = lean_unbox_usize(v_i_7441_);
lean_dec(v_i_7441_);
v_stop_boxed_7445_ = lean_unbox_usize(v_stop_7442_);
lean_dec(v_stop_7442_);
v_res_7446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7438_, v_j_7439_, v_as_7440_, v_i_boxed_7444_, v_stop_boxed_7445_, v_b_7443_);
lean_dec_ref(v_as_7440_);
return v_res_7446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7447_, lean_object* v_aa_7448_, lean_object* v_adjustResult_7449_, lean_object* v_n_7450_, lean_object* v_j_7451_, lean_object* v_a_7452_){
_start:
{
lean_object* v_zero_7453_; uint8_t v_isZero_7454_; 
v_zero_7453_ = lean_unsigned_to_nat(0u);
v_isZero_7454_ = lean_nat_dec_eq(v_j_7451_, v_zero_7453_);
if (v_isZero_7454_ == 1)
{
lean_dec(v_j_7451_);
lean_dec(v_adjustResult_7449_);
return v_a_7452_;
}
else
{
lean_object* v_one_7455_; lean_object* v_n_7456_; lean_object* v___x_7457_; lean_object* v___x_7458_; lean_object* v_j_7459_; lean_object* v_b_7460_; lean_object* v___x_7461_; uint8_t v___x_7462_; 
v_one_7455_ = lean_unsigned_to_nat(1u);
v_n_7456_ = lean_nat_sub(v_j_7451_, v_one_7455_);
v___x_7457_ = lean_nat_sub(v_n_7450_, v_j_7451_);
lean_dec(v_j_7451_);
v___x_7458_ = lean_nat_sub(v_n_7447_, v_one_7455_);
v_j_7459_ = lean_nat_sub(v___x_7458_, v___x_7457_);
lean_dec(v___x_7457_);
lean_dec(v___x_7458_);
v_b_7460_ = lean_array_fget_borrowed(v_aa_7448_, v_j_7459_);
v___x_7461_ = lean_array_get_size(v_b_7460_);
v___x_7462_ = lean_nat_dec_lt(v_zero_7453_, v___x_7461_);
if (v___x_7462_ == 0)
{
lean_dec(v_j_7459_);
v_j_7451_ = v_n_7456_;
goto _start;
}
else
{
uint8_t v___x_7464_; 
v___x_7464_ = lean_nat_dec_le(v___x_7461_, v___x_7461_);
if (v___x_7464_ == 0)
{
if (v___x_7462_ == 0)
{
lean_dec(v_j_7459_);
v_j_7451_ = v_n_7456_;
goto _start;
}
else
{
size_t v___x_7466_; size_t v___x_7467_; lean_object* v___x_7468_; 
v___x_7466_ = ((size_t)0ULL);
v___x_7467_ = lean_usize_of_nat(v___x_7461_);
lean_inc(v_adjustResult_7449_);
v___x_7468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7449_, v_j_7459_, v_b_7460_, v___x_7466_, v___x_7467_, v_a_7452_);
v_j_7451_ = v_n_7456_;
v_a_7452_ = v___x_7468_;
goto _start;
}
}
else
{
size_t v___x_7470_; size_t v___x_7471_; lean_object* v___x_7472_; 
v___x_7470_ = ((size_t)0ULL);
v___x_7471_ = lean_usize_of_nat(v___x_7461_);
lean_inc(v_adjustResult_7449_);
v___x_7472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7449_, v_j_7459_, v_b_7460_, v___x_7470_, v___x_7471_, v_a_7452_);
v_j_7451_ = v_n_7456_;
v_a_7452_ = v___x_7472_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7474_, lean_object* v_aa_7475_, lean_object* v_adjustResult_7476_, lean_object* v_n_7477_, lean_object* v_j_7478_, lean_object* v_a_7479_){
_start:
{
lean_object* v_res_7480_; 
v_res_7480_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7474_, v_aa_7475_, v_adjustResult_7476_, v_n_7477_, v_j_7478_, v_a_7479_);
lean_dec(v_n_7477_);
lean_dec_ref(v_aa_7475_);
lean_dec(v_n_7474_);
return v_res_7480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7481_, lean_object* v_adjustResult_7482_, lean_object* v_aa_7483_, lean_object* v_n_7484_, lean_object* v_j_7485_, lean_object* v_a_7486_){
_start:
{
lean_object* v_zero_7487_; uint8_t v_isZero_7488_; 
v_zero_7487_ = lean_unsigned_to_nat(0u);
v_isZero_7488_ = lean_nat_dec_eq(v_j_7485_, v_zero_7487_);
if (v_isZero_7488_ == 1)
{
lean_dec(v_adjustResult_7482_);
return v_a_7486_;
}
else
{
lean_object* v_one_7489_; lean_object* v_n_7490_; lean_object* v___x_7491_; lean_object* v___x_7492_; lean_object* v_j_7493_; lean_object* v_b_7494_; lean_object* v___x_7495_; uint8_t v___x_7496_; 
v_one_7489_ = lean_unsigned_to_nat(1u);
v_n_7490_ = lean_nat_sub(v_j_7485_, v_one_7489_);
v___x_7491_ = lean_nat_sub(v_n_7484_, v_j_7485_);
v___x_7492_ = lean_nat_sub(v_n_7481_, v_one_7489_);
v_j_7493_ = lean_nat_sub(v___x_7492_, v___x_7491_);
lean_dec(v___x_7491_);
lean_dec(v___x_7492_);
v_b_7494_ = lean_array_fget_borrowed(v_aa_7483_, v_j_7493_);
v___x_7495_ = lean_array_get_size(v_b_7494_);
v___x_7496_ = lean_nat_dec_lt(v_zero_7487_, v___x_7495_);
if (v___x_7496_ == 0)
{
lean_object* v___x_7497_; 
lean_dec(v_j_7493_);
v___x_7497_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7481_, v_aa_7483_, v_adjustResult_7482_, v_n_7484_, v_n_7490_, v_a_7486_);
return v___x_7497_;
}
else
{
uint8_t v___x_7498_; 
v___x_7498_ = lean_nat_dec_le(v___x_7495_, v___x_7495_);
if (v___x_7498_ == 0)
{
if (v___x_7496_ == 0)
{
lean_object* v___x_7499_; 
lean_dec(v_j_7493_);
v___x_7499_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7481_, v_aa_7483_, v_adjustResult_7482_, v_n_7484_, v_n_7490_, v_a_7486_);
return v___x_7499_;
}
else
{
size_t v___x_7500_; size_t v___x_7501_; lean_object* v___x_7502_; lean_object* v___x_7503_; 
v___x_7500_ = ((size_t)0ULL);
v___x_7501_ = lean_usize_of_nat(v___x_7495_);
lean_inc(v_adjustResult_7482_);
v___x_7502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7482_, v_j_7493_, v_b_7494_, v___x_7500_, v___x_7501_, v_a_7486_);
v___x_7503_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7481_, v_aa_7483_, v_adjustResult_7482_, v_n_7484_, v_n_7490_, v___x_7502_);
return v___x_7503_;
}
}
else
{
size_t v___x_7504_; size_t v___x_7505_; lean_object* v___x_7506_; lean_object* v___x_7507_; 
v___x_7504_ = ((size_t)0ULL);
v___x_7505_ = lean_usize_of_nat(v___x_7495_);
lean_inc(v_adjustResult_7482_);
v___x_7506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7482_, v_j_7493_, v_b_7494_, v___x_7504_, v___x_7505_, v_a_7486_);
v___x_7507_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7481_, v_aa_7483_, v_adjustResult_7482_, v_n_7484_, v_n_7490_, v___x_7506_);
return v___x_7507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7508_, lean_object* v_adjustResult_7509_, lean_object* v_aa_7510_, lean_object* v_n_7511_, lean_object* v_j_7512_, lean_object* v_a_7513_){
_start:
{
lean_object* v_res_7514_; 
v_res_7514_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7508_, v_adjustResult_7509_, v_aa_7510_, v_n_7511_, v_j_7512_, v_a_7513_);
lean_dec(v_j_7512_);
lean_dec(v_n_7511_);
lean_dec_ref(v_aa_7510_);
lean_dec(v_n_7508_);
return v_res_7514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7515_, lean_object* v_mr_7516_, lean_object* v_a_7517_){
_start:
{
lean_object* v_n_7518_; lean_object* v___x_7519_; 
v_n_7518_ = lean_array_get_size(v_mr_7516_);
v___x_7519_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7518_, v_adjustResult_7515_, v_mr_7516_, v_n_7518_, v_n_7518_, v_a_7517_);
return v___x_7519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7520_, lean_object* v_mr_7521_, lean_object* v_a_7522_){
_start:
{
lean_object* v_res_7523_; 
v_res_7523_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7520_, v_mr_7521_, v_a_7522_);
lean_dec_ref(v_mr_7521_);
return v_res_7523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7524_, lean_object* v_ext_7525_, lean_object* v_addEntry_7526_, lean_object* v_droppedKeys_7527_, lean_object* v_constantsPerTask_7528_, lean_object* v_droppedEntriesRef_7529_, lean_object* v_adjustResult_7530_, lean_object* v_ty_7531_, lean_object* v_a_7532_, lean_object* v_a_7533_, lean_object* v_a_7534_, lean_object* v_a_7535_){
_start:
{
lean_object* v___x_7537_; 
lean_inc_ref(v_ty_7531_);
v___x_7537_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7524_, v_ty_7531_, v_a_7532_, v_a_7533_, v_a_7534_, v_a_7535_);
if (lean_obj_tag(v___x_7537_) == 0)
{
lean_object* v_a_7538_; lean_object* v___x_7539_; 
v_a_7538_ = lean_ctor_get(v___x_7537_, 0);
lean_inc(v_a_7538_);
lean_dec_ref(v___x_7537_);
v___x_7539_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ext_7525_, v_addEntry_7526_, v_droppedKeys_7527_, v_constantsPerTask_7528_, v_droppedEntriesRef_7529_, v_ty_7531_, v_a_7532_, v_a_7533_, v_a_7534_, v_a_7535_);
if (lean_obj_tag(v___x_7539_) == 0)
{
lean_object* v_a_7540_; lean_object* v___x_7542_; uint8_t v_isShared_7543_; uint8_t v_isSharedCheck_7553_; 
v_a_7540_ = lean_ctor_get(v___x_7539_, 0);
v_isSharedCheck_7553_ = !lean_is_exclusive(v___x_7539_);
if (v_isSharedCheck_7553_ == 0)
{
v___x_7542_ = v___x_7539_;
v_isShared_7543_ = v_isSharedCheck_7553_;
goto v_resetjp_7541_;
}
else
{
lean_inc(v_a_7540_);
lean_dec(v___x_7539_);
v___x_7542_ = lean_box(0);
v_isShared_7543_ = v_isSharedCheck_7553_;
goto v_resetjp_7541_;
}
v_resetjp_7541_:
{
lean_object* v___x_7544_; lean_object* v___x_7545_; lean_object* v___x_7546_; lean_object* v___x_7547_; lean_object* v___x_7548_; lean_object* v___x_7549_; lean_object* v___x_7551_; 
v___x_7544_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7538_);
v___x_7545_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7540_);
v___x_7546_ = lean_nat_add(v___x_7544_, v___x_7545_);
lean_dec(v___x_7545_);
lean_dec(v___x_7544_);
v___x_7547_ = lean_mk_empty_array_with_capacity(v___x_7546_);
lean_dec(v___x_7546_);
lean_inc(v_adjustResult_7530_);
v___x_7548_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7530_, v_a_7538_, v___x_7547_);
lean_dec(v_a_7538_);
v___x_7549_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7530_, v_a_7540_, v___x_7548_);
lean_dec(v_a_7540_);
if (v_isShared_7543_ == 0)
{
lean_ctor_set(v___x_7542_, 0, v___x_7549_);
v___x_7551_ = v___x_7542_;
goto v_reusejp_7550_;
}
else
{
lean_object* v_reuseFailAlloc_7552_; 
v_reuseFailAlloc_7552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7552_, 0, v___x_7549_);
v___x_7551_ = v_reuseFailAlloc_7552_;
goto v_reusejp_7550_;
}
v_reusejp_7550_:
{
return v___x_7551_;
}
}
}
else
{
lean_object* v_a_7554_; lean_object* v___x_7556_; uint8_t v_isShared_7557_; uint8_t v_isSharedCheck_7561_; 
lean_dec(v_a_7538_);
lean_dec(v_adjustResult_7530_);
v_a_7554_ = lean_ctor_get(v___x_7539_, 0);
v_isSharedCheck_7561_ = !lean_is_exclusive(v___x_7539_);
if (v_isSharedCheck_7561_ == 0)
{
v___x_7556_ = v___x_7539_;
v_isShared_7557_ = v_isSharedCheck_7561_;
goto v_resetjp_7555_;
}
else
{
lean_inc(v_a_7554_);
lean_dec(v___x_7539_);
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
else
{
lean_object* v_a_7562_; lean_object* v___x_7564_; uint8_t v_isShared_7565_; uint8_t v_isSharedCheck_7569_; 
lean_dec_ref(v_ty_7531_);
lean_dec(v_adjustResult_7530_);
lean_dec(v_droppedEntriesRef_7529_);
lean_dec(v_constantsPerTask_7528_);
lean_dec(v_droppedKeys_7527_);
lean_dec_ref(v_addEntry_7526_);
v_a_7562_ = lean_ctor_get(v___x_7537_, 0);
v_isSharedCheck_7569_ = !lean_is_exclusive(v___x_7537_);
if (v_isSharedCheck_7569_ == 0)
{
v___x_7564_ = v___x_7537_;
v_isShared_7565_ = v_isSharedCheck_7569_;
goto v_resetjp_7563_;
}
else
{
lean_inc(v_a_7562_);
lean_dec(v___x_7537_);
v___x_7564_ = lean_box(0);
v_isShared_7565_ = v_isSharedCheck_7569_;
goto v_resetjp_7563_;
}
v_resetjp_7563_:
{
lean_object* v___x_7567_; 
if (v_isShared_7565_ == 0)
{
v___x_7567_ = v___x_7564_;
goto v_reusejp_7566_;
}
else
{
lean_object* v_reuseFailAlloc_7568_; 
v_reuseFailAlloc_7568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7568_, 0, v_a_7562_);
v___x_7567_ = v_reuseFailAlloc_7568_;
goto v_reusejp_7566_;
}
v_reusejp_7566_:
{
return v___x_7567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7570_, lean_object* v_ext_7571_, lean_object* v_addEntry_7572_, lean_object* v_droppedKeys_7573_, lean_object* v_constantsPerTask_7574_, lean_object* v_droppedEntriesRef_7575_, lean_object* v_adjustResult_7576_, lean_object* v_ty_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_, lean_object* v_a_7580_, lean_object* v_a_7581_, lean_object* v_a_7582_){
_start:
{
lean_object* v_res_7583_; 
v_res_7583_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7570_, v_ext_7571_, v_addEntry_7572_, v_droppedKeys_7573_, v_constantsPerTask_7574_, v_droppedEntriesRef_7575_, v_adjustResult_7576_, v_ty_7577_, v_a_7578_, v_a_7579_, v_a_7580_, v_a_7581_);
lean_dec(v_a_7581_);
lean_dec_ref(v_a_7580_);
lean_dec(v_a_7579_);
lean_dec_ref(v_a_7578_);
lean_dec_ref(v_ext_7571_);
return v_res_7583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7584_, lean_object* v_00_u03b2_7585_, lean_object* v_moduleTreeRef_7586_, lean_object* v_ext_7587_, lean_object* v_addEntry_7588_, lean_object* v_droppedKeys_7589_, lean_object* v_constantsPerTask_7590_, lean_object* v_droppedEntriesRef_7591_, lean_object* v_adjustResult_7592_, lean_object* v_ty_7593_, lean_object* v_a_7594_, lean_object* v_a_7595_, lean_object* v_a_7596_, lean_object* v_a_7597_){
_start:
{
lean_object* v___x_7599_; 
v___x_7599_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7586_, v_ext_7587_, v_addEntry_7588_, v_droppedKeys_7589_, v_constantsPerTask_7590_, v_droppedEntriesRef_7591_, v_adjustResult_7592_, v_ty_7593_, v_a_7594_, v_a_7595_, v_a_7596_, v_a_7597_);
return v___x_7599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7600_, lean_object* v_00_u03b2_7601_, lean_object* v_moduleTreeRef_7602_, lean_object* v_ext_7603_, lean_object* v_addEntry_7604_, lean_object* v_droppedKeys_7605_, lean_object* v_constantsPerTask_7606_, lean_object* v_droppedEntriesRef_7607_, lean_object* v_adjustResult_7608_, lean_object* v_ty_7609_, lean_object* v_a_7610_, lean_object* v_a_7611_, lean_object* v_a_7612_, lean_object* v_a_7613_, lean_object* v_a_7614_){
_start:
{
lean_object* v_res_7615_; 
v_res_7615_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7600_, v_00_u03b2_7601_, v_moduleTreeRef_7602_, v_ext_7603_, v_addEntry_7604_, v_droppedKeys_7605_, v_constantsPerTask_7606_, v_droppedEntriesRef_7607_, v_adjustResult_7608_, v_ty_7609_, v_a_7610_, v_a_7611_, v_a_7612_, v_a_7613_);
lean_dec(v_a_7613_);
lean_dec_ref(v_a_7612_);
lean_dec(v_a_7611_);
lean_dec_ref(v_a_7610_);
lean_dec_ref(v_ext_7603_);
return v_res_7615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7616_, lean_object* v_00_u03b2_7617_, lean_object* v_adjustResult_7618_, lean_object* v_mr_7619_, lean_object* v_a_7620_){
_start:
{
lean_object* v___x_7621_; 
v___x_7621_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7618_, v_mr_7619_, v_a_7620_);
return v___x_7621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7622_, lean_object* v_00_u03b2_7623_, lean_object* v_adjustResult_7624_, lean_object* v_mr_7625_, lean_object* v_a_7626_){
_start:
{
lean_object* v_res_7627_; 
v_res_7627_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7622_, v_00_u03b2_7623_, v_adjustResult_7624_, v_mr_7625_, v_a_7626_);
lean_dec_ref(v_mr_7625_);
return v_res_7627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7628_, lean_object* v_00_u03b2_7629_, lean_object* v_adjustResult_7630_, lean_object* v_j_7631_, size_t v_sz_7632_, size_t v_i_7633_, lean_object* v_bs_7634_){
_start:
{
lean_object* v___x_7635_; 
v___x_7635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7630_, v_j_7631_, v_sz_7632_, v_i_7633_, v_bs_7634_);
return v___x_7635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7636_, lean_object* v_00_u03b2_7637_, lean_object* v_adjustResult_7638_, lean_object* v_j_7639_, lean_object* v_sz_7640_, lean_object* v_i_7641_, lean_object* v_bs_7642_){
_start:
{
size_t v_sz_boxed_7643_; size_t v_i_boxed_7644_; lean_object* v_res_7645_; 
v_sz_boxed_7643_ = lean_unbox_usize(v_sz_7640_);
lean_dec(v_sz_7640_);
v_i_boxed_7644_ = lean_unbox_usize(v_i_7641_);
lean_dec(v_i_7641_);
v_res_7645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7636_, v_00_u03b2_7637_, v_adjustResult_7638_, v_j_7639_, v_sz_boxed_7643_, v_i_boxed_7644_, v_bs_7642_);
return v_res_7645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7646_, lean_object* v_00_u03b2_7647_, lean_object* v_adjustResult_7648_, lean_object* v_j_7649_, lean_object* v_as_7650_, size_t v_i_7651_, size_t v_stop_7652_, lean_object* v_b_7653_){
_start:
{
lean_object* v___x_7654_; 
v___x_7654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7648_, v_j_7649_, v_as_7650_, v_i_7651_, v_stop_7652_, v_b_7653_);
return v___x_7654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7655_, lean_object* v_00_u03b2_7656_, lean_object* v_adjustResult_7657_, lean_object* v_j_7658_, lean_object* v_as_7659_, lean_object* v_i_7660_, lean_object* v_stop_7661_, lean_object* v_b_7662_){
_start:
{
size_t v_i_boxed_7663_; size_t v_stop_boxed_7664_; lean_object* v_res_7665_; 
v_i_boxed_7663_ = lean_unbox_usize(v_i_7660_);
lean_dec(v_i_7660_);
v_stop_boxed_7664_ = lean_unbox_usize(v_stop_7661_);
lean_dec(v_stop_7661_);
v_res_7665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7655_, v_00_u03b2_7656_, v_adjustResult_7657_, v_j_7658_, v_as_7659_, v_i_boxed_7663_, v_stop_boxed_7664_, v_b_7662_);
lean_dec_ref(v_as_7659_);
return v_res_7665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7666_, lean_object* v_n_7667_, lean_object* v_00_u03b1_7668_, lean_object* v_adjustResult_7669_, lean_object* v_aa_7670_, lean_object* v_n_7671_, lean_object* v_j_7672_, lean_object* v_a_7673_, lean_object* v_a_7674_){
_start:
{
lean_object* v___x_7675_; 
v___x_7675_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7667_, v_adjustResult_7669_, v_aa_7670_, v_n_7671_, v_j_7672_, v_a_7674_);
return v___x_7675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7676_, lean_object* v_n_7677_, lean_object* v_00_u03b1_7678_, lean_object* v_adjustResult_7679_, lean_object* v_aa_7680_, lean_object* v_n_7681_, lean_object* v_j_7682_, lean_object* v_a_7683_, lean_object* v_a_7684_){
_start:
{
lean_object* v_res_7685_; 
v_res_7685_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7676_, v_n_7677_, v_00_u03b1_7678_, v_adjustResult_7679_, v_aa_7680_, v_n_7681_, v_j_7682_, v_a_7683_, v_a_7684_);
lean_dec(v_j_7682_);
lean_dec(v_n_7681_);
lean_dec_ref(v_aa_7680_);
lean_dec(v_n_7677_);
return v_res_7685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7686_, lean_object* v_n_7687_, lean_object* v_00_u03b1_7688_, lean_object* v_aa_7689_, lean_object* v_adjustResult_7690_, lean_object* v_n_7691_, lean_object* v_j_7692_, lean_object* v_a_7693_, lean_object* v_a_7694_){
_start:
{
lean_object* v___x_7695_; 
v___x_7695_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7687_, v_aa_7689_, v_adjustResult_7690_, v_n_7691_, v_j_7692_, v_a_7694_);
return v___x_7695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7696_, lean_object* v_n_7697_, lean_object* v_00_u03b1_7698_, lean_object* v_aa_7699_, lean_object* v_adjustResult_7700_, lean_object* v_n_7701_, lean_object* v_j_7702_, lean_object* v_a_7703_, lean_object* v_a_7704_){
_start:
{
lean_object* v_res_7705_; 
v_res_7705_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7696_, v_n_7697_, v_00_u03b1_7698_, v_aa_7699_, v_adjustResult_7700_, v_n_7701_, v_j_7702_, v_a_7703_, v_a_7704_);
lean_dec(v_n_7701_);
lean_dec_ref(v_aa_7699_);
lean_dec(v_n_7697_);
return v_res_7705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7706_, lean_object* v_v_7707_){
_start:
{
lean_inc(v_v_7707_);
return v_v_7707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7708_, lean_object* v_v_7709_){
_start:
{
lean_object* v_res_7710_; 
v_res_7710_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7708_, v_v_7709_);
lean_dec(v_v_7709_);
lean_dec(v_x_7708_);
return v_res_7710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ext_7712_, lean_object* v_addEntry_7713_, lean_object* v_droppedKeys_7714_, lean_object* v_constantsPerTask_7715_, lean_object* v_droppedEntriesRef_7716_, lean_object* v_ty_7717_, lean_object* v_a_7718_, lean_object* v_a_7719_, lean_object* v_a_7720_, lean_object* v_a_7721_){
_start:
{
lean_object* v___x_7723_; 
lean_inc(v_droppedEntriesRef_7716_);
lean_inc(v_droppedKeys_7714_);
lean_inc_ref(v_addEntry_7713_);
v___x_7723_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7713_, v_droppedKeys_7714_, v_droppedEntriesRef_7716_, v_a_7718_, v_a_7719_, v_a_7720_, v_a_7721_);
if (lean_obj_tag(v___x_7723_) == 0)
{
lean_object* v_a_7724_; lean_object* v___f_7725_; lean_object* v___x_7726_; 
v_a_7724_ = lean_ctor_get(v___x_7723_, 0);
lean_inc(v_a_7724_);
lean_dec_ref(v___x_7723_);
v___f_7725_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7726_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7724_, v_ext_7712_, v_addEntry_7713_, v_droppedKeys_7714_, v_constantsPerTask_7715_, v_droppedEntriesRef_7716_, v___f_7725_, v_ty_7717_, v_a_7718_, v_a_7719_, v_a_7720_, v_a_7721_);
return v___x_7726_;
}
else
{
lean_object* v_a_7727_; lean_object* v___x_7729_; uint8_t v_isShared_7730_; uint8_t v_isSharedCheck_7734_; 
lean_dec_ref(v_ty_7717_);
lean_dec(v_droppedEntriesRef_7716_);
lean_dec(v_constantsPerTask_7715_);
lean_dec(v_droppedKeys_7714_);
lean_dec_ref(v_addEntry_7713_);
v_a_7727_ = lean_ctor_get(v___x_7723_, 0);
v_isSharedCheck_7734_ = !lean_is_exclusive(v___x_7723_);
if (v_isSharedCheck_7734_ == 0)
{
v___x_7729_ = v___x_7723_;
v_isShared_7730_ = v_isSharedCheck_7734_;
goto v_resetjp_7728_;
}
else
{
lean_inc(v_a_7727_);
lean_dec(v___x_7723_);
v___x_7729_ = lean_box(0);
v_isShared_7730_ = v_isSharedCheck_7734_;
goto v_resetjp_7728_;
}
v_resetjp_7728_:
{
lean_object* v___x_7732_; 
if (v_isShared_7730_ == 0)
{
v___x_7732_ = v___x_7729_;
goto v_reusejp_7731_;
}
else
{
lean_object* v_reuseFailAlloc_7733_; 
v_reuseFailAlloc_7733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7733_, 0, v_a_7727_);
v___x_7732_ = v_reuseFailAlloc_7733_;
goto v_reusejp_7731_;
}
v_reusejp_7731_:
{
return v___x_7732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ext_7735_, lean_object* v_addEntry_7736_, lean_object* v_droppedKeys_7737_, lean_object* v_constantsPerTask_7738_, lean_object* v_droppedEntriesRef_7739_, lean_object* v_ty_7740_, lean_object* v_a_7741_, lean_object* v_a_7742_, lean_object* v_a_7743_, lean_object* v_a_7744_, lean_object* v_a_7745_){
_start:
{
lean_object* v_res_7746_; 
v_res_7746_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ext_7735_, v_addEntry_7736_, v_droppedKeys_7737_, v_constantsPerTask_7738_, v_droppedEntriesRef_7739_, v_ty_7740_, v_a_7741_, v_a_7742_, v_a_7743_, v_a_7744_);
lean_dec(v_a_7744_);
lean_dec_ref(v_a_7743_);
lean_dec(v_a_7742_);
lean_dec_ref(v_a_7741_);
lean_dec_ref(v_ext_7735_);
return v_res_7746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7747_, lean_object* v_ext_7748_, lean_object* v_addEntry_7749_, lean_object* v_droppedKeys_7750_, lean_object* v_constantsPerTask_7751_, lean_object* v_droppedEntriesRef_7752_, lean_object* v_ty_7753_, lean_object* v_a_7754_, lean_object* v_a_7755_, lean_object* v_a_7756_, lean_object* v_a_7757_){
_start:
{
lean_object* v___x_7759_; 
v___x_7759_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ext_7748_, v_addEntry_7749_, v_droppedKeys_7750_, v_constantsPerTask_7751_, v_droppedEntriesRef_7752_, v_ty_7753_, v_a_7754_, v_a_7755_, v_a_7756_, v_a_7757_);
return v___x_7759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7760_, lean_object* v_ext_7761_, lean_object* v_addEntry_7762_, lean_object* v_droppedKeys_7763_, lean_object* v_constantsPerTask_7764_, lean_object* v_droppedEntriesRef_7765_, lean_object* v_ty_7766_, lean_object* v_a_7767_, lean_object* v_a_7768_, lean_object* v_a_7769_, lean_object* v_a_7770_, lean_object* v_a_7771_){
_start:
{
lean_object* v_res_7772_; 
v_res_7772_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7760_, v_ext_7761_, v_addEntry_7762_, v_droppedKeys_7763_, v_constantsPerTask_7764_, v_droppedEntriesRef_7765_, v_ty_7766_, v_a_7767_, v_a_7768_, v_a_7769_, v_a_7770_);
lean_dec(v_a_7770_);
lean_dec_ref(v_a_7769_);
lean_dec(v_a_7768_);
lean_dec_ref(v_a_7767_);
lean_dec_ref(v_ext_7761_);
return v_res_7772_;
}
}
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
