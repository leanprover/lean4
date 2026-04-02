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
lean_inc_ref_n(v_arg_416_, 2);
lean_dec_ref(v_x_408_);
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
lean_object* v___y_777_; lean_object* v_fileName_786_; lean_object* v_fileMap_787_; lean_object* v_options_788_; lean_object* v_currRecDepth_789_; lean_object* v_maxRecDepth_790_; lean_object* v_ref_791_; lean_object* v_currNamespace_792_; lean_object* v_openDecls_793_; lean_object* v_initHeartbeats_794_; lean_object* v_maxHeartbeats_795_; lean_object* v_quotContext_796_; lean_object* v_currMacroScope_797_; uint8_t v_diag_798_; lean_object* v_cancelTk_x3f_799_; uint8_t v_suppressElabErrors_800_; lean_object* v_inheritedTraceOptions_801_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_fileName_786_ = lean_ctor_get(v___y_773_, 0);
v_fileMap_787_ = lean_ctor_get(v___y_773_, 1);
v_options_788_ = lean_ctor_get(v___y_773_, 2);
v_currRecDepth_789_ = lean_ctor_get(v___y_773_, 3);
v_maxRecDepth_790_ = lean_ctor_get(v___y_773_, 4);
v_ref_791_ = lean_ctor_get(v___y_773_, 5);
v_currNamespace_792_ = lean_ctor_get(v___y_773_, 6);
v_openDecls_793_ = lean_ctor_get(v___y_773_, 7);
v_initHeartbeats_794_ = lean_ctor_get(v___y_773_, 8);
v_maxHeartbeats_795_ = lean_ctor_get(v___y_773_, 9);
v_quotContext_796_ = lean_ctor_get(v___y_773_, 10);
v_currMacroScope_797_ = lean_ctor_get(v___y_773_, 11);
v_diag_798_ = lean_ctor_get_uint8(v___y_773_, sizeof(void*)*14);
v_cancelTk_x3f_799_ = lean_ctor_get(v___y_773_, 12);
v_suppressElabErrors_800_ = lean_ctor_get_uint8(v___y_773_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_801_ = lean_ctor_get(v___y_773_, 13);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_nat_dec_eq(v_maxRecDepth_790_, v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; 
v___x_809_ = lean_nat_dec_eq(v_currRecDepth_789_, v_maxRecDepth_790_);
if (v___x_809_ == 0)
{
goto v___jp_802_;
}
else
{
lean_object* v___x_810_; 
lean_dec_ref(v_x_771_);
lean_inc(v_ref_791_);
v___x_810_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_791_);
v___y_777_ = v___x_810_;
goto v___jp_776_;
}
}
else
{
goto v___jp_802_;
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
v___jp_802_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_nat_add(v_currRecDepth_789_, v___x_803_);
lean_inc_ref(v_inheritedTraceOptions_801_);
lean_inc(v_cancelTk_x3f_799_);
lean_inc(v_currMacroScope_797_);
lean_inc(v_quotContext_796_);
lean_inc(v_maxHeartbeats_795_);
lean_inc(v_initHeartbeats_794_);
lean_inc(v_openDecls_793_);
lean_inc(v_currNamespace_792_);
lean_inc(v_ref_791_);
lean_inc(v_maxRecDepth_790_);
lean_inc_ref(v_options_788_);
lean_inc_ref(v_fileMap_787_);
lean_inc_ref(v_fileName_786_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v___x_819_; 
v___x_819_ = lean_box(0);
return v___x_819_;
}
else
{
lean_object* v_key_820_; lean_object* v_value_821_; lean_object* v_tail_822_; uint8_t v___x_823_; 
v_key_820_ = lean_ctor_get(v_x_818_, 0);
v_value_821_ = lean_ctor_get(v_x_818_, 1);
v_tail_822_ = lean_ctor_get(v_x_818_, 2);
v___x_823_ = l_Lean_ExprStructEq_beq(v_key_820_, v_a_817_);
if (v___x_823_ == 0)
{
v_x_818_ = v_tail_822_;
goto _start;
}
else
{
lean_object* v___x_825_; 
lean_inc(v_value_821_);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v_value_821_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_826_, lean_object* v_x_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_826_, v_x_827_);
lean_dec(v_x_827_);
lean_dec_ref(v_a_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(lean_object* v_m_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_buckets_831_; lean_object* v___x_832_; uint64_t v___x_833_; uint64_t v___x_834_; uint64_t v___x_835_; uint64_t v_fold_836_; uint64_t v___x_837_; uint64_t v___x_838_; uint64_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_buckets_831_ = lean_ctor_get(v_m_829_, 1);
v___x_832_ = lean_array_get_size(v_buckets_831_);
v___x_833_ = l_Lean_ExprStructEq_hash(v_a_830_);
v___x_834_ = 32ULL;
v___x_835_ = lean_uint64_shift_right(v___x_833_, v___x_834_);
v_fold_836_ = lean_uint64_xor(v___x_833_, v___x_835_);
v___x_837_ = 16ULL;
v___x_838_ = lean_uint64_shift_right(v_fold_836_, v___x_837_);
v___x_839_ = lean_uint64_xor(v_fold_836_, v___x_838_);
v___x_840_ = lean_uint64_to_usize(v___x_839_);
v___x_841_ = lean_usize_of_nat(v___x_832_);
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_sub(v___x_841_, v___x_842_);
v___x_844_ = lean_usize_land(v___x_840_, v___x_843_);
v___x_845_ = lean_array_uget_borrowed(v_buckets_831_, v___x_844_);
v___x_846_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_830_, v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_847_, v_a_848_);
lean_dec_ref(v_a_848_);
lean_dec_ref(v_m_847_);
return v_res_849_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
if (lean_obj_tag(v_x_851_) == 0)
{
uint8_t v___x_852_; 
v___x_852_ = 0;
return v___x_852_;
}
else
{
lean_object* v_key_853_; lean_object* v_tail_854_; uint8_t v___x_855_; 
v_key_853_ = lean_ctor_get(v_x_851_, 0);
v_tail_854_ = lean_ctor_get(v_x_851_, 2);
v___x_855_ = l_Lean_ExprStructEq_beq(v_key_853_, v_a_850_);
if (v___x_855_ == 0)
{
v_x_851_ = v_tail_854_;
goto _start;
}
else
{
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg(v_a_857_, v_x_858_);
lean_dec(v_x_858_);
lean_dec_ref(v_a_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
return v_x_861_;
}
else
{
lean_object* v_key_863_; lean_object* v_value_864_; lean_object* v_tail_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_888_; 
v_key_863_ = lean_ctor_get(v_x_862_, 0);
v_value_864_ = lean_ctor_get(v_x_862_, 1);
v_tail_865_ = lean_ctor_get(v_x_862_, 2);
v_isSharedCheck_888_ = !lean_is_exclusive(v_x_862_);
if (v_isSharedCheck_888_ == 0)
{
v___x_867_ = v_x_862_;
v_isShared_868_ = v_isSharedCheck_888_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_tail_865_);
lean_inc(v_value_864_);
lean_inc(v_key_863_);
lean_dec(v_x_862_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_888_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v_fold_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_869_ = lean_array_get_size(v_x_861_);
v___x_870_ = l_Lean_ExprStructEq_hash(v_key_863_);
v___x_871_ = 32ULL;
v___x_872_ = lean_uint64_shift_right(v___x_870_, v___x_871_);
v_fold_873_ = lean_uint64_xor(v___x_870_, v___x_872_);
v___x_874_ = 16ULL;
v___x_875_ = lean_uint64_shift_right(v_fold_873_, v___x_874_);
v___x_876_ = lean_uint64_xor(v_fold_873_, v___x_875_);
v___x_877_ = lean_uint64_to_usize(v___x_876_);
v___x_878_ = lean_usize_of_nat(v___x_869_);
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_sub(v___x_878_, v___x_879_);
v___x_881_ = lean_usize_land(v___x_877_, v___x_880_);
v___x_882_ = lean_array_uget_borrowed(v_x_861_, v___x_881_);
lean_inc(v___x_882_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 2, v___x_882_);
v___x_884_ = v___x_867_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_key_863_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_value_864_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v___x_882_);
v___x_884_ = v_reuseFailAlloc_887_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; 
v___x_885_ = lean_array_uset(v_x_861_, v___x_881_, v___x_884_);
v_x_861_ = v___x_885_;
v_x_862_ = v_tail_865_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_889_, lean_object* v_source_890_, lean_object* v_target_891_){
_start:
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_array_get_size(v_source_890_);
v___x_893_ = lean_nat_dec_lt(v_i_889_, v___x_892_);
if (v___x_893_ == 0)
{
lean_dec_ref(v_source_890_);
lean_dec(v_i_889_);
return v_target_891_;
}
else
{
lean_object* v_es_894_; lean_object* v___x_895_; lean_object* v_source_896_; lean_object* v_target_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_es_894_ = lean_array_fget(v_source_890_, v_i_889_);
v___x_895_ = lean_box(0);
v_source_896_ = lean_array_fset(v_source_890_, v_i_889_, v___x_895_);
v_target_897_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_891_, v_es_894_);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_i_889_, v___x_898_);
lean_dec(v_i_889_);
v_i_889_ = v___x_899_;
v_source_890_ = v_source_896_;
v_target_891_ = v_target_897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v_nbuckets_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_902_ = lean_array_get_size(v_data_901_);
v___x_903_ = lean_unsigned_to_nat(2u);
v_nbuckets_904_ = lean_nat_mul(v___x_902_, v___x_903_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_box(0);
v___x_907_ = lean_mk_array(v_nbuckets_904_, v___x_906_);
v___x_908_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_905_, v_data_901_, v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_909_, lean_object* v_b_910_, lean_object* v_x_911_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
lean_dec(v_b_910_);
lean_dec_ref(v_a_909_);
return v_x_911_;
}
else
{
lean_object* v_key_912_; lean_object* v_value_913_; lean_object* v_tail_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_926_; 
v_key_912_ = lean_ctor_get(v_x_911_, 0);
v_value_913_ = lean_ctor_get(v_x_911_, 1);
v_tail_914_ = lean_ctor_get(v_x_911_, 2);
v_isSharedCheck_926_ = !lean_is_exclusive(v_x_911_);
if (v_isSharedCheck_926_ == 0)
{
v___x_916_ = v_x_911_;
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_tail_914_);
lean_inc(v_value_913_);
lean_inc(v_key_912_);
lean_dec(v_x_911_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_ExprStructEq_beq(v_key_912_, v_a_909_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_a_909_, v_b_910_, v_tail_914_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 2, v___x_919_);
v___x_921_ = v___x_916_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_key_912_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_value_913_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
else
{
lean_object* v___x_924_; 
lean_dec(v_value_913_);
lean_dec(v_key_912_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v_b_910_);
lean_ctor_set(v___x_916_, 0, v_a_909_);
v___x_924_ = v___x_916_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_909_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_b_910_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_tail_914_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
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
v___x_949_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg(v_a_928_, v_bkt_948_);
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
v_val_960_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_953_);
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
v___x_969_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_a_928_, v_b_929_, v_bkt_948_);
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
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v___x_979_, v_e_976_, v_a_977_);
v___x_981_ = lean_st_ref_set(v_a_975_, v___x_980_);
v___x_982_ = lean_box(0);
return v___x_982_;
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
lean_object* v_v_1015_; lean_object* v___x_1016_; 
v_v_1015_ = lean_array_uget_borrowed(v_bs_1008_, v_i_1007_);
lean_inc(v_v_1015_);
lean_inc_ref(v_post_1005_);
lean_inc_ref(v_pre_1004_);
v___x_1016_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1004_, v_post_1005_, v_v_1015_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v_bs_x27_1019_; size_t v___x_1020_; size_t v___x_1021_; lean_object* v___x_1022_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = lean_unsigned_to_nat(0u);
v_bs_x27_1019_ = lean_array_uset(v_bs_1008_, v_i_1007_, v___x_1018_);
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_add(v_i_1007_, v___x_1020_);
v___x_1022_ = lean_array_uset(v_bs_x27_1019_, v_i_1007_, v_a_1017_);
v_i_1007_ = v___x_1021_;
v_bs_1008_ = v___x_1022_;
goto _start;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v_bs_1008_);
lean_dec_ref(v_post_1005_);
lean_dec_ref(v_pre_1004_);
v_a_1024_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1016_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1016_);
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
lean_dec_ref(v_x_1034_);
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
lean_dec_ref(v___x_1047_);
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
lean_dec_ref(v___x_1051_);
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
lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; uint8_t v___y_1077_; lean_object* v___y_1078_; uint8_t v___y_1079_; lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; uint8_t v___y_1106_; uint8_t v___y_1107_; lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Core_checkSystem(v___x_1063_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v___x_1115_; 
lean_dec_ref(v___x_1114_);
lean_inc_ref(v_pre_1064_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc_ref(v_e_1065_);
v___x_1115_ = lean_apply_4(v_pre_1064_, v_e_1065_, v___y_1068_, v___y_1069_, lean_box(0));
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1205_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1205_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1205_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___y_1121_; 
switch(lean_obj_tag(v_a_1116_))
{
case 0:
{
lean_object* v_e_1195_; lean_object* v___x_1197_; 
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_e_1065_);
lean_dec_ref(v_pre_1064_);
v_e_1195_ = lean_ctor_get(v_a_1116_, 0);
lean_inc_ref(v_e_1195_);
lean_dec_ref(v_a_1116_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v_e_1195_);
v___x_1197_ = v___x_1118_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_e_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
case 1:
{
lean_object* v_e_1199_; lean_object* v___x_1200_; 
lean_del_object(v___x_1118_);
lean_dec_ref(v_e_1065_);
v_e_1199_ = lean_ctor_get(v_a_1116_, 0);
lean_inc_ref(v_e_1199_);
lean_dec_ref(v_a_1116_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1200_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_e_1199_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1202_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v_a_1201_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1202_;
}
else
{
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1200_;
}
}
default: 
{
lean_object* v_e_x3f_1203_; 
lean_del_object(v___x_1118_);
v_e_x3f_1203_ = lean_ctor_get(v_a_1116_, 0);
lean_inc(v_e_x3f_1203_);
lean_dec_ref(v_a_1116_);
if (lean_obj_tag(v_e_x3f_1203_) == 0)
{
v___y_1121_ = v_e_1065_;
goto v___jp_1120_;
}
else
{
lean_object* v_val_1204_; 
lean_dec_ref(v_e_1065_);
v_val_1204_ = lean_ctor_get(v_e_x3f_1203_, 0);
lean_inc(v_val_1204_);
lean_dec_ref(v_e_x3f_1203_);
v___y_1121_ = v_val_1204_;
goto v___jp_1120_;
}
}
}
v___jp_1120_:
{
switch(lean_obj_tag(v___y_1121_))
{
case 7:
{
lean_object* v_binderName_1122_; lean_object* v_binderType_1123_; lean_object* v_body_1124_; uint8_t v_binderInfo_1125_; lean_object* v___x_1126_; 
v_binderName_1122_ = lean_ctor_get(v___y_1121_, 0);
lean_inc(v_binderName_1122_);
v_binderType_1123_ = lean_ctor_get(v___y_1121_, 1);
v_body_1124_ = lean_ctor_get(v___y_1121_, 2);
v_binderInfo_1125_ = lean_ctor_get_uint8(v___y_1121_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1123_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1126_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_binderType_1123_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref(v___x_1126_);
lean_inc_ref(v_body_1124_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1128_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_body_1124_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; size_t v___x_1130_; size_t v___x_1131_; uint8_t v___x_1132_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = lean_ptr_addr(v_binderType_1123_);
v___x_1131_ = lean_ptr_addr(v_a_1127_);
v___x_1132_ = lean_usize_dec_eq(v___x_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
v___y_1102_ = v_binderName_1122_;
v___y_1103_ = v_a_1127_;
v___y_1104_ = v_a_1129_;
v___y_1105_ = v___y_1121_;
v___y_1106_ = v_binderInfo_1125_;
v___y_1107_ = v___x_1132_;
goto v___jp_1101_;
}
else
{
size_t v___x_1133_; size_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1133_ = lean_ptr_addr(v_body_1124_);
v___x_1134_ = lean_ptr_addr(v_a_1129_);
v___x_1135_ = lean_usize_dec_eq(v___x_1133_, v___x_1134_);
v___y_1102_ = v_binderName_1122_;
v___y_1103_ = v_a_1127_;
v___y_1104_ = v_a_1129_;
v___y_1105_ = v___y_1121_;
v___y_1106_ = v_binderInfo_1125_;
v___y_1107_ = v___x_1135_;
goto v___jp_1101_;
}
}
else
{
lean_dec(v_a_1127_);
lean_dec_ref(v___y_1121_);
lean_dec(v_binderName_1122_);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1128_;
}
}
else
{
lean_dec_ref(v___y_1121_);
lean_dec(v_binderName_1122_);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1126_;
}
}
case 6:
{
lean_object* v_binderName_1136_; lean_object* v_binderType_1137_; lean_object* v_body_1138_; uint8_t v_binderInfo_1139_; lean_object* v___x_1140_; 
v_binderName_1136_ = lean_ctor_get(v___y_1121_, 0);
lean_inc(v_binderName_1136_);
v_binderType_1137_ = lean_ctor_get(v___y_1121_, 1);
v_body_1138_ = lean_ctor_get(v___y_1121_, 2);
v_binderInfo_1139_ = lean_ctor_get_uint8(v___y_1121_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_1137_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1140_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_binderType_1137_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref(v___x_1140_);
lean_inc_ref(v_body_1138_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1142_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_body_1138_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; size_t v___x_1144_; size_t v___x_1145_; uint8_t v___x_1146_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref(v___x_1142_);
v___x_1144_ = lean_ptr_addr(v_binderType_1137_);
v___x_1145_ = lean_ptr_addr(v_a_1141_);
v___x_1146_ = lean_usize_dec_eq(v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
v___y_1089_ = v_a_1143_;
v___y_1090_ = v___y_1121_;
v___y_1091_ = v_binderInfo_1139_;
v___y_1092_ = v_a_1141_;
v___y_1093_ = v_binderName_1136_;
v___y_1094_ = v___x_1146_;
goto v___jp_1088_;
}
else
{
size_t v___x_1147_; size_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = lean_ptr_addr(v_body_1138_);
v___x_1148_ = lean_ptr_addr(v_a_1143_);
v___x_1149_ = lean_usize_dec_eq(v___x_1147_, v___x_1148_);
v___y_1089_ = v_a_1143_;
v___y_1090_ = v___y_1121_;
v___y_1091_ = v_binderInfo_1139_;
v___y_1092_ = v_a_1141_;
v___y_1093_ = v_binderName_1136_;
v___y_1094_ = v___x_1149_;
goto v___jp_1088_;
}
}
else
{
lean_dec(v_a_1141_);
lean_dec_ref(v___y_1121_);
lean_dec(v_binderName_1136_);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1142_;
}
}
else
{
lean_dec(v_binderName_1136_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1140_;
}
}
case 8:
{
lean_object* v_declName_1150_; lean_object* v_type_1151_; lean_object* v_value_1152_; lean_object* v_body_1153_; uint8_t v_nondep_1154_; lean_object* v___x_1155_; 
v_declName_1150_ = lean_ctor_get(v___y_1121_, 0);
lean_inc(v_declName_1150_);
v_type_1151_ = lean_ctor_get(v___y_1121_, 1);
v_value_1152_ = lean_ctor_get(v___y_1121_, 2);
v_body_1153_ = lean_ctor_get(v___y_1121_, 3);
lean_inc_ref(v_body_1153_);
v_nondep_1154_ = lean_ctor_get_uint8(v___y_1121_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_1151_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1155_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_type_1151_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref(v___x_1155_);
lean_inc_ref(v_value_1152_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1157_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_value_1152_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1159_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref(v___x_1157_);
lean_inc_ref(v_body_1153_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1159_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_body_1153_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; size_t v___x_1161_; size_t v___x_1162_; uint8_t v___x_1163_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref(v___x_1159_);
v___x_1161_ = lean_ptr_addr(v_type_1151_);
v___x_1162_ = lean_ptr_addr(v_a_1156_);
v___x_1163_ = lean_usize_dec_eq(v___x_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
v___y_1072_ = v_a_1160_;
v___y_1073_ = v_a_1158_;
v___y_1074_ = v_declName_1150_;
v___y_1075_ = v___y_1121_;
v___y_1076_ = v_a_1156_;
v___y_1077_ = v_nondep_1154_;
v___y_1078_ = v_body_1153_;
v___y_1079_ = v___x_1163_;
goto v___jp_1071_;
}
else
{
size_t v___x_1164_; size_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_ptr_addr(v_value_1152_);
v___x_1165_ = lean_ptr_addr(v_a_1158_);
v___x_1166_ = lean_usize_dec_eq(v___x_1164_, v___x_1165_);
v___y_1072_ = v_a_1160_;
v___y_1073_ = v_a_1158_;
v___y_1074_ = v_declName_1150_;
v___y_1075_ = v___y_1121_;
v___y_1076_ = v_a_1156_;
v___y_1077_ = v_nondep_1154_;
v___y_1078_ = v_body_1153_;
v___y_1079_ = v___x_1166_;
goto v___jp_1071_;
}
}
else
{
lean_dec(v_a_1158_);
lean_dec(v_a_1156_);
lean_dec_ref(v_body_1153_);
lean_dec_ref(v___y_1121_);
lean_dec(v_declName_1150_);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1159_;
}
}
else
{
lean_dec(v_a_1156_);
lean_dec_ref(v_body_1153_);
lean_dec_ref(v___y_1121_);
lean_dec(v_declName_1150_);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1157_;
}
}
else
{
lean_dec_ref(v_body_1153_);
lean_dec_ref(v___y_1121_);
lean_dec(v_declName_1150_);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1155_;
}
}
case 5:
{
lean_object* v_dummy_1167_; lean_object* v_nargs_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_dummy_1167_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
v_nargs_1168_ = l_Lean_Expr_getAppNumArgs(v___y_1121_);
lean_inc(v_nargs_1168_);
v___x_1169_ = lean_mk_array(v_nargs_1168_, v_dummy_1167_);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_nat_sub(v_nargs_1168_, v___x_1170_);
lean_dec(v_nargs_1168_);
v___x_1172_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1064_, v_post_1066_, v___y_1121_, v___x_1169_, v___x_1171_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1172_;
}
case 10:
{
lean_object* v_data_1173_; lean_object* v_expr_1174_; lean_object* v___x_1175_; 
v_data_1173_ = lean_ctor_get(v___y_1121_, 0);
v_expr_1174_ = lean_ctor_get(v___y_1121_, 1);
lean_inc_ref(v_expr_1174_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1175_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_expr_1174_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; size_t v___x_1177_; size_t v___x_1178_; uint8_t v___x_1179_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref(v___x_1175_);
v___x_1177_ = lean_ptr_addr(v_expr_1174_);
v___x_1178_ = lean_ptr_addr(v_a_1176_);
v___x_1179_ = lean_usize_dec_eq(v___x_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_inc(v_data_1173_);
lean_dec_ref(v___y_1121_);
v___x_1180_ = l_Lean_Expr_mdata___override(v_data_1173_, v_a_1176_);
v___x_1181_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1180_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1181_;
}
else
{
lean_object* v___x_1182_; 
lean_dec(v_a_1176_);
v___x_1182_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1121_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1182_;
}
}
else
{
lean_dec_ref(v___y_1121_);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1175_;
}
}
case 11:
{
lean_object* v_typeName_1183_; lean_object* v_idx_1184_; lean_object* v_struct_1185_; lean_object* v___x_1186_; 
v_typeName_1183_ = lean_ctor_get(v___y_1121_, 0);
v_idx_1184_ = lean_ctor_get(v___y_1121_, 1);
v_struct_1185_ = lean_ctor_get(v___y_1121_, 2);
lean_inc_ref(v_struct_1185_);
lean_inc_ref(v_post_1066_);
lean_inc_ref(v_pre_1064_);
v___x_1186_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1064_, v_post_1066_, v_struct_1185_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; size_t v___x_1188_; size_t v___x_1189_; uint8_t v___x_1190_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = lean_ptr_addr(v_struct_1185_);
v___x_1189_ = lean_ptr_addr(v_a_1187_);
v___x_1190_ = lean_usize_dec_eq(v___x_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_inc(v_idx_1184_);
lean_inc(v_typeName_1183_);
lean_dec_ref(v___y_1121_);
v___x_1191_ = l_Lean_Expr_proj___override(v_typeName_1183_, v_idx_1184_, v_a_1187_);
v___x_1192_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1191_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; 
lean_dec(v_a_1187_);
v___x_1193_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1121_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1193_;
}
}
else
{
lean_dec_ref(v___y_1121_);
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_pre_1064_);
return v___x_1186_;
}
}
default: 
{
lean_object* v___x_1194_; 
v___x_1194_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1121_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1194_;
}
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_e_1065_);
lean_dec_ref(v_pre_1064_);
v_a_1206_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1115_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1115_);
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
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_post_1066_);
lean_dec_ref(v_e_1065_);
lean_dec_ref(v_pre_1064_);
v_a_1214_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1114_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1114_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
v___jp_1071_:
{
if (v___y_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v___y_1078_);
lean_dec_ref(v___y_1075_);
v___x_1080_ = l_Lean_Expr_letE___override(v___y_1074_, v___y_1076_, v___y_1073_, v___y_1072_, v___y_1077_);
v___x_1081_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1080_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1081_;
}
else
{
size_t v___x_1082_; size_t v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = lean_ptr_addr(v___y_1078_);
lean_dec_ref(v___y_1078_);
v___x_1083_ = lean_ptr_addr(v___y_1072_);
v___x_1084_ = lean_usize_dec_eq(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec_ref(v___y_1075_);
v___x_1085_ = l_Lean_Expr_letE___override(v___y_1074_, v___y_1076_, v___y_1073_, v___y_1072_, v___y_1077_);
v___x_1086_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1085_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; 
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec_ref(v___y_1072_);
v___x_1087_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1075_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1087_;
}
}
}
v___jp_1088_:
{
if (v___y_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec_ref(v___y_1090_);
v___x_1095_ = l_Lean_Expr_lam___override(v___y_1093_, v___y_1092_, v___y_1089_, v___y_1091_);
v___x_1096_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1095_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1096_;
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_instBEqBinderInfo_beq(v___y_1091_, v___y_1091_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_dec_ref(v___y_1090_);
v___x_1098_ = l_Lean_Expr_lam___override(v___y_1093_, v___y_1092_, v___y_1089_, v___y_1091_);
v___x_1099_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1098_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; 
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___y_1089_);
v___x_1100_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1090_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1100_;
}
}
}
v___jp_1101_:
{
if (v___y_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec_ref(v___y_1105_);
v___x_1108_ = l_Lean_Expr_forallE___override(v___y_1102_, v___y_1103_, v___y_1104_, v___y_1106_);
v___x_1109_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1108_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1109_;
}
else
{
uint8_t v___x_1110_; 
v___x_1110_ = l_Lean_instBEqBinderInfo_beq(v___y_1106_, v___y_1106_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec_ref(v___y_1105_);
v___x_1111_ = l_Lean_Expr_forallE___override(v___y_1102_, v___y_1103_, v___y_1104_, v___y_1106_);
v___x_1112_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___x_1111_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; 
lean_dec_ref(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
v___x_1113_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1064_, v_post_1066_, v___y_1105_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1222_, lean_object* v_pre_1223_, lean_object* v_e_1224_, lean_object* v_post_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1(v___x_1222_, v_pre_1223_, v_e_1224_, v_post_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(lean_object* v_pre_1231_, lean_object* v_post_1232_, lean_object* v_e_1233_, lean_object* v_a_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_inc(v_a_1234_);
v___x_1238_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1238_, 0, lean_box(0));
lean_closure_set(v___x_1238_, 1, lean_box(0));
lean_closure_set(v___x_1238_, 2, v_a_1234_);
v___x_1239_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___x_1238_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1271_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1271_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1271_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_a_1240_, v_e_1233_);
lean_dec(v_a_1240_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; 
lean_del_object(v___x_1242_);
v___x_1245_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_1233_);
v___f_1246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1246_, 0, v___x_1245_);
lean_closure_set(v___f_1246_, 1, v_pre_1231_);
lean_closure_set(v___f_1246_, 2, v_e_1233_);
lean_closure_set(v___f_1246_, 3, v_post_1232_);
v___x_1247_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1246_, v_a_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc_n(v_a_1248_, 2);
lean_dec_ref(v___x_1247_);
lean_inc(v_a_1234_);
v___f_1249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1249_, 0, v_a_1234_);
lean_closure_set(v___f_1249_, 1, v_e_1233_);
lean_closure_set(v___f_1249_, 2, v_a_1248_);
v___x_1250_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__0(lean_box(0), v___f_1249_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1250_, 0);
lean_dec(v_unused_1258_);
v___x_1252_ = v___x_1250_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_dec(v___x_1250_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v_a_1248_);
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1248_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1248_);
v_a_1259_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1250_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1250_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
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
lean_dec_ref(v_e_1233_);
return v___x_1247_;
}
}
else
{
lean_object* v_val_1267_; lean_object* v___x_1269_; 
lean_dec_ref(v_e_1233_);
lean_dec_ref(v_post_1232_);
lean_dec_ref(v_pre_1231_);
v_val_1267_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_val_1267_);
lean_dec_ref(v___x_1244_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v_val_1267_);
v___x_1269_ = v___x_1242_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_val_1267_);
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
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_e_1233_);
lean_dec_ref(v_post_1232_);
lean_dec_ref(v_pre_1231_);
v_a_1272_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1239_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1239_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(lean_object* v_pre_1280_, lean_object* v_post_1281_, lean_object* v_e_1282_, lean_object* v_a_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
lean_inc_ref(v_post_1281_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc_ref(v_e_1282_);
v___x_1287_ = lean_apply_4(v_post_1281_, v_e_1282_, v___y_1284_, v___y_1285_, lean_box(0));
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1306_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1306_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1306_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
switch(lean_obj_tag(v_a_1288_))
{
case 0:
{
lean_object* v_e_1292_; lean_object* v___x_1294_; 
lean_dec_ref(v_e_1282_);
lean_dec_ref(v_post_1281_);
lean_dec_ref(v_pre_1280_);
v_e_1292_ = lean_ctor_get(v_a_1288_, 0);
lean_inc_ref(v_e_1292_);
lean_dec_ref(v_a_1288_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v_e_1292_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_e_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
case 1:
{
lean_object* v_e_1296_; lean_object* v___x_1297_; 
lean_del_object(v___x_1290_);
lean_dec_ref(v_e_1282_);
v_e_1296_ = lean_ctor_get(v_a_1288_, 0);
lean_inc_ref(v_e_1296_);
lean_dec_ref(v_a_1288_);
v___x_1297_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1280_, v_post_1281_, v_e_1296_, v_a_1283_, v___y_1284_, v___y_1285_);
return v___x_1297_;
}
default: 
{
lean_object* v_e_x3f_1298_; 
lean_dec_ref(v_post_1281_);
lean_dec_ref(v_pre_1280_);
v_e_x3f_1298_ = lean_ctor_get(v_a_1288_, 0);
lean_inc(v_e_x3f_1298_);
lean_dec_ref(v_a_1288_);
if (lean_obj_tag(v_e_x3f_1298_) == 0)
{
lean_object* v___x_1300_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v_e_1282_);
v___x_1300_ = v___x_1290_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_e_1282_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
else
{
lean_object* v_val_1302_; lean_object* v___x_1304_; 
lean_dec_ref(v_e_1282_);
v_val_1302_ = lean_ctor_get(v_e_x3f_1298_, 0);
lean_inc(v_val_1302_);
lean_dec_ref(v_e_x3f_1298_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v_val_1302_);
v___x_1304_ = v___x_1290_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_val_1302_);
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
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref(v_e_1282_);
lean_dec_ref(v_post_1281_);
lean_dec_ref(v_pre_1280_);
v_a_1307_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1287_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1287_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1315_, lean_object* v_post_1316_, lean_object* v_e_1317_, lean_object* v_a_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__2(v_pre_1315_, v_post_1316_, v_e_1317_, v_a_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v_a_1318_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1323_, lean_object* v_post_1324_, lean_object* v_sz_1325_, lean_object* v_i_1326_, lean_object* v_bs_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
size_t v_sz_boxed_1332_; size_t v_i_boxed_1333_; lean_object* v_res_1334_; 
v_sz_boxed_1332_ = lean_unbox_usize(v_sz_1325_);
lean_dec(v_sz_1325_);
v_i_boxed_1333_ = lean_unbox_usize(v_i_1326_);
lean_dec(v_i_1326_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__1(v_pre_1323_, v_post_1324_, v_sz_boxed_1332_, v_i_boxed_1333_, v_bs_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_1335_, lean_object* v_post_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__4(v_pre_1335_, v_post_1336_, v_x_1337_, v_x_1338_, v_x_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___boxed(lean_object* v_pre_1345_, lean_object* v_post_1346_, lean_object* v_e_1347_, lean_object* v_a_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1345_, v_post_1346_, v_e_1347_, v_a_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v_a_1348_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_object* v_00_u03b1_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_apply_1(v_x_1354_, lean_box(0));
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1360_, lean_object* v_x_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(v_00_u03b1_1360_, v_x_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1365_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_unsigned_to_nat(16u);
v___x_1368_ = lean_mk_array(v___x_1367_, v___x_1366_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__0);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v___x_1369_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__1);
v___x_1373_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1373_, 0, lean_box(0));
lean_closure_set(v___x_1373_, 1, lean_box(0));
lean_closure_set(v___x_1373_, 2, v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(lean_object* v_input_1374_, lean_object* v_pre_1375_, lean_object* v_post_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_a_1382_; lean_object* v___x_1383_; 
v___x_1380_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___closed__2);
v___x_1381_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1380_, v___y_1377_, v___y_1378_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0(v_pre_1375_, v_post_1376_, v_input_1374_, v_a_1382_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1385_, 0, lean_box(0));
lean_closure_set(v___x_1385_, 1, lean_box(0));
lean_closure_set(v___x_1385_, 2, v_a_1382_);
v___x_1386_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___lam__0(lean_box(0), v___x_1385_, v___y_1377_, v___y_1378_);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v___x_1386_, 0);
lean_dec(v_unused_1394_);
v___x_1388_ = v___x_1386_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_dec(v___x_1386_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v_a_1384_);
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1384_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_dec(v_a_1382_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0___boxed(lean_object* v_input_1395_, lean_object* v_pre_1396_, lean_object* v_post_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_input_1395_, v_pre_1396_, v_post_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(lean_object* v_e_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___f_1408_; lean_object* v___f_1409_; lean_object* v___x_1410_; 
v___f_1408_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__0));
v___f_1409_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___closed__1));
v___x_1410_ = l_Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0(v_e_1404_, v___f_1408_, v___f_1409_, v_a_1405_, v_a_1406_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta___boxed(lean_object* v_e_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_e_1411_, v_a_1412_, v_a_1413_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1416_, lean_object* v_m_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___redArg(v_m_1417_, v_a_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1420_, lean_object* v_m_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3(v_00_u03b2_1420_, v_m_1421_, v_a_1422_);
lean_dec_ref(v_a_1422_);
lean_dec_ref(v_m_1421_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1424_, lean_object* v_ref_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_1425_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1430_, lean_object* v_ref_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1430_, v_ref_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1436_, lean_object* v_x_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v_x_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5(v_00_u03b1_1443_, v_x_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_1450_, lean_object* v_m_1451_, lean_object* v_a_1452_, lean_object* v_b_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6___redArg(v_m_1451_, v_a_1452_, v_b_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_1455_, lean_object* v_a_1456_, lean_object* v_x_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___redArg(v_a_1456_, v_x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1459_, lean_object* v_a_1460_, lean_object* v_x_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_1459_, v_a_1460_, v_x_1461_);
lean_dec(v_x_1461_);
lean_dec_ref(v_a_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_1463_, lean_object* v_a_1464_, lean_object* v_x_1465_){
_start:
{
uint8_t v___x_1466_; 
v___x_1466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___redArg(v_a_1464_, v_x_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1467_, lean_object* v_a_1468_, lean_object* v_x_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_1467_, v_a_1468_, v_x_1469_);
lean_dec(v_x_1469_);
lean_dec_ref(v_a_1468_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_1472_, lean_object* v_data_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10___redArg(v_data_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_1475_, lean_object* v_a_1476_, lean_object* v_b_1477_, lean_object* v_x_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__11___redArg(v_a_1476_, v_b_1477_, v_x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_1480_, lean_object* v_i_1481_, lean_object* v_source_1482_, lean_object* v_target_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_1481_, v_source_1482_, v_target_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_1486_, v_x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(lean_object* v_declName_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v_env_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1492_ = lean_st_ref_get(v___y_1490_);
v_env_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc_ref(v_env_1493_);
lean_dec(v___x_1492_);
v___x_1494_ = l_Lean_isRecCore(v_env_1493_, v_declName_1489_);
v___x_1495_ = lean_box(v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg___boxed(lean_object* v_declName_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1497_, v___y_1498_);
lean_dec(v___y_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(lean_object* v_declName_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1501_, v___y_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___boxed(lean_object* v_declName_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2(v_declName_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(lean_object* v_declName_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v_env_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1518_ = lean_st_ref_get(v___y_1516_);
v_env_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc_ref(v_env_1519_);
lean_dec(v___x_1518_);
v___x_1520_ = lean_get_reducibility_status(v_env_1519_, v_declName_1515_);
v___x_1521_ = lean_box(v___x_1520_);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1523_, v___y_1524_);
lean_dec(v___y_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(lean_object* v_declName_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1549_; 
v___x_1533_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1527_, v___y_1531_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1549_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1549_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
uint8_t v___x_1538_; 
v___x_1538_ = lean_unbox(v_a_1534_);
lean_dec(v_a_1534_);
if (v___x_1538_ == 0)
{
uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1539_ = 1;
v___x_1540_ = lean_box(v___x_1539_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1540_);
v___x_1542_ = v___x_1536_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
else
{
uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1544_ = 0;
v___x_1545_ = lean_box(v___x_1544_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1545_);
v___x_1547_ = v___x_1536_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0___boxed(lean_object* v_declName_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(lean_object* v_a_1557_, lean_object* v_b_1558_){
_start:
{
lean_object* v_array_1560_; lean_object* v_start_1561_; lean_object* v_stop_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1579_; 
v_array_1560_ = lean_ctor_get(v_a_1557_, 0);
v_start_1561_ = lean_ctor_get(v_a_1557_, 1);
v_stop_1562_ = lean_ctor_get(v_a_1557_, 2);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1564_ = v_a_1557_;
v_isShared_1565_ = v_isSharedCheck_1579_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_stop_1562_);
lean_inc(v_start_1561_);
lean_inc(v_array_1560_);
lean_dec(v_a_1557_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1579_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_nat_dec_lt(v_start_1561_, v_stop_1562_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_del_object(v___x_1564_);
lean_dec(v_stop_1562_);
lean_dec(v_start_1561_);
lean_dec_ref(v_array_1560_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_b_1558_);
return v___x_1567_;
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_unsigned_to_nat(1u);
v___x_1570_ = lean_nat_add(v_start_1561_, v___x_1569_);
lean_inc_ref(v_array_1560_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 1, v___x_1570_);
v___x_1572_ = v___x_1564_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_array_1560_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_stop_1562_);
v___x_1572_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = lean_array_fget(v_array_1560_, v_start_1561_);
lean_dec(v_start_1561_);
lean_dec_ref(v_array_1560_);
v___x_1574_ = l_Lean_Expr_hasExprMVar(v___x_1573_);
lean_dec(v___x_1573_);
if (v___x_1574_ == 0)
{
v_a_1557_ = v___x_1572_;
v_b_1558_ = v___x_1568_;
goto _start;
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_dec_ref(v___x_1576_);
v_a_1557_ = v___x_1572_;
v_b_1558_ = v___x_1568_;
goto _start;
}
else
{
lean_dec_ref(v___x_1572_);
return v___x_1576_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg___boxed(lean_object* v_a_1580_, lean_object* v_b_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1580_, v_b_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(lean_object* v_e_1592_, uint8_t v_isMatch_1593_, uint8_t v_root_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___y_1601_; lean_object* v_b_1602_; lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1592_, v_root_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1776_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1776_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1776_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___y_1619_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; 
if (v_root_1594_ == 0)
{
lean_object* v___x_1764_; 
lean_inc(v_a_1614_);
v___x_1764_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1614_);
if (lean_obj_tag(v___x_1764_) == 1)
{
lean_object* v_val_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1775_; 
lean_del_object(v___x_1616_);
lean_dec(v_a_1614_);
v_val_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_val_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 2);
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_val_1765_);
v___x_1770_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
}
}
else
{
lean_dec(v___x_1764_);
v___y_1629_ = v_a_1595_;
v___y_1630_ = v_a_1596_;
v___y_1631_ = v_a_1597_;
v___y_1632_ = v_a_1598_;
goto v___jp_1628_;
}
}
else
{
v___y_1629_ = v_a_1595_;
v___y_1630_ = v_a_1596_;
v___y_1631_ = v_a_1597_;
v___y_1632_ = v_a_1598_;
goto v___jp_1628_;
}
v___jp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1620_ = l_Lean_Expr_getAppNumArgs(v_a_1614_);
lean_inc(v___x_1620_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___y_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_mk_empty_array_with_capacity(v___x_1620_);
lean_dec(v___x_1620_);
v___x_1623_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1614_, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1621_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1624_);
v___x_1626_ = v___x_1616_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
v___jp_1628_:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Expr_getAppFn(v_a_1614_);
switch(lean_obj_tag(v___x_1633_))
{
case 1:
{
lean_object* v_fvarId_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_del_object(v___x_1616_);
v_fvarId_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_fvarId_1634_);
lean_dec_ref(v___x_1633_);
v___x_1635_ = l_Lean_Expr_getAppNumArgs(v_a_1614_);
lean_inc(v___x_1635_);
v___x_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1636_, 0, v_fvarId_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_mk_empty_array_with_capacity(v___x_1635_);
lean_dec(v___x_1635_);
v___x_1638_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1614_, v___x_1637_);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1636_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
case 2:
{
lean_del_object(v___x_1616_);
lean_dec(v_a_1614_);
if (v_isMatch_1593_ == 0)
{
lean_object* v_mvarId_1641_; lean_object* v___x_1642_; uint8_t v_isDefEqStuckEx_1643_; 
v_mvarId_1641_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_mvarId_1641_);
lean_dec_ref(v___x_1633_);
v___x_1642_ = l_Lean_Meta_Context_config(v___y_1629_);
v_isDefEqStuckEx_1643_ = lean_ctor_get_uint8(v___x_1642_, 4);
lean_dec_ref(v___x_1642_);
if (v_isDefEqStuckEx_1643_ == 0)
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1641_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1658_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1658_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1658_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
uint8_t v___x_1649_; 
v___x_1649_ = lean_unbox(v_a_1645_);
lean_dec(v_a_1645_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1650_);
v___x_1652_ = v___x_1647_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1654_);
v___x_1656_ = v___x_1647_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_a_1659_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1644_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1644_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec(v_mvarId_1641_);
v___x_1667_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec_ref(v___x_1633_);
v___x_1669_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
case 4:
{
lean_object* v_declName_1671_; lean_object* v___x_1672_; uint8_t v_isDefEqStuckEx_1673_; 
v_declName_1671_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_declName_1671_);
lean_dec_ref(v___x_1633_);
v___x_1672_ = l_Lean_Meta_Context_config(v___y_1629_);
v_isDefEqStuckEx_1673_ = lean_ctor_get_uint8(v___x_1672_, 4);
lean_dec_ref(v___x_1672_);
if (v_isDefEqStuckEx_1673_ == 0)
{
v___y_1619_ = v_declName_1671_;
goto v___jp_1618_;
}
else
{
uint8_t v___x_1674_; 
v___x_1674_ = l_Lean_Expr_hasExprMVar(v_a_1614_);
if (v___x_1674_ == 0)
{
v___y_1619_ = v_declName_1671_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1675_; 
lean_inc(v_declName_1671_);
v___x_1675_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1671_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
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
v___x_1678_ = lean_st_ref_get(v___y_1632_);
v_env_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_ref(v_env_1679_);
lean_dec(v___x_1678_);
v___x_1680_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1679_, v_a_1614_);
if (lean_obj_tag(v___x_1680_) == 1)
{
lean_object* v_val_1681_; lean_object* v_numDiscrs_1682_; lean_object* v_nargs_1683_; lean_object* v_dummy_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_val_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_val_1681_);
lean_dec_ref(v___x_1680_);
v_numDiscrs_1682_ = lean_ctor_get(v_val_1681_, 1);
lean_inc(v_numDiscrs_1682_);
v_nargs_1683_ = l_Lean_Expr_getAppNumArgs(v_a_1614_);
v_dummy_1684_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1683_);
v___x_1685_ = lean_mk_array(v_nargs_1683_, v_dummy_1684_);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_nat_sub(v_nargs_1683_, v___x_1686_);
lean_dec(v_nargs_1683_);
lean_inc(v_a_1614_);
v___x_1688_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1614_, v___x_1685_, v___x_1687_);
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
v___y_1619_ = v_declName_1671_;
goto v___jp_1618_;
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_declName_1671_);
lean_del_object(v___x_1616_);
lean_dec(v_a_1614_);
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
lean_inc(v_declName_1671_);
v___x_1702_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1671_, v___y_1632_);
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = lean_unbox(v_a_1703_);
lean_dec(v_a_1703_);
if (v___x_1704_ == 0)
{
v___y_1619_ = v_declName_1671_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_dec_ref(v___x_1705_);
v___y_1619_ = v_declName_1671_;
goto v___jp_1618_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec(v_declName_1671_);
lean_del_object(v___x_1616_);
lean_dec(v_a_1614_);
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
v___y_1619_ = v_declName_1671_;
goto v___jp_1618_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_declName_1671_);
lean_del_object(v___x_1616_);
lean_dec(v_a_1614_);
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
lean_dec(v_declName_1671_);
lean_del_object(v___x_1616_);
lean_dec(v_a_1614_);
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
case 7:
{
lean_object* v_binderType_1731_; lean_object* v_body_1732_; uint8_t v___x_1733_; 
lean_del_object(v___x_1616_);
lean_dec(v_a_1614_);
v_binderType_1731_ = lean_ctor_get(v___x_1633_, 1);
lean_inc_ref(v_binderType_1731_);
v_body_1732_ = lean_ctor_get(v___x_1633_, 2);
lean_inc_ref(v_body_1732_);
lean_dec_ref(v___x_1633_);
v___x_1733_ = l_Lean_Expr_hasLooseBVars(v_body_1732_);
if (v___x_1733_ == 0)
{
v___y_1601_ = v_binderType_1731_;
v_b_1602_ = v_body_1732_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1732_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1734_);
v___y_1601_ = v_binderType_1731_;
v_b_1602_ = v_a_1735_;
goto v___jp_1600_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec_ref(v_binderType_1731_);
v_a_1736_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1734_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1734_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
case 9:
{
lean_object* v_a_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_del_object(v___x_1616_);
lean_dec(v_a_1614_);
v_a_1744_ = lean_ctor_get(v___x_1633_, 0);
lean_inc_ref(v_a_1744_);
lean_dec_ref(v___x_1633_);
v___x_1745_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_a_1744_);
v___x_1746_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
return v___x_1748_;
}
case 11:
{
lean_object* v_typeName_1749_; lean_object* v_idx_1750_; lean_object* v_struct_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_del_object(v___x_1616_);
v_typeName_1749_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_typeName_1749_);
v_idx_1750_ = lean_ctor_get(v___x_1633_, 1);
lean_inc(v_idx_1750_);
v_struct_1751_ = lean_ctor_get(v___x_1633_, 2);
lean_inc_ref(v_struct_1751_);
lean_dec_ref(v___x_1633_);
v___x_1752_ = l_Lean_Expr_getAppNumArgs(v_a_1614_);
lean_inc(v___x_1752_);
v___x_1753_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1753_, 0, v_typeName_1749_);
lean_ctor_set(v___x_1753_, 1, v_idx_1750_);
lean_ctor_set(v___x_1753_, 2, v___x_1752_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = lean_mk_empty_array_with_capacity(v___x_1754_);
v___x_1756_ = lean_array_push(v___x_1755_, v_struct_1751_);
v___x_1757_ = lean_mk_empty_array_with_capacity(v___x_1752_);
lean_dec(v___x_1752_);
v___x_1758_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1614_, v___x_1757_);
v___x_1759_ = l_Array_append___redArg(v___x_1756_, v___x_1758_);
lean_dec_ref(v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1753_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
default: 
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec_ref(v___x_1633_);
lean_del_object(v___x_1616_);
lean_dec(v_a_1614_);
v___x_1762_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_a_1777_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1613_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1613_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
v___jp_1600_:
{
uint8_t v___x_1603_; 
v___x_1603_ = l_Lean_Expr_hasLooseBVars(v_b_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1604_ = lean_box(5);
v___x_1605_ = lean_unsigned_to_nat(2u);
v___x_1606_ = lean_mk_empty_array_with_capacity(v___x_1605_);
v___x_1607_ = lean_array_push(v___x_1606_, v___y_1601_);
v___x_1608_ = lean_array_push(v___x_1607_, v_b_1602_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1604_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref(v_b_1602_);
lean_dec_ref(v___y_1601_);
v___x_1611_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
return v___x_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1785_, lean_object* v_isMatch_1786_, lean_object* v_root_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
uint8_t v_isMatch_boxed_1793_; uint8_t v_root_boxed_1794_; lean_object* v_res_1795_; 
v_isMatch_boxed_1793_ = lean_unbox(v_isMatch_1786_);
v_root_boxed_1794_ = lean_unbox(v_root_1787_);
v_res_1795_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1785_, v_isMatch_boxed_1793_, v_root_boxed_1794_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1796_, v___y_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1810_, lean_object* v_R_1811_, lean_object* v_a_1812_, lean_object* v_b_1813_, lean_object* v_c_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1812_, v_b_1813_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1821_, lean_object* v_R_1822_, lean_object* v_a_1823_, lean_object* v_b_1824_, lean_object* v_c_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1821_, v_R_1822_, v_a_1823_, v_b_1824_, v_c_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1832_, uint8_t v_root_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
uint8_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = 1;
v___x_1840_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1832_, v___x_1839_, v_root_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1841_, lean_object* v_root_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
uint8_t v_root_boxed_1848_; lean_object* v_res_1849_; 
v_root_boxed_1848_ = lean_unbox(v_root_1842_);
v_res_1849_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1841_, v_root_boxed_1848_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
return v_res_1849_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_unsigned_to_nat(16u);
v___x_1854_ = lean_mk_array(v___x_1853_, v___x_1852_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v___x_1855_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1861_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___x_1859_);
lean_ctor_set(v___x_1861_, 2, v___x_1858_);
lean_ctor_set(v___x_1861_, 3, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_a_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3);
return v___x_1863_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_box(0));
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1869_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1870_ = lean_unsigned_to_nat(0u);
v___x_1871_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_1872_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1870_);
lean_ctor_set(v___x_1872_, 2, v___x_1869_);
lean_ctor_set(v___x_1872_, 3, v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
lean_object* v_values_1877_; lean_object* v_star_1878_; lean_object* v_children_1879_; lean_object* v_pending_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1888_; 
v_values_1877_ = lean_ctor_get(v_x_1875_, 0);
v_star_1878_ = lean_ctor_get(v_x_1875_, 1);
v_children_1879_ = lean_ctor_get(v_x_1875_, 2);
v_pending_1880_ = lean_ctor_get(v_x_1875_, 3);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1882_ = v_x_1875_;
v_isShared_1883_ = v_isSharedCheck_1888_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_pending_1880_);
lean_inc(v_children_1879_);
lean_inc(v_star_1878_);
lean_inc(v_values_1877_);
lean_dec(v_x_1875_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1888_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1884_ = lean_array_push(v_pending_1880_, v_x_1876_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 3, v___x_1884_);
v___x_1886_ = v___x_1882_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_values_1877_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_star_1878_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_children_1879_);
lean_ctor_set(v_reuseFailAlloc_1887_, 3, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1890_, v_x_1891_);
return v___x_1892_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1893_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_1894_ = lean_unsigned_to_nat(1u);
v___x_1895_ = lean_mk_empty_array_with_capacity(v___x_1894_);
v___x_1896_ = lean_array_push(v___x_1895_, v___x_1893_);
return v___x_1896_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1898_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v___x_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1908_; lean_object* v_env_1909_; lean_object* v___x_1910_; lean_object* v_mctx_1911_; lean_object* v_lctx_1912_; lean_object* v_options_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1908_ = lean_st_ref_get(v___y_1906_);
v_env_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc_ref(v_env_1909_);
lean_dec(v___x_1908_);
v___x_1910_ = lean_st_ref_get(v___y_1904_);
v_mctx_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc_ref(v_mctx_1911_);
lean_dec(v___x_1910_);
v_lctx_1912_ = lean_ctor_get(v___y_1903_, 2);
v_options_1913_ = lean_ctor_get(v___y_1905_, 2);
lean_inc_ref(v_options_1913_);
lean_inc_ref(v_lctx_1912_);
v___x_1914_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1914_, 0, v_env_1909_);
lean_ctor_set(v___x_1914_, 1, v_mctx_1911_);
lean_ctor_set(v___x_1914_, 2, v_lctx_1912_);
lean_ctor_set(v___x_1914_, 3, v_options_1913_);
v___x_1915_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v_msgData_1902_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_ref_1930_; lean_object* v___x_1931_; lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1940_; 
v_ref_1930_ = lean_ctor_get(v___y_1927_, 5);
v___x_1931_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_inc(v_ref_1930_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_ref_1930_);
lean_ctor_set(v___x_1936_, 1, v_a_1932_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 1);
lean_ctor_set(v___x_1934_, 0, v___x_1936_);
v___x_1938_ = v___x_1934_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1947_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1950_ = l_Lean_stringToMessageData(v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1951_, lean_object* v_todo_1952_, lean_object* v_e_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
uint8_t v___x_1959_; 
v___x_1959_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1953_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1953_, v_root_1951_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2100_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_2100_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2100_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_v_1966_; lean_object* v___x_1972_; lean_object* v_k_1974_; lean_object* v_nargs_1975_; lean_object* v_todo_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; 
v___x_1972_ = l_Lean_Expr_getAppFn(v_a_1961_);
switch(lean_obj_tag(v___x_1972_))
{
case 9:
{
lean_object* v_a_2019_; 
lean_dec(v_a_1961_);
v_a_2019_ = lean_ctor_get(v___x_1972_, 0);
lean_inc_ref(v_a_2019_);
lean_dec_ref(v___x_1972_);
v_v_1966_ = v_a_2019_;
goto v___jp_1965_;
}
case 4:
{
lean_object* v_declName_2020_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; 
v_declName_2020_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_declName_2020_);
if (v_root_1951_ == 0)
{
lean_object* v___x_2028_; 
lean_inc(v_a_1961_);
v___x_2028_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1961_);
if (lean_obj_tag(v___x_2028_) == 1)
{
lean_object* v_val_2029_; 
lean_dec(v_declName_2020_);
lean_dec_ref(v___x_1972_);
lean_dec(v_a_1961_);
v_val_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_val_2029_);
lean_dec_ref(v___x_2028_);
v_v_1966_ = v_val_2029_;
goto v___jp_1965_;
}
else
{
lean_object* v___x_2030_; 
lean_dec(v___x_2028_);
lean_del_object(v___x_1963_);
v___x_2030_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2020_, v_a_1961_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2041_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_unbox(v_a_2031_);
lean_dec(v_a_2031_);
if (v___x_2035_ == 0)
{
lean_del_object(v___x_2033_);
v___y_2022_ = v_a_1954_;
v___y_2023_ = v_a_1955_;
v___y_2024_ = v_a_1956_;
v___y_2025_ = v_a_1957_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec(v_declName_2020_);
lean_dec_ref(v___x_1972_);
lean_dec(v_a_1961_);
v___x_2036_ = lean_box(3);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v_todo_1952_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2037_);
v___x_2039_ = v___x_2033_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
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
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v___x_1972_);
lean_dec(v_declName_2020_);
lean_dec(v_a_1961_);
lean_dec_ref(v_todo_1952_);
v_a_2042_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2030_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2030_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
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
}
else
{
lean_del_object(v___x_1963_);
v___y_2022_ = v_a_1954_;
v___y_2023_ = v_a_1955_;
v___y_2024_ = v_a_1956_;
v___y_2025_ = v_a_1957_;
goto v___jp_2021_;
}
v___jp_2021_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = l_Lean_Expr_getAppNumArgs(v_a_1961_);
lean_inc(v___x_2026_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_declName_2020_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v_k_1974_ = v___x_2027_;
v_nargs_1975_ = v___x_2026_;
v_todo_1976_ = v_todo_1952_;
v___y_1977_ = v___y_2022_;
v___y_1978_ = v___y_2023_;
v___y_1979_ = v___y_2024_;
v___y_1980_ = v___y_2025_;
goto v___jp_1973_;
}
}
case 11:
{
lean_object* v_typeName_2050_; lean_object* v_idx_2051_; lean_object* v_struct_2052_; lean_object* v___x_2053_; lean_object* v___y_2055_; lean_object* v_env_2059_; uint8_t v___x_2060_; 
lean_del_object(v___x_1963_);
v_typeName_2050_ = lean_ctor_get(v___x_1972_, 0);
lean_inc_n(v_typeName_2050_, 2);
v_idx_2051_ = lean_ctor_get(v___x_1972_, 1);
lean_inc(v_idx_2051_);
v_struct_2052_ = lean_ctor_get(v___x_1972_, 2);
lean_inc_ref(v_struct_2052_);
v___x_2053_ = lean_st_ref_get(v_a_1957_);
v_env_2059_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_ref(v_env_2059_);
lean_dec(v___x_2053_);
v___x_2060_ = lean_is_class(v_env_2059_, v_typeName_2050_);
if (v___x_2060_ == 0)
{
v___y_2055_ = v_struct_2052_;
goto v___jp_2054_;
}
else
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2052_);
v___y_2055_ = v___x_2061_;
goto v___jp_2054_;
}
v___jp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = l_Lean_Expr_getAppNumArgs(v_a_1961_);
lean_inc(v___x_2056_);
v___x_2057_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2057_, 0, v_typeName_2050_);
lean_ctor_set(v___x_2057_, 1, v_idx_2051_);
lean_ctor_set(v___x_2057_, 2, v___x_2056_);
v___x_2058_ = lean_array_push(v_todo_1952_, v___y_2055_);
v_k_1974_ = v___x_2057_;
v_nargs_1975_ = v___x_2056_;
v_todo_1976_ = v___x_2058_;
v___y_1977_ = v_a_1954_;
v___y_1978_ = v_a_1955_;
v___y_1979_ = v_a_1956_;
v___y_1980_ = v_a_1957_;
goto v___jp_1973_;
}
}
case 1:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_dec_ref(v___x_1972_);
lean_del_object(v___x_1963_);
lean_dec(v_a_1961_);
v___x_2062_ = lean_box(3);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v_todo_1952_);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
case 2:
{
lean_object* v_mvarId_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
lean_del_object(v___x_1963_);
lean_dec(v_a_1961_);
v_mvarId_2065_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_mvarId_2065_);
lean_dec_ref(v___x_1972_);
v___x_2066_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2067_ = l_Lean_instBEqMVarId_beq(v_mvarId_2065_, v___x_2066_);
lean_dec(v_mvarId_2065_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec_ref(v_todo_1952_);
v___x_2068_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2069_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2068_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
return v___x_2069_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_box(3);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v_todo_1952_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
}
case 7:
{
lean_object* v_binderType_2073_; lean_object* v_body_2074_; lean_object* v_b_2076_; uint8_t v___x_2086_; 
lean_del_object(v___x_1963_);
lean_dec(v_a_1961_);
v_binderType_2073_ = lean_ctor_get(v___x_1972_, 1);
lean_inc_ref(v_binderType_2073_);
v_body_2074_ = lean_ctor_get(v___x_1972_, 2);
lean_inc_ref(v_body_2074_);
lean_dec_ref(v___x_1972_);
v___x_2086_ = l_Lean_Expr_hasLooseBVars(v_body_2074_);
if (v___x_2086_ == 0)
{
v_b_2076_ = v_body_2074_;
goto v___jp_2075_;
}
else
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2074_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref(v___x_2087_);
v_b_2076_ = v_a_2088_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_binderType_2073_);
lean_dec_ref(v_todo_1952_);
v_a_2089_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2087_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2087_);
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
v___jp_2075_:
{
uint8_t v___x_2077_; 
v___x_2077_ = l_Lean_Expr_hasLooseBVars(v_b_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2078_ = lean_box(5);
v___x_2079_ = lean_array_push(v_todo_1952_, v_binderType_2073_);
v___x_2080_ = lean_array_push(v___x_2079_, v_b_2076_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2078_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_binderType_2073_);
v___x_2083_ = lean_box(4);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v_todo_1952_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
}
}
default: 
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec_ref(v___x_1972_);
lean_del_object(v___x_1963_);
lean_dec(v_a_1961_);
v___x_2097_ = lean_box(4);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_todo_1952_);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
return v___x_2099_;
}
}
v___jp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1967_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_v_1966_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v_todo_1952_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1968_);
v___x_1970_ = v___x_1963_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
v___jp_1973_:
{
lean_object* v___x_1981_; 
lean_inc(v_nargs_1975_);
v___x_1981_ = l_Lean_Meta_getFunInfoNArgs(v___x_1972_, v_nargs_1975_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v_paramInfo_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2009_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref(v___x_1981_);
v_paramInfo_1983_ = lean_ctor_get(v_a_1982_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_a_1982_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_a_1982_, 1);
lean_dec(v_unused_2010_);
v___x_1985_ = v_a_1982_;
v_isShared_1986_ = v_isSharedCheck_2009_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_paramInfo_1983_);
lean_dec(v_a_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2009_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_sub(v_nargs_1975_, v___x_1987_);
lean_dec(v_nargs_1975_);
v___x_1989_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_1983_, v___x_1988_, v_a_1961_, v_todo_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec_ref(v_paramInfo_1983_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2000_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v_a_1990_);
lean_ctor_set(v___x_1985_, 0, v_k_1974_);
v___x_1995_ = v___x_1985_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_k_1974_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1995_);
v___x_1997_ = v___x_1992_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_del_object(v___x_1985_);
lean_dec(v_k_1974_);
v_a_2001_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1989_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1989_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
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
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v_todo_1976_);
lean_dec(v_nargs_1975_);
lean_dec(v_k_1974_);
lean_dec(v_a_1961_);
v_a_2011_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1981_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1981_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v_todo_1952_);
v_a_2101_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_1960_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_1960_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec_ref(v_e_1953_);
v___x_2109_ = lean_box(3);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v_todo_1952_);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
return v___x_2111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2112_, lean_object* v_todo_2113_, lean_object* v_e_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
uint8_t v_root_boxed_2120_; lean_object* v_res_2121_; 
v_root_boxed_2120_ = lean_unbox(v_root_2112_);
v_res_2121_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2120_, v_todo_2113_, v_e_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2122_, lean_object* v_msg_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2130_, lean_object* v_msg_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2130_, v_msg_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2137_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_unsigned_to_nat(8u);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2145_ = 1;
v___x_2146_ = lean_unsigned_to_nat(8u);
v___x_2147_ = lean_mk_empty_array_with_capacity(v___x_2146_);
v___x_2148_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2145_, v___x_2147_, v_e_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2156_, uint8_t v_root_2157_, lean_object* v_todo_2158_, lean_object* v_keys_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2165_ = lean_array_get_size(v_todo_2158_);
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = lean_nat_dec_eq(v___x_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v_e_2171_; lean_object* v_todo_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2168_ = l_Lean_instInhabitedExpr;
v___x_2169_ = lean_unsigned_to_nat(1u);
v___x_2170_ = lean_nat_sub(v___x_2165_, v___x_2169_);
v_e_2171_ = lean_array_get(v___x_2168_, v_todo_2158_, v___x_2170_);
lean_dec(v___x_2170_);
v_todo_2172_ = lean_array_pop(v_todo_2158_);
v___x_2173_ = lean_box(v_root_2157_);
lean_inc_ref(v_op_2156_);
lean_inc(v_a_2163_);
lean_inc_ref(v_a_2162_);
lean_inc(v_a_2161_);
lean_inc_ref(v_a_2160_);
v___x_2174_ = lean_apply_8(v_op_2156_, v___x_2173_, v_todo_2172_, v_e_2171_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, lean_box(0));
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v_fst_2176_; lean_object* v_snd_2177_; lean_object* v___x_2178_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
v_fst_2176_ = lean_ctor_get(v_a_2175_, 0);
lean_inc(v_fst_2176_);
v_snd_2177_ = lean_ctor_get(v_a_2175_, 1);
lean_inc(v_snd_2177_);
lean_dec(v_a_2175_);
v___x_2178_ = lean_array_push(v_keys_2159_, v_fst_2176_);
v_root_2157_ = v___x_2167_;
v_todo_2158_ = v_snd_2177_;
v_keys_2159_ = v___x_2178_;
goto _start;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_keys_2159_);
lean_dec_ref(v_op_2156_);
v_a_2180_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2174_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2174_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v___x_2188_; 
lean_dec_ref(v_todo_2158_);
lean_dec_ref(v_op_2156_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_keys_2159_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2189_, lean_object* v_root_2190_, lean_object* v_todo_2191_, lean_object* v_keys_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
uint8_t v_root_boxed_2198_; lean_object* v_res_2199_; 
v_root_boxed_2198_ = lean_unbox(v_root_2190_);
v_res_2199_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2189_, v_root_boxed_2198_, v_todo_2191_, v_keys_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_op_2207_; lean_object* v___x_2208_; lean_object* v_todo_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_op_2207_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2208_ = lean_unsigned_to_nat(8u);
v_todo_2209_ = lean_mk_empty_array_with_capacity(v___x_2208_);
v___x_2210_ = 1;
lean_inc_ref(v_todo_2209_);
v___x_2211_ = lean_array_push(v_todo_2209_, v_e_2201_);
v___x_2212_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2207_, v___x_2210_, v___x_2211_, v_todo_2209_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2220_, lean_object* v_todo_2221_, lean_object* v_e_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = 1;
v___x_2229_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2222_, v___x_2228_, v_root_2220_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2247_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2247_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2247_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_fst_2234_; lean_object* v_snd_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2246_; 
v_fst_2234_ = lean_ctor_get(v_a_2230_, 0);
v_snd_2235_ = lean_ctor_get(v_a_2230_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_a_2230_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2237_ = v_a_2230_;
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_snd_2235_);
lean_inc(v_fst_2234_);
lean_dec(v_a_2230_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2239_ = l_Array_append___redArg(v_todo_2221_, v_snd_2235_);
lean_dec(v_snd_2235_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 1, v___x_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_fst_2234_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2243_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2241_);
v___x_2243_ = v___x_2232_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2221_);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2248_, lean_object* v_todo_2249_, lean_object* v_e_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v_root_boxed_2256_; lean_object* v_res_2257_; 
v_root_boxed_2256_ = lean_unbox(v_root_2248_);
v_res_2257_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2256_, v_todo_2249_, v_e_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_op_2265_; lean_object* v___x_2266_; lean_object* v_todo_2267_; uint8_t v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_op_2265_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2266_ = lean_unsigned_to_nat(8u);
v_todo_2267_ = lean_mk_empty_array_with_capacity(v___x_2266_);
v___x_2268_ = 1;
lean_inc_ref(v_todo_2267_);
v___x_2269_ = lean_array_push(v_todo_2267_, v_e_2259_);
v___x_2270_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2265_, v___x_2268_, v___x_2269_, v_todo_2267_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_);
lean_dec(v_a_2275_);
lean_dec_ref(v_a_2274_);
lean_dec(v_a_2273_);
lean_dec_ref(v_a_2272_);
return v_res_2277_;
}
}
static uint64_t _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0(void){
_start:
{
uint8_t v___x_2278_; uint64_t v___x_2279_; 
v___x_2278_ = 2;
v___x_2279_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2280_, lean_object* v_m_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_tries_2287_; lean_object* v_roots_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2360_; 
v_tries_2287_ = lean_ctor_get(v_d_2280_, 0);
v_roots_2288_ = lean_ctor_get(v_d_2280_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_d_2280_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2290_ = v_d_2280_;
v_isShared_2291_ = v_isSharedCheck_2360_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_roots_2288_);
lean_inc(v_tries_2287_);
lean_dec(v_d_2280_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2360_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; uint8_t v_foApprox_2293_; uint8_t v_ctxApprox_2294_; uint8_t v_quasiPatternApprox_2295_; uint8_t v_constApprox_2296_; uint8_t v_isDefEqStuckEx_2297_; uint8_t v_unificationHints_2298_; uint8_t v_proofIrrelevance_2299_; uint8_t v_assignSyntheticOpaque_2300_; uint8_t v_offsetCnstrs_2301_; uint8_t v_etaStruct_2302_; uint8_t v_univApprox_2303_; uint8_t v_iota_2304_; uint8_t v_beta_2305_; uint8_t v_proj_2306_; uint8_t v_zeta_2307_; uint8_t v_zetaDelta_2308_; uint8_t v_zetaUnused_2309_; uint8_t v_zetaHave_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2359_; 
v___x_2292_ = l_Lean_Meta_Context_config(v_a_2282_);
v_foApprox_2293_ = lean_ctor_get_uint8(v___x_2292_, 0);
v_ctxApprox_2294_ = lean_ctor_get_uint8(v___x_2292_, 1);
v_quasiPatternApprox_2295_ = lean_ctor_get_uint8(v___x_2292_, 2);
v_constApprox_2296_ = lean_ctor_get_uint8(v___x_2292_, 3);
v_isDefEqStuckEx_2297_ = lean_ctor_get_uint8(v___x_2292_, 4);
v_unificationHints_2298_ = lean_ctor_get_uint8(v___x_2292_, 5);
v_proofIrrelevance_2299_ = lean_ctor_get_uint8(v___x_2292_, 6);
v_assignSyntheticOpaque_2300_ = lean_ctor_get_uint8(v___x_2292_, 7);
v_offsetCnstrs_2301_ = lean_ctor_get_uint8(v___x_2292_, 8);
v_etaStruct_2302_ = lean_ctor_get_uint8(v___x_2292_, 10);
v_univApprox_2303_ = lean_ctor_get_uint8(v___x_2292_, 11);
v_iota_2304_ = lean_ctor_get_uint8(v___x_2292_, 12);
v_beta_2305_ = lean_ctor_get_uint8(v___x_2292_, 13);
v_proj_2306_ = lean_ctor_get_uint8(v___x_2292_, 14);
v_zeta_2307_ = lean_ctor_get_uint8(v___x_2292_, 15);
v_zetaDelta_2308_ = lean_ctor_get_uint8(v___x_2292_, 16);
v_zetaUnused_2309_ = lean_ctor_get_uint8(v___x_2292_, 17);
v_zetaHave_2310_ = lean_ctor_get_uint8(v___x_2292_, 18);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2312_ = v___x_2292_;
v_isShared_2313_ = v_isSharedCheck_2359_;
goto v_resetjp_2311_;
}
else
{
lean_dec(v___x_2292_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2359_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; uint8_t v_trackZetaDelta_2315_; lean_object* v_zetaDeltaSet_2316_; lean_object* v_lctx_2317_; lean_object* v_localInstances_2318_; lean_object* v_defEqCtx_x3f_2319_; lean_object* v_synthPendingDepth_2320_; lean_object* v_canUnfold_x3f_2321_; uint8_t v_univApprox_2322_; uint8_t v_inTypeClassResolution_2323_; uint8_t v_cacheInferType_2324_; uint8_t v___x_2325_; lean_object* v_config_2327_; 
v___x_2314_ = lean_st_mk_ref(v_tries_2287_);
v_trackZetaDelta_2315_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*7);
v_zetaDeltaSet_2316_ = lean_ctor_get(v_a_2282_, 1);
v_lctx_2317_ = lean_ctor_get(v_a_2282_, 2);
v_localInstances_2318_ = lean_ctor_get(v_a_2282_, 3);
v_defEqCtx_x3f_2319_ = lean_ctor_get(v_a_2282_, 4);
v_synthPendingDepth_2320_ = lean_ctor_get(v_a_2282_, 5);
v_canUnfold_x3f_2321_ = lean_ctor_get(v_a_2282_, 6);
v_univApprox_2322_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2323_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*7 + 2);
v_cacheInferType_2324_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*7 + 3);
v___x_2325_ = 2;
if (v_isShared_2313_ == 0)
{
v_config_2327_ = v___x_2312_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 0, v_foApprox_2293_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 1, v_ctxApprox_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 2, v_quasiPatternApprox_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 3, v_constApprox_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 4, v_isDefEqStuckEx_2297_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 5, v_unificationHints_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 6, v_proofIrrelevance_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 7, v_assignSyntheticOpaque_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 8, v_offsetCnstrs_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 10, v_etaStruct_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 11, v_univApprox_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 12, v_iota_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 13, v_beta_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 14, v_proj_2306_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 15, v_zeta_2307_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 16, v_zetaDelta_2308_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 17, v_zetaUnused_2309_);
lean_ctor_set_uint8(v_reuseFailAlloc_2358_, 18, v_zetaHave_2310_);
v_config_2327_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
uint64_t v___x_2328_; uint64_t v___x_2329_; uint64_t v___x_2330_; uint64_t v___x_2331_; uint64_t v___x_2332_; uint64_t v_key_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_ctor_set_uint8(v_config_2327_, 9, v___x_2325_);
v___x_2328_ = l_Lean_Meta_Context_configKey(v_a_2282_);
v___x_2329_ = 2ULL;
v___x_2330_ = lean_uint64_shift_right(v___x_2328_, v___x_2329_);
v___x_2331_ = lean_uint64_shift_left(v___x_2330_, v___x_2329_);
v___x_2332_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0);
v_key_2333_ = lean_uint64_lor(v___x_2331_, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2334_, 0, v_config_2327_);
lean_ctor_set_uint64(v___x_2334_, sizeof(void*)*1, v_key_2333_);
lean_inc(v_canUnfold_x3f_2321_);
lean_inc(v_synthPendingDepth_2320_);
lean_inc(v_defEqCtx_x3f_2319_);
lean_inc_ref(v_localInstances_2318_);
lean_inc_ref(v_lctx_2317_);
lean_inc(v_zetaDeltaSet_2316_);
v___x_2335_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v_zetaDeltaSet_2316_);
lean_ctor_set(v___x_2335_, 2, v_lctx_2317_);
lean_ctor_set(v___x_2335_, 3, v_localInstances_2318_);
lean_ctor_set(v___x_2335_, 4, v_defEqCtx_x3f_2319_);
lean_ctor_set(v___x_2335_, 5, v_synthPendingDepth_2320_);
lean_ctor_set(v___x_2335_, 6, v_canUnfold_x3f_2321_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*7, v_trackZetaDelta_2315_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*7 + 1, v_univApprox_2322_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2323_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*7 + 3, v_cacheInferType_2324_);
lean_inc(v_a_2285_);
lean_inc_ref(v_a_2284_);
lean_inc(v_a_2283_);
lean_inc(v___x_2314_);
v___x_2336_ = lean_apply_6(v_m_2281_, v___x_2314_, v___x_2335_, v_a_2283_, v_a_2284_, v_a_2285_, lean_box(0));
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2349_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2349_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2341_ = lean_st_ref_get(v___x_2314_);
lean_dec(v___x_2314_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2341_);
v___x_2343_ = v___x_2290_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_roots_2288_);
v___x_2343_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_a_2337_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2344_);
v___x_2346_ = v___x_2339_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v___x_2314_);
lean_del_object(v___x_2290_);
lean_dec_ref(v_roots_2288_);
v_a_2350_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2336_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2336_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2361_, lean_object* v_m_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2361_, v_m_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2369_, lean_object* v_00_u03b2_2370_, lean_object* v_d_2371_, lean_object* v_m_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2371_, v_m_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2379_, lean_object* v_00_u03b2_2380_, lean_object* v_d_2381_, lean_object* v_m_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2379_, v_00_u03b2_2380_, v_d_2381_, v_m_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2389_, lean_object* v_v_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2393_ = lean_st_ref_take(v_a_2391_);
v___x_2394_ = lean_array_set(v___x_2393_, v_i_2389_, v_v_2390_);
v___x_2395_ = lean_st_ref_set(v_a_2391_, v___x_2394_);
v___x_2396_ = lean_box(0);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2398_, lean_object* v_v_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2398_, v_v_2399_, v_a_2400_);
lean_dec(v_a_2400_);
lean_dec(v_i_2398_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2403_, lean_object* v_i_2404_, lean_object* v_v_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2404_, v_v_2405_, v_a_2406_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2413_, lean_object* v_i_2414_, lean_object* v_v_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2413_, v_i_2414_, v_v_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec(v_i_2414_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_sz_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v_sz_2425_ = lean_array_get_size(v_a_2424_);
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2428_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2429_ = lean_unsigned_to_nat(1u);
v___x_2430_ = lean_mk_empty_array_with_capacity(v___x_2429_);
v___x_2431_ = lean_array_push(v___x_2430_, v_e_2423_);
v___x_2432_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2427_);
lean_ctor_set(v___x_2432_, 1, v___x_2426_);
lean_ctor_set(v___x_2432_, 2, v___x_2428_);
lean_ctor_set(v___x_2432_, 3, v___x_2431_);
v___x_2433_ = lean_array_push(v_a_2424_, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_sz_2425_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2435_, lean_object* v_e_2436_){
_start:
{
lean_object* v_modifyGet_2437_; lean_object* v___f_2438_; lean_object* v___x_2439_; 
v_modifyGet_2437_ = lean_ctor_get(v_inst_2435_, 2);
lean_inc(v_modifyGet_2437_);
lean_dec_ref(v_inst_2435_);
v___f_2438_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2438_, 0, v_e_2436_);
v___x_2439_ = lean_apply_2(v_modifyGet_2437_, lean_box(0), v___f_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2440_, lean_object* v_00_u03b1_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_e_2444_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2443_, v_e_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2446_, lean_object* v_00_u03b1_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_e_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2446_, v_00_u03b1_2447_, v_inst_2448_, v_inst_2449_, v_e_2450_);
lean_dec_ref(v_inst_2448_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2452_, lean_object* v_e_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2456_; lean_object* v_fst_2458_; lean_object* v_snd_2459_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2456_ = lean_st_ref_take(v_a_2454_);
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_array_get_size(v___x_2456_);
v___x_2464_ = lean_nat_dec_lt(v_i_2452_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_dec_ref(v_e_2453_);
v_fst_2458_ = v___x_2462_;
v_snd_2459_ = v___x_2456_;
goto v___jp_2457_;
}
else
{
lean_object* v_v_2465_; lean_object* v_xs_x27_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_v_2465_ = lean_array_fget(v___x_2456_, v_i_2452_);
v_xs_x27_2466_ = lean_array_fset(v___x_2456_, v_i_2452_, v___x_2462_);
v___x_2467_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2465_, v_e_2453_);
v___x_2468_ = lean_array_fset(v_xs_x27_2466_, v_i_2452_, v___x_2467_);
v_fst_2458_ = v___x_2462_;
v_snd_2459_ = v___x_2468_;
goto v___jp_2457_;
}
v___jp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_st_ref_set(v_a_2454_, v_snd_2459_);
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v_fst_2458_);
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2469_, lean_object* v_e_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2469_, v_e_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec(v_i_2469_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2474_, lean_object* v_i_2475_, lean_object* v_e_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2475_, v_e_2476_, v_a_2477_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2484_, lean_object* v_i_2485_, lean_object* v_e_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2484_, v_i_2485_, v_e_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec(v_i_2485_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v___x_2501_; 
lean_inc(v___y_2495_);
v___x_2501_ = lean_apply_6(v_x_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, lean_box(0));
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2503_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2510_, lean_object* v_localInsts_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___f_2519_; lean_object* v___x_2520_; 
lean_inc(v___y_2513_);
v___f_2519_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2519_, 0, v_x_2512_);
lean_closure_set(v___f_2519_, 1, v___y_2513_);
v___x_2520_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2510_, v_localInsts_2511_, v___f_2519_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2520_) == 0)
{
return v___x_2520_;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2529_, lean_object* v_localInsts_2530_, lean_object* v_x_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2529_, v_localInsts_2530_, v_x_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2539_, lean_object* v_00_u03b1_2540_, lean_object* v_lctx_2541_, lean_object* v_localInsts_2542_, lean_object* v_x_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2541_, v_localInsts_2542_, v_x_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_00_u03b1_2552_, lean_object* v_lctx_2553_, lean_object* v_localInsts_2554_, lean_object* v_x_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2551_, v_00_u03b1_2552_, v_lctx_2553_, v_localInsts_2554_, v_x_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v_sz_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2566_ = lean_st_ref_take(v___y_2564_);
v_sz_2567_ = lean_array_get_size(v___x_2566_);
v___x_2568_ = lean_unsigned_to_nat(0u);
v___x_2569_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2570_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2571_ = lean_unsigned_to_nat(1u);
v___x_2572_ = lean_mk_empty_array_with_capacity(v___x_2571_);
v___x_2573_ = lean_array_push(v___x_2572_, v_e_2563_);
v___x_2574_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2569_);
lean_ctor_set(v___x_2574_, 1, v___x_2568_);
lean_ctor_set(v___x_2574_, 2, v___x_2570_);
lean_ctor_set(v___x_2574_, 3, v___x_2573_);
v___x_2575_ = lean_array_push(v___x_2566_, v___x_2574_);
v___x_2576_ = lean_st_ref_set(v___y_2564_, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v_sz_2567_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2578_, v___y_2579_);
lean_dec(v___y_2579_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2582_, lean_object* v_e_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2583_, v___y_2584_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2591_, lean_object* v_e_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2591_, v_e_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2600_, lean_object* v_todo_2601_, lean_object* v_e_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2600_, v_todo_2601_, v_e_2602_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2610_, lean_object* v_todo_2611_, lean_object* v_e_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
uint8_t v___x_4063__boxed_2619_; lean_object* v_res_2620_; 
v___x_4063__boxed_2619_ = lean_unbox(v___x_2610_);
v_res_2620_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_4063__boxed_2619_, v_todo_2611_, v_e_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2621_, lean_object* v_b_2622_, lean_object* v_x_2623_){
_start:
{
if (lean_obj_tag(v_x_2623_) == 0)
{
lean_dec(v_b_2622_);
lean_dec(v_a_2621_);
return v_x_2623_;
}
else
{
lean_object* v_key_2624_; lean_object* v_value_2625_; lean_object* v_tail_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2638_; 
v_key_2624_ = lean_ctor_get(v_x_2623_, 0);
v_value_2625_ = lean_ctor_get(v_x_2623_, 1);
v_tail_2626_ = lean_ctor_get(v_x_2623_, 2);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_x_2623_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2628_ = v_x_2623_;
v_isShared_2629_ = v_isSharedCheck_2638_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_tail_2626_);
lean_inc(v_value_2625_);
lean_inc(v_key_2624_);
lean_dec(v_x_2623_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2638_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
uint8_t v___x_2630_; 
v___x_2630_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2624_, v_a_2621_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2631_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2621_, v_b_2622_, v_tail_2626_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 2, v___x_2631_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_key_2624_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_value_2625_);
lean_ctor_set(v_reuseFailAlloc_2634_, 2, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
else
{
lean_object* v___x_2636_; 
lean_dec(v_value_2625_);
lean_dec(v_key_2624_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 1, v_b_2622_);
lean_ctor_set(v___x_2628_, 0, v_a_2621_);
v___x_2636_ = v___x_2628_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2621_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_b_2622_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_tail_2626_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2639_, lean_object* v_x_2640_){
_start:
{
if (lean_obj_tag(v_x_2640_) == 0)
{
uint8_t v___x_2641_; 
v___x_2641_ = 0;
return v___x_2641_;
}
else
{
lean_object* v_key_2642_; lean_object* v_tail_2643_; uint8_t v___x_2644_; 
v_key_2642_ = lean_ctor_get(v_x_2640_, 0);
v_tail_2643_ = lean_ctor_get(v_x_2640_, 2);
v___x_2644_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2642_, v_a_2639_);
if (v___x_2644_ == 0)
{
v_x_2640_ = v_tail_2643_;
goto _start;
}
else
{
return v___x_2644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2646_, lean_object* v_x_2647_){
_start:
{
uint8_t v_res_2648_; lean_object* v_r_2649_; 
v_res_2648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2646_, v_x_2647_);
lean_dec(v_x_2647_);
lean_dec(v_a_2646_);
v_r_2649_ = lean_box(v_res_2648_);
return v_r_2649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2650_, lean_object* v_x_2651_){
_start:
{
if (lean_obj_tag(v_x_2651_) == 0)
{
return v_x_2650_;
}
else
{
lean_object* v_key_2652_; lean_object* v_value_2653_; lean_object* v_tail_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2677_; 
v_key_2652_ = lean_ctor_get(v_x_2651_, 0);
v_value_2653_ = lean_ctor_get(v_x_2651_, 1);
v_tail_2654_ = lean_ctor_get(v_x_2651_, 2);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_x_2651_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2656_ = v_x_2651_;
v_isShared_2657_ = v_isSharedCheck_2677_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_tail_2654_);
lean_inc(v_value_2653_);
lean_inc(v_key_2652_);
lean_dec(v_x_2651_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2677_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; uint64_t v___x_2659_; uint64_t v___x_2660_; uint64_t v___x_2661_; uint64_t v_fold_2662_; uint64_t v___x_2663_; uint64_t v___x_2664_; uint64_t v___x_2665_; size_t v___x_2666_; size_t v___x_2667_; size_t v___x_2668_; size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2658_ = lean_array_get_size(v_x_2650_);
v___x_2659_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2652_);
v___x_2660_ = 32ULL;
v___x_2661_ = lean_uint64_shift_right(v___x_2659_, v___x_2660_);
v_fold_2662_ = lean_uint64_xor(v___x_2659_, v___x_2661_);
v___x_2663_ = 16ULL;
v___x_2664_ = lean_uint64_shift_right(v_fold_2662_, v___x_2663_);
v___x_2665_ = lean_uint64_xor(v_fold_2662_, v___x_2664_);
v___x_2666_ = lean_uint64_to_usize(v___x_2665_);
v___x_2667_ = lean_usize_of_nat(v___x_2658_);
v___x_2668_ = ((size_t)1ULL);
v___x_2669_ = lean_usize_sub(v___x_2667_, v___x_2668_);
v___x_2670_ = lean_usize_land(v___x_2666_, v___x_2669_);
v___x_2671_ = lean_array_uget_borrowed(v_x_2650_, v___x_2670_);
lean_inc(v___x_2671_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 2, v___x_2671_);
v___x_2673_ = v___x_2656_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_key_2652_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_value_2653_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; 
v___x_2674_ = lean_array_uset(v_x_2650_, v___x_2670_, v___x_2673_);
v_x_2650_ = v___x_2674_;
v_x_2651_ = v_tail_2654_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2678_, lean_object* v_source_2679_, lean_object* v_target_2680_){
_start:
{
lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = lean_array_get_size(v_source_2679_);
v___x_2682_ = lean_nat_dec_lt(v_i_2678_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_dec_ref(v_source_2679_);
lean_dec(v_i_2678_);
return v_target_2680_;
}
else
{
lean_object* v_es_2683_; lean_object* v___x_2684_; lean_object* v_source_2685_; lean_object* v_target_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_es_2683_ = lean_array_fget(v_source_2679_, v_i_2678_);
v___x_2684_ = lean_box(0);
v_source_2685_ = lean_array_fset(v_source_2679_, v_i_2678_, v___x_2684_);
v_target_2686_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2680_, v_es_2683_);
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_add(v_i_2678_, v___x_2687_);
lean_dec(v_i_2678_);
v_i_2678_ = v___x_2688_;
v_source_2679_ = v_source_2685_;
v_target_2680_ = v_target_2686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2690_){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v_nbuckets_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2691_ = lean_array_get_size(v_data_2690_);
v___x_2692_ = lean_unsigned_to_nat(2u);
v_nbuckets_2693_ = lean_nat_mul(v___x_2691_, v___x_2692_);
v___x_2694_ = lean_unsigned_to_nat(0u);
v___x_2695_ = lean_box(0);
v___x_2696_ = lean_mk_array(v_nbuckets_2693_, v___x_2695_);
v___x_2697_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2694_, v_data_2690_, v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2698_, lean_object* v_a_2699_, lean_object* v_b_2700_){
_start:
{
lean_object* v_size_2701_; lean_object* v_buckets_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2745_; 
v_size_2701_ = lean_ctor_get(v_m_2698_, 0);
v_buckets_2702_ = lean_ctor_get(v_m_2698_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_m_2698_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2704_ = v_m_2698_;
v_isShared_2705_ = v_isSharedCheck_2745_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_buckets_2702_);
lean_inc(v_size_2701_);
lean_dec(v_m_2698_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2745_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; uint64_t v___x_2707_; uint64_t v___x_2708_; uint64_t v___x_2709_; uint64_t v_fold_2710_; uint64_t v___x_2711_; uint64_t v___x_2712_; uint64_t v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; lean_object* v_bkt_2719_; uint8_t v___x_2720_; 
v___x_2706_ = lean_array_get_size(v_buckets_2702_);
v___x_2707_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2699_);
v___x_2708_ = 32ULL;
v___x_2709_ = lean_uint64_shift_right(v___x_2707_, v___x_2708_);
v_fold_2710_ = lean_uint64_xor(v___x_2707_, v___x_2709_);
v___x_2711_ = 16ULL;
v___x_2712_ = lean_uint64_shift_right(v_fold_2710_, v___x_2711_);
v___x_2713_ = lean_uint64_xor(v_fold_2710_, v___x_2712_);
v___x_2714_ = lean_uint64_to_usize(v___x_2713_);
v___x_2715_ = lean_usize_of_nat(v___x_2706_);
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_sub(v___x_2715_, v___x_2716_);
v___x_2718_ = lean_usize_land(v___x_2714_, v___x_2717_);
v_bkt_2719_ = lean_array_uget_borrowed(v_buckets_2702_, v___x_2718_);
v___x_2720_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2699_, v_bkt_2719_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; lean_object* v_size_x27_2722_; lean_object* v___x_2723_; lean_object* v_buckets_x27_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2721_ = lean_unsigned_to_nat(1u);
v_size_x27_2722_ = lean_nat_add(v_size_2701_, v___x_2721_);
lean_dec(v_size_2701_);
lean_inc(v_bkt_2719_);
v___x_2723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2723_, 0, v_a_2699_);
lean_ctor_set(v___x_2723_, 1, v_b_2700_);
lean_ctor_set(v___x_2723_, 2, v_bkt_2719_);
v_buckets_x27_2724_ = lean_array_uset(v_buckets_2702_, v___x_2718_, v___x_2723_);
v___x_2725_ = lean_unsigned_to_nat(4u);
v___x_2726_ = lean_nat_mul(v_size_x27_2722_, v___x_2725_);
v___x_2727_ = lean_unsigned_to_nat(3u);
v___x_2728_ = lean_nat_div(v___x_2726_, v___x_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_array_get_size(v_buckets_x27_2724_);
v___x_2730_ = lean_nat_dec_le(v___x_2728_, v___x_2729_);
lean_dec(v___x_2728_);
if (v___x_2730_ == 0)
{
lean_object* v_val_2731_; lean_object* v___x_2733_; 
v_val_2731_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2724_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 1, v_val_2731_);
lean_ctor_set(v___x_2704_, 0, v_size_x27_2722_);
v___x_2733_ = v___x_2704_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_size_x27_2722_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_val_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
else
{
lean_object* v___x_2736_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 1, v_buckets_x27_2724_);
lean_ctor_set(v___x_2704_, 0, v_size_x27_2722_);
v___x_2736_ = v___x_2704_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_size_x27_2722_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_buckets_x27_2724_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
else
{
lean_object* v___x_2738_; lean_object* v_buckets_x27_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_inc(v_bkt_2719_);
v___x_2738_ = lean_box(0);
v_buckets_x27_2739_ = lean_array_uset(v_buckets_2702_, v___x_2718_, v___x_2738_);
v___x_2740_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2699_, v_b_2700_, v_bkt_2719_);
v___x_2741_ = lean_array_uset(v_buckets_x27_2739_, v___x_2718_, v___x_2740_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 1, v___x_2741_);
v___x_2743_ = v___x_2704_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_size_2701_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2746_, lean_object* v_x_2747_){
_start:
{
if (lean_obj_tag(v_x_2747_) == 0)
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_box(0);
return v___x_2748_;
}
else
{
lean_object* v_key_2749_; lean_object* v_value_2750_; lean_object* v_tail_2751_; uint8_t v___x_2752_; 
v_key_2749_ = lean_ctor_get(v_x_2747_, 0);
v_value_2750_ = lean_ctor_get(v_x_2747_, 1);
v_tail_2751_ = lean_ctor_get(v_x_2747_, 2);
v___x_2752_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2749_, v_a_2746_);
if (v___x_2752_ == 0)
{
v_x_2747_ = v_tail_2751_;
goto _start;
}
else
{
lean_object* v___x_2754_; 
lean_inc(v_value_2750_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_value_2750_);
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2755_, lean_object* v_x_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2755_, v_x_2756_);
lean_dec(v_x_2756_);
lean_dec(v_a_2755_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v_buckets_2760_; lean_object* v___x_2761_; uint64_t v___x_2762_; uint64_t v___x_2763_; uint64_t v___x_2764_; uint64_t v_fold_2765_; uint64_t v___x_2766_; uint64_t v___x_2767_; uint64_t v___x_2768_; size_t v___x_2769_; size_t v___x_2770_; size_t v___x_2771_; size_t v___x_2772_; size_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_buckets_2760_ = lean_ctor_get(v_m_2758_, 1);
v___x_2761_ = lean_array_get_size(v_buckets_2760_);
v___x_2762_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2759_);
v___x_2763_ = 32ULL;
v___x_2764_ = lean_uint64_shift_right(v___x_2762_, v___x_2763_);
v_fold_2765_ = lean_uint64_xor(v___x_2762_, v___x_2764_);
v___x_2766_ = 16ULL;
v___x_2767_ = lean_uint64_shift_right(v_fold_2765_, v___x_2766_);
v___x_2768_ = lean_uint64_xor(v_fold_2765_, v___x_2767_);
v___x_2769_ = lean_uint64_to_usize(v___x_2768_);
v___x_2770_ = lean_usize_of_nat(v___x_2761_);
v___x_2771_ = ((size_t)1ULL);
v___x_2772_ = lean_usize_sub(v___x_2770_, v___x_2771_);
v___x_2773_ = lean_usize_land(v___x_2769_, v___x_2772_);
v___x_2774_ = lean_array_uget_borrowed(v_buckets_2760_, v___x_2773_);
v___x_2775_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2759_, v___x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2776_, v_a_2777_);
lean_dec(v_a_2777_);
lean_dec_ref(v_m_2776_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2779_, lean_object* v_entry_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_snd_2787_; lean_object* v_snd_2788_; lean_object* v_fst_2789_; lean_object* v_fst_2790_; lean_object* v_snd_2791_; lean_object* v_fst_2792_; lean_object* v_fst_2793_; lean_object* v_snd_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v_snd_2787_ = lean_ctor_get(v_p_2779_, 1);
v_snd_2788_ = lean_ctor_get(v_entry_2780_, 1);
lean_inc(v_snd_2788_);
v_fst_2789_ = lean_ctor_get(v_p_2779_, 0);
v_fst_2790_ = lean_ctor_get(v_snd_2787_, 0);
v_snd_2791_ = lean_ctor_get(v_snd_2787_, 1);
v_fst_2792_ = lean_ctor_get(v_entry_2780_, 0);
lean_inc(v_fst_2792_);
lean_dec_ref(v_entry_2780_);
v_fst_2793_ = lean_ctor_get(v_snd_2788_, 0);
lean_inc(v_fst_2793_);
v_snd_2794_ = lean_ctor_get(v_snd_2788_, 1);
v___x_2795_ = lean_array_get_size(v_fst_2792_);
v___x_2796_ = lean_unsigned_to_nat(0u);
v___x_2797_ = lean_nat_dec_eq(v___x_2795_, v___x_2796_);
if (v___x_2797_ == 0)
{
lean_object* v_fst_2798_; lean_object* v_snd_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2904_; 
v_fst_2798_ = lean_ctor_get(v_fst_2793_, 0);
v_snd_2799_ = lean_ctor_get(v_fst_2793_, 1);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_fst_2793_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2801_ = v_fst_2793_;
v_isShared_2802_ = v_isSharedCheck_2904_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_snd_2799_);
lean_inc(v_fst_2798_);
lean_dec(v_fst_2793_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2904_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v_e_2806_; lean_object* v_todo_2807_; lean_object* v___x_2808_; lean_object* v___f_2809_; lean_object* v___x_2810_; 
v___x_2803_ = l_Lean_instInhabitedExpr;
v___x_2804_ = lean_unsigned_to_nat(1u);
v___x_2805_ = lean_nat_sub(v___x_2795_, v___x_2804_);
v_e_2806_ = lean_array_get(v___x_2803_, v_fst_2792_, v___x_2805_);
lean_dec(v___x_2805_);
v_todo_2807_ = lean_array_pop(v_fst_2792_);
v___x_2808_ = lean_box(v___x_2797_);
v___f_2809_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2809_, 0, v___x_2808_);
lean_closure_set(v___f_2809_, 1, v_todo_2807_);
lean_closure_set(v___f_2809_, 2, v_e_2806_);
v___x_2810_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2798_, v_snd_2799_, v___f_2809_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v_fst_2812_; lean_object* v_snd_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2895_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2810_);
v_fst_2812_ = lean_ctor_get(v_a_2811_, 0);
v_snd_2813_ = lean_ctor_get(v_a_2811_, 1);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_a_2811_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2815_ = v_a_2811_;
v_isShared_2816_ = v_isSharedCheck_2895_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_snd_2813_);
lean_inc(v_fst_2812_);
lean_dec(v_a_2811_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2895_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = lean_box(3);
v___x_2818_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2812_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2791_, v_fst_2812_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v___x_2821_; 
lean_inc(v_snd_2791_);
lean_inc(v_fst_2790_);
lean_inc(v_fst_2789_);
lean_dec_ref(v_p_2779_);
lean_inc(v_snd_2788_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v_snd_2788_);
lean_ctor_set(v___x_2815_, 0, v_snd_2813_);
v___x_2821_ = v___x_2815_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_snd_2813_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_snd_2788_);
v___x_2821_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2841_; 
v_isSharedCheck_2841_ = !lean_is_exclusive(v_snd_2788_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; lean_object* v_unused_2843_; 
v_unused_2842_ = lean_ctor_get(v_snd_2788_, 1);
lean_dec(v_unused_2842_);
v_unused_2843_ = lean_ctor_get(v_snd_2788_, 0);
lean_dec(v_unused_2843_);
v___x_2823_ = v_snd_2788_;
v_isShared_2824_ = v_isSharedCheck_2841_;
goto v_resetjp_2822_;
}
else
{
lean_dec(v_snd_2788_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2841_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2840_; 
v___x_2825_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2821_, v_a_2781_);
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2840_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2840_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
v___x_2830_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2791_, v_fst_2812_, v_a_2826_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 1, v___x_2830_);
lean_ctor_set(v___x_2801_, 0, v_fst_2790_);
v___x_2832_ = v___x_2801_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_fst_2790_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2834_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v___x_2832_);
lean_ctor_set(v___x_2823_, 0, v_fst_2789_);
v___x_2834_ = v___x_2823_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_fst_2789_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
lean_object* v___x_2836_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2834_);
v___x_2836_ = v___x_2828_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2845_; lean_object* v___x_2847_; 
lean_dec(v_fst_2812_);
lean_del_object(v___x_2801_);
v_val_2845_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_val_2845_);
lean_dec_ref(v___x_2819_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v_snd_2788_);
lean_ctor_set(v___x_2815_, 0, v_snd_2813_);
v___x_2847_ = v___x_2815_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_snd_2813_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_snd_2788_);
v___x_2847_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
v___x_2848_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2845_, v___x_2847_, v_a_2781_);
lean_dec(v_val_2845_);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2848_, 0);
lean_dec(v_unused_2856_);
v___x_2850_ = v___x_2848_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_dec(v___x_2848_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v_p_2779_);
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_p_2779_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
else
{
uint8_t v___x_2858_; 
lean_dec(v_fst_2812_);
v___x_2858_ = lean_nat_dec_eq(v_fst_2790_, v___x_2796_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2860_; 
lean_del_object(v___x_2801_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v_snd_2788_);
lean_ctor_set(v___x_2815_, 0, v_snd_2813_);
v___x_2860_ = v___x_2815_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_snd_2813_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_snd_2788_);
v___x_2860_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
v___x_2861_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2790_, v___x_2860_, v_a_2781_);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v___x_2861_, 0);
lean_dec(v_unused_2869_);
v___x_2863_ = v___x_2861_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_dec(v___x_2861_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v_p_2779_);
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_p_2779_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_object* v___x_2872_; 
lean_inc(v_snd_2791_);
lean_inc(v_fst_2789_);
lean_dec_ref(v_p_2779_);
lean_inc(v_snd_2788_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v_snd_2788_);
lean_ctor_set(v___x_2815_, 0, v_snd_2813_);
v___x_2872_ = v___x_2815_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_snd_2813_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_snd_2788_);
v___x_2872_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2891_; 
v_isSharedCheck_2891_ = !lean_is_exclusive(v_snd_2788_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; lean_object* v_unused_2893_; 
v_unused_2892_ = lean_ctor_get(v_snd_2788_, 1);
lean_dec(v_unused_2892_);
v_unused_2893_ = lean_ctor_get(v_snd_2788_, 0);
lean_dec(v_unused_2893_);
v___x_2874_ = v_snd_2788_;
v_isShared_2875_ = v_isSharedCheck_2891_;
goto v_resetjp_2873_;
}
else
{
lean_dec(v_snd_2788_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2891_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2890_; 
v___x_2876_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2872_, v_a_2781_);
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2890_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2890_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 1, v_snd_2791_);
lean_ctor_set(v___x_2801_, 0, v_a_2877_);
v___x_2882_ = v___x_2801_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2877_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_snd_2791_);
v___x_2882_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2884_; 
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 1, v___x_2882_);
lean_ctor_set(v___x_2874_, 0, v_fst_2789_);
v___x_2884_ = v___x_2874_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_fst_2789_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2886_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2884_);
v___x_2886_ = v___x_2879_;
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
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_del_object(v___x_2801_);
lean_dec(v_snd_2788_);
lean_dec_ref(v_p_2779_);
v_a_2896_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2810_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2810_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
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
lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2913_; 
lean_inc(v_snd_2794_);
lean_inc(v_fst_2789_);
lean_inc(v_snd_2787_);
lean_dec(v_fst_2793_);
lean_dec(v_fst_2792_);
lean_dec_ref(v_p_2779_);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_snd_2788_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; lean_object* v_unused_2915_; 
v_unused_2914_ = lean_ctor_get(v_snd_2788_, 1);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_snd_2788_, 0);
lean_dec(v_unused_2915_);
v___x_2906_ = v_snd_2788_;
v_isShared_2907_ = v_isSharedCheck_2913_;
goto v_resetjp_2905_;
}
else
{
lean_dec(v_snd_2788_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2913_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_values_2908_; lean_object* v___x_2910_; 
v_values_2908_ = lean_array_push(v_fst_2789_, v_snd_2794_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 1, v_snd_2787_);
lean_ctor_set(v___x_2906_, 0, v_values_2908_);
v___x_2910_ = v___x_2906_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_values_2908_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_snd_2787_);
v___x_2910_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2916_, lean_object* v_entry_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2916_, v_entry_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_a_2918_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2925_, lean_object* v_p_2926_, lean_object* v_entry_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2926_, v_entry_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2935_, lean_object* v_p_2936_, lean_object* v_entry_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2935_, v_p_2936_, v_entry_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2945_, lean_object* v_m_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2946_, v_a_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2949_, lean_object* v_m_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2949_, v_m_2950_, v_a_2951_);
lean_dec(v_a_2951_);
lean_dec_ref(v_m_2950_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2953_, lean_object* v_m_2954_, lean_object* v_a_2955_, lean_object* v_b_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2954_, v_a_2955_, v_b_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2958_, lean_object* v_a_2959_, lean_object* v_x_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2959_, v_x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2962_, lean_object* v_a_2963_, lean_object* v_x_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_2962_, v_a_2963_, v_x_2964_);
lean_dec(v_x_2964_);
lean_dec(v_a_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_2966_, lean_object* v_a_2967_, lean_object* v_x_2968_){
_start:
{
uint8_t v___x_2969_; 
v___x_2969_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2967_, v_x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2970_, lean_object* v_a_2971_, lean_object* v_x_2972_){
_start:
{
uint8_t v_res_2973_; lean_object* v_r_2974_; 
v_res_2973_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_2970_, v_a_2971_, v_x_2972_);
lean_dec(v_x_2972_);
lean_dec(v_a_2971_);
v_r_2974_ = lean_box(v_res_2973_);
return v_r_2974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_2975_, lean_object* v_data_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_2978_, lean_object* v_a_2979_, lean_object* v_b_2980_, lean_object* v_x_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2979_, v_b_2980_, v_x_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_2983_, lean_object* v_i_2984_, lean_object* v_source_2985_, lean_object* v_target_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_2984_, v_source_2985_, v_target_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_2988_, lean_object* v_x_2989_, lean_object* v_x_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_2989_, v_x_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_2992_, size_t v_i_2993_, size_t v_stop_2994_, lean_object* v_b_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_usize_dec_eq(v_i_2993_, v_stop_2994_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_array_uget_borrowed(v_as_2992_, v_i_2993_);
lean_inc(v___x_3003_);
v___x_3004_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_2995_, v___x_3003_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; size_t v___x_3006_; size_t v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref(v___x_3004_);
v___x_3006_ = ((size_t)1ULL);
v___x_3007_ = lean_usize_add(v_i_2993_, v___x_3006_);
v_i_2993_ = v___x_3007_;
v_b_2995_ = v_a_3005_;
goto _start;
}
else
{
return v___x_3004_;
}
}
else
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_b_2995_);
return v___x_3009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_3010_, lean_object* v_i_3011_, lean_object* v_stop_3012_, lean_object* v_b_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
size_t v_i_boxed_3020_; size_t v_stop_boxed_3021_; lean_object* v_res_3022_; 
v_i_boxed_3020_ = lean_unbox_usize(v_i_3011_);
lean_dec(v_i_3011_);
v_stop_boxed_3021_ = lean_unbox_usize(v_stop_3012_);
lean_dec(v_stop_3012_);
v_res_3022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3010_, v_i_boxed_3020_, v_stop_boxed_3021_, v_b_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v_as_3010_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3023_, lean_object* v_starIdx_3024_, lean_object* v_children_3025_, lean_object* v_entries_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v_starIdx_3024_);
lean_ctor_set(v___x_3033_, 1, v_children_3025_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_values_3023_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = lean_unsigned_to_nat(0u);
v___x_3036_ = lean_array_get_size(v_entries_3026_);
v___x_3037_ = lean_nat_dec_lt(v___x_3035_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3034_);
return v___x_3038_;
}
else
{
uint8_t v___x_3039_; 
v___x_3039_ = lean_nat_dec_le(v___x_3036_, v___x_3036_);
if (v___x_3039_ == 0)
{
if (v___x_3037_ == 0)
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3034_);
return v___x_3040_;
}
else
{
size_t v___x_3041_; size_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3041_ = ((size_t)0ULL);
v___x_3042_ = lean_usize_of_nat(v___x_3036_);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3026_, v___x_3041_, v___x_3042_, v___x_3034_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
return v___x_3043_;
}
}
else
{
size_t v___x_3044_; size_t v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = ((size_t)0ULL);
v___x_3045_ = lean_usize_of_nat(v___x_3036_);
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3026_, v___x_3044_, v___x_3045_, v___x_3034_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
return v___x_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3047_, lean_object* v_starIdx_3048_, lean_object* v_children_3049_, lean_object* v_entries_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3047_, v_starIdx_3048_, v_children_3049_, v_entries_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_entries_3050_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3058_, lean_object* v_values_3059_, lean_object* v_starIdx_3060_, lean_object* v_children_3061_, lean_object* v_entries_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3059_, v_starIdx_3060_, v_children_3061_, v_entries_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3070_, lean_object* v_values_3071_, lean_object* v_starIdx_3072_, lean_object* v_children_3073_, lean_object* v_entries_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3070_, v_values_3071_, v_starIdx_3072_, v_children_3073_, v_entries_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_entries_3074_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3082_, lean_object* v_as_3083_, size_t v_i_3084_, size_t v_stop_3085_, lean_object* v_b_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3083_, v_i_3084_, v_stop_3085_, v_b_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3094_, lean_object* v_as_3095_, lean_object* v_i_3096_, lean_object* v_stop_3097_, lean_object* v_b_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
size_t v_i_boxed_3105_; size_t v_stop_boxed_3106_; lean_object* v_res_3107_; 
v_i_boxed_3105_ = lean_unbox_usize(v_i_3096_);
lean_dec(v_i_3096_);
v_stop_boxed_3106_ = lean_unbox_usize(v_stop_3097_);
lean_dec(v_stop_3097_);
v_res_3107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3094_, v_as_3095_, v_i_boxed_3105_, v_stop_boxed_3106_, v_b_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v_as_3095_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v_values_3120_; lean_object* v_star_3121_; lean_object* v_children_3122_; lean_object* v_pending_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3153_; 
v___x_3117_ = lean_st_ref_get(v_a_3111_);
v___x_3118_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3119_ = lean_array_get(v___x_3118_, v___x_3117_, v_c_3110_);
lean_dec(v___x_3117_);
v_values_3120_ = lean_ctor_get(v___x_3119_, 0);
v_star_3121_ = lean_ctor_get(v___x_3119_, 1);
v_children_3122_ = lean_ctor_get(v___x_3119_, 2);
v_pending_3123_ = lean_ctor_get(v___x_3119_, 3);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3125_ = v___x_3119_;
v_isShared_3126_ = v_isSharedCheck_3153_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_pending_3123_);
lean_inc(v_children_3122_);
lean_inc(v_star_3121_);
lean_inc(v_values_3120_);
lean_dec(v___x_3119_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3153_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3127_ = lean_array_get_size(v_pending_3123_);
v___x_3128_ = lean_unsigned_to_nat(0u);
v___x_3129_ = lean_nat_dec_eq(v___x_3127_, v___x_3128_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3110_, v___x_3118_, v_a_3111_);
lean_dec_ref(v___x_3130_);
v___x_3131_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3120_, v_star_3121_, v_children_3122_, v_pending_3123_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_);
lean_dec_ref(v_pending_3123_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v_snd_3133_; lean_object* v_fst_3134_; lean_object* v_fst_3135_; lean_object* v_snd_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref(v___x_3131_);
v_snd_3133_ = lean_ctor_get(v_a_3132_, 1);
v_fst_3134_ = lean_ctor_get(v_a_3132_, 0);
v_fst_3135_ = lean_ctor_get(v_snd_3133_, 0);
v_snd_3136_ = lean_ctor_get(v_snd_3133_, 1);
v___x_3137_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_evalNode___redArg___closed__0));
lean_inc(v_snd_3136_);
lean_inc(v_fst_3135_);
lean_inc(v_fst_3134_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 3, v___x_3137_);
lean_ctor_set(v___x_3125_, 2, v_snd_3136_);
lean_ctor_set(v___x_3125_, 1, v_fst_3135_);
lean_ctor_set(v___x_3125_, 0, v_fst_3134_);
v___x_3139_ = v___x_3125_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_fst_3134_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_fst_3135_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v_snd_3136_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v___x_3140_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3110_, v___x_3139_, v_a_3111_);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v___x_3140_, 0);
lean_dec(v_unused_3148_);
v___x_3142_ = v___x_3140_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_dec(v___x_3140_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v_a_3132_);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3132_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_del_object(v___x_3125_);
return v___x_3131_;
}
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_del_object(v___x_3125_);
lean_dec_ref(v_pending_3123_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_star_3121_);
lean_ctor_set(v___x_3150_, 1, v_children_3122_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v_values_3120_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
return v___x_3152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec(v_c_3154_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3162_, lean_object* v_c_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3171_, lean_object* v_c_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3171_, v_c_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec(v_a_3173_);
lean_dec(v_c_3172_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3180_, lean_object* v_fallback_3181_, lean_object* v_x_3182_){
_start:
{
if (lean_obj_tag(v_x_3182_) == 0)
{
lean_inc(v_fallback_3181_);
return v_fallback_3181_;
}
else
{
lean_object* v_key_3183_; lean_object* v_value_3184_; lean_object* v_tail_3185_; uint8_t v___x_3186_; 
v_key_3183_ = lean_ctor_get(v_x_3182_, 0);
v_value_3184_ = lean_ctor_get(v_x_3182_, 1);
v_tail_3185_ = lean_ctor_get(v_x_3182_, 2);
v___x_3186_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3183_, v_a_3180_);
if (v___x_3186_ == 0)
{
v_x_3182_ = v_tail_3185_;
goto _start;
}
else
{
lean_inc(v_value_3184_);
return v_value_3184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3188_, lean_object* v_fallback_3189_, lean_object* v_x_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3188_, v_fallback_3189_, v_x_3190_);
lean_dec(v_x_3190_);
lean_dec(v_fallback_3189_);
lean_dec(v_a_3188_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3192_, lean_object* v_a_3193_, lean_object* v_fallback_3194_){
_start:
{
lean_object* v_buckets_3195_; lean_object* v___x_3196_; uint64_t v___x_3197_; uint64_t v___x_3198_; uint64_t v___x_3199_; uint64_t v_fold_3200_; uint64_t v___x_3201_; uint64_t v___x_3202_; uint64_t v___x_3203_; size_t v___x_3204_; size_t v___x_3205_; size_t v___x_3206_; size_t v___x_3207_; size_t v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v_buckets_3195_ = lean_ctor_get(v_m_3192_, 1);
v___x_3196_ = lean_array_get_size(v_buckets_3195_);
v___x_3197_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3193_);
v___x_3198_ = 32ULL;
v___x_3199_ = lean_uint64_shift_right(v___x_3197_, v___x_3198_);
v_fold_3200_ = lean_uint64_xor(v___x_3197_, v___x_3199_);
v___x_3201_ = 16ULL;
v___x_3202_ = lean_uint64_shift_right(v_fold_3200_, v___x_3201_);
v___x_3203_ = lean_uint64_xor(v_fold_3200_, v___x_3202_);
v___x_3204_ = lean_uint64_to_usize(v___x_3203_);
v___x_3205_ = lean_usize_of_nat(v___x_3196_);
v___x_3206_ = ((size_t)1ULL);
v___x_3207_ = lean_usize_sub(v___x_3205_, v___x_3206_);
v___x_3208_ = lean_usize_land(v___x_3204_, v___x_3207_);
v___x_3209_ = lean_array_uget_borrowed(v_buckets_3195_, v___x_3208_);
v___x_3210_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3193_, v_fallback_3194_, v___x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3211_, lean_object* v_a_3212_, lean_object* v_fallback_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3211_, v_a_3212_, v_fallback_3213_);
lean_dec(v_fallback_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_m_3211_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3215_, lean_object* v_rest_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = lean_unsigned_to_nat(0u);
v___x_3224_ = lean_nat_dec_eq(v_next_3215_, v___x_3223_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3215_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3251_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3251_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3251_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_snd_3230_; 
v_snd_3230_ = lean_ctor_get(v_a_3226_, 1);
lean_inc(v_snd_3230_);
lean_dec(v_a_3226_);
if (lean_obj_tag(v_rest_3216_) == 0)
{
lean_object* v_fst_3231_; lean_object* v_snd_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v_fst_3231_ = lean_ctor_get(v_snd_3230_, 0);
lean_inc(v_fst_3231_);
v_snd_3232_ = lean_ctor_get(v_snd_3230_, 1);
lean_inc(v_snd_3232_);
lean_dec(v_snd_3230_);
v___x_3233_ = lean_st_ref_take(v_a_3217_);
v___x_3234_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3234_);
lean_ctor_set(v___x_3235_, 1, v_fst_3231_);
lean_ctor_set(v___x_3235_, 2, v_snd_3232_);
lean_ctor_set(v___x_3235_, 3, v___x_3234_);
v___x_3236_ = lean_array_set(v___x_3233_, v_next_3215_, v___x_3235_);
lean_dec(v_next_3215_);
v___x_3237_ = lean_st_ref_set(v_a_3217_, v___x_3236_);
v___x_3238_ = lean_box(0);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3238_);
v___x_3240_ = v___x_3228_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
else
{
lean_object* v_fst_3242_; lean_object* v_snd_3243_; lean_object* v_head_3244_; lean_object* v_tail_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
lean_del_object(v___x_3228_);
lean_dec(v_next_3215_);
v_fst_3242_ = lean_ctor_get(v_snd_3230_, 0);
lean_inc(v_fst_3242_);
v_snd_3243_ = lean_ctor_get(v_snd_3230_, 1);
lean_inc(v_snd_3243_);
lean_dec(v_snd_3230_);
v_head_3244_ = lean_ctor_get(v_rest_3216_, 0);
v_tail_3245_ = lean_ctor_get(v_rest_3216_, 1);
v___x_3246_ = lean_box(3);
v___x_3247_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3244_, v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; 
lean_dec(v_fst_3242_);
v___x_3248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3243_, v_head_3244_, v___x_3223_);
lean_dec(v_snd_3243_);
v_next_3215_ = v___x_3248_;
v_rest_3216_ = v_tail_3245_;
goto _start;
}
else
{
lean_dec(v_snd_3243_);
v_next_3215_ = v_fst_3242_;
v_rest_3216_ = v_tail_3245_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_next_3215_);
v_a_3252_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3225_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3225_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec(v_next_3215_);
v___x_3260_ = lean_box(0);
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
return v___x_3261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3262_, lean_object* v_rest_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3262_, v_rest_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec(v_rest_3263_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3271_, lean_object* v_next_3272_, lean_object* v_rest_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3272_, v_rest_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3281_, lean_object* v_next_3282_, lean_object* v_rest_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3281_, v_next_3282_, v_rest_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_rest_3283_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3291_, lean_object* v_m_3292_, lean_object* v_a_3293_, lean_object* v_fallback_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3292_, v_a_3293_, v_fallback_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3296_, lean_object* v_m_3297_, lean_object* v_a_3298_, lean_object* v_fallback_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3296_, v_m_3297_, v_a_3298_, v_fallback_3299_);
lean_dec(v_fallback_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_m_3297_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3301_, lean_object* v_a_3302_, lean_object* v_fallback_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3302_, v_fallback_3303_, v_x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3306_, lean_object* v_a_3307_, lean_object* v_fallback_3308_, lean_object* v_x_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3306_, v_a_3307_, v_fallback_3308_, v_x_3309_);
lean_dec(v_x_3309_);
lean_dec(v_fallback_3308_);
lean_dec(v_a_3307_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3311_, lean_object* v_path_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
if (lean_obj_tag(v_path_3312_) == 0)
{
lean_object* v___x_3318_; 
v___x_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3318_, 0, v_t_3311_);
return v___x_3318_;
}
else
{
lean_object* v_head_3319_; lean_object* v_tail_3320_; lean_object* v_roots_3321_; lean_object* v___x_3322_; lean_object* v_idx_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_head_3319_ = lean_ctor_get(v_path_3312_, 0);
lean_inc(v_head_3319_);
v_tail_3320_ = lean_ctor_get(v_path_3312_, 1);
lean_inc(v_tail_3320_);
lean_dec_ref(v_path_3312_);
v_roots_3321_ = lean_ctor_get(v_t_3311_, 1);
v___x_3322_ = lean_unsigned_to_nat(0u);
v_idx_3323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3321_, v_head_3319_, v___x_3322_);
lean_dec(v_head_3319_);
v___x_3324_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3324_, 0, lean_box(0));
lean_closure_set(v___x_3324_, 1, v_idx_3323_);
lean_closure_set(v___x_3324_, 2, v_tail_3320_);
v___x_3325_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3311_, v___x_3324_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3334_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3328_ = v___x_3325_;
v_isShared_3329_ = v_isSharedCheck_3334_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3325_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3334_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v_snd_3330_; lean_object* v___x_3332_; 
v_snd_3330_ = lean_ctor_get(v_a_3326_, 1);
lean_inc(v_snd_3330_);
lean_dec(v_a_3326_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v_snd_3330_);
v___x_3332_ = v___x_3328_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_snd_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
v_a_3335_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3325_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3325_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3343_, lean_object* v_path_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3343_, v_path_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3351_, lean_object* v_t_3352_, lean_object* v_path_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3352_, v_path_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3360_, lean_object* v_t_3361_, lean_object* v_path_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3360_, v_t_3361_, v_path_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3371_, lean_object* v_e_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3374_ = lean_array_get_size(v_a_3373_);
v___x_3375_ = lean_nat_dec_lt(v___x_3374_, v_score_3371_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3376_ = lean_unsigned_to_nat(1u);
v___x_3377_ = lean_mk_empty_array_with_capacity(v___x_3376_);
v___x_3378_ = lean_array_push(v___x_3377_, v_e_3372_);
v___x_3379_ = lean_array_push(v_a_3373_, v___x_3378_);
return v___x_3379_;
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3381_ = lean_array_push(v_a_3373_, v___x_3380_);
v_a_3373_ = v___x_3381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3383_, lean_object* v_e_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3383_, v_e_3384_, v_a_3385_);
lean_dec(v_score_3383_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3387_, lean_object* v_score_3388_, lean_object* v_e_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3388_, v_e_3389_, v_a_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3392_, lean_object* v_score_3393_, lean_object* v_e_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3392_, v_score_3393_, v_e_3394_, v_a_3395_);
lean_dec(v_score_3393_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3397_, lean_object* v_score_3398_, lean_object* v_e_3399_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3400_ = lean_array_get_size(v_e_3399_);
v___x_3401_ = lean_unsigned_to_nat(0u);
v___x_3402_ = lean_nat_dec_eq(v___x_3400_, v___x_3401_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3403_ = lean_array_get_size(v_r_3397_);
v___x_3404_ = lean_nat_dec_lt(v_score_3398_, v___x_3403_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; 
v___x_3405_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3398_, v_e_3399_, v_r_3397_);
return v___x_3405_;
}
else
{
if (v___x_3404_ == 0)
{
lean_dec_ref(v_e_3399_);
return v_r_3397_;
}
else
{
lean_object* v_v_3406_; lean_object* v___x_3407_; lean_object* v_xs_x27_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_v_3406_ = lean_array_fget(v_r_3397_, v_score_3398_);
v___x_3407_ = lean_box(0);
v_xs_x27_3408_ = lean_array_fset(v_r_3397_, v_score_3398_, v___x_3407_);
v___x_3409_ = lean_array_push(v_v_3406_, v_e_3399_);
v___x_3410_ = lean_array_fset(v_xs_x27_3408_, v_score_3398_, v___x_3409_);
return v___x_3410_;
}
}
}
else
{
lean_dec_ref(v_e_3399_);
return v_r_3397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3411_, lean_object* v_score_3412_, lean_object* v_e_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3411_, v_score_3412_, v_e_3413_);
lean_dec(v_score_3412_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3415_, lean_object* v_r_3416_, lean_object* v_score_3417_, lean_object* v_e_3418_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3416_, v_score_3417_, v_e_3418_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3420_, lean_object* v_r_3421_, lean_object* v_score_3422_, lean_object* v_e_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3420_, v_r_3421_, v_score_3422_, v_e_3423_);
lean_dec(v_score_3422_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3425_, size_t v_i_3426_, size_t v_stop_3427_, lean_object* v_b_3428_){
_start:
{
uint8_t v___x_3429_; 
v___x_3429_ = lean_usize_dec_eq(v_i_3426_, v_stop_3427_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; size_t v___x_3433_; size_t v___x_3434_; 
v___x_3430_ = lean_array_uget_borrowed(v_as_3425_, v_i_3426_);
v___x_3431_ = lean_array_get_size(v___x_3430_);
v___x_3432_ = lean_nat_add(v_b_3428_, v___x_3431_);
lean_dec(v_b_3428_);
v___x_3433_ = ((size_t)1ULL);
v___x_3434_ = lean_usize_add(v_i_3426_, v___x_3433_);
v_i_3426_ = v___x_3434_;
v_b_3428_ = v___x_3432_;
goto _start;
}
else
{
return v_b_3428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3436_, lean_object* v_i_3437_, lean_object* v_stop_3438_, lean_object* v_b_3439_){
_start:
{
size_t v_i_boxed_3440_; size_t v_stop_boxed_3441_; lean_object* v_res_3442_; 
v_i_boxed_3440_ = lean_unbox_usize(v_i_3437_);
lean_dec(v_i_3437_);
v_stop_boxed_3441_ = lean_unbox_usize(v_stop_3438_);
lean_dec(v_stop_3438_);
v_res_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3436_, v_i_boxed_3440_, v_stop_boxed_3441_, v_b_3439_);
lean_dec_ref(v_as_3436_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3443_, size_t v_i_3444_, size_t v_stop_3445_, lean_object* v_b_3446_){
_start:
{
lean_object* v___y_3448_; uint8_t v___x_3452_; 
v___x_3452_ = lean_usize_dec_eq(v_i_3444_, v_stop_3445_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v___x_3453_ = lean_array_uget_borrowed(v_as_3443_, v_i_3444_);
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = lean_array_get_size(v___x_3453_);
v___x_3456_ = lean_nat_dec_lt(v___x_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
v___y_3448_ = v_b_3446_;
goto v___jp_3447_;
}
else
{
uint8_t v___x_3457_; 
v___x_3457_ = lean_nat_dec_le(v___x_3455_, v___x_3455_);
if (v___x_3457_ == 0)
{
if (v___x_3456_ == 0)
{
v___y_3448_ = v_b_3446_;
goto v___jp_3447_;
}
else
{
size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = ((size_t)0ULL);
v___x_3459_ = lean_usize_of_nat(v___x_3455_);
v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3453_, v___x_3458_, v___x_3459_, v_b_3446_);
v___y_3448_ = v___x_3460_;
goto v___jp_3447_;
}
}
else
{
size_t v___x_3461_; size_t v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = ((size_t)0ULL);
v___x_3462_ = lean_usize_of_nat(v___x_3455_);
v___x_3463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3453_, v___x_3461_, v___x_3462_, v_b_3446_);
v___y_3448_ = v___x_3463_;
goto v___jp_3447_;
}
}
}
else
{
return v_b_3446_;
}
v___jp_3447_:
{
size_t v___x_3449_; size_t v___x_3450_; 
v___x_3449_ = ((size_t)1ULL);
v___x_3450_ = lean_usize_add(v_i_3444_, v___x_3449_);
v_i_3444_ = v___x_3450_;
v_b_3446_ = v___y_3448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3464_, lean_object* v_i_3465_, lean_object* v_stop_3466_, lean_object* v_b_3467_){
_start:
{
size_t v_i_boxed_3468_; size_t v_stop_boxed_3469_; lean_object* v_res_3470_; 
v_i_boxed_3468_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_stop_boxed_3469_ = lean_unbox_usize(v_stop_3466_);
lean_dec(v_stop_3466_);
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3464_, v_i_boxed_3468_, v_stop_boxed_3469_, v_b_3467_);
lean_dec_ref(v_as_3464_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3471_){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3472_ = lean_unsigned_to_nat(0u);
v___x_3473_ = lean_array_get_size(v_mr_3471_);
v___x_3474_ = lean_nat_dec_lt(v___x_3472_, v___x_3473_);
if (v___x_3474_ == 0)
{
return v___x_3472_;
}
else
{
uint8_t v___x_3475_; 
v___x_3475_ = lean_nat_dec_le(v___x_3473_, v___x_3473_);
if (v___x_3475_ == 0)
{
if (v___x_3474_ == 0)
{
return v___x_3472_;
}
else
{
size_t v___x_3476_; size_t v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = ((size_t)0ULL);
v___x_3477_ = lean_usize_of_nat(v___x_3473_);
v___x_3478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3471_, v___x_3476_, v___x_3477_, v___x_3472_);
return v___x_3478_;
}
}
else
{
size_t v___x_3479_; size_t v___x_3480_; lean_object* v___x_3481_; 
v___x_3479_ = ((size_t)0ULL);
v___x_3480_ = lean_usize_of_nat(v___x_3473_);
v___x_3481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3471_, v___x_3479_, v___x_3480_, v___x_3472_);
return v___x_3481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3482_);
lean_dec_ref(v_mr_3482_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3484_, lean_object* v_mr_3485_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3487_, lean_object* v_mr_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3487_, v_mr_3488_);
lean_dec_ref(v_mr_3488_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3490_, lean_object* v_as_3491_, size_t v_i_3492_, size_t v_stop_3493_, lean_object* v_b_3494_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3491_, v_i_3492_, v_stop_3493_, v_b_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3496_, lean_object* v_as_3497_, lean_object* v_i_3498_, lean_object* v_stop_3499_, lean_object* v_b_3500_){
_start:
{
size_t v_i_boxed_3501_; size_t v_stop_boxed_3502_; lean_object* v_res_3503_; 
v_i_boxed_3501_ = lean_unbox_usize(v_i_3498_);
lean_dec(v_i_3498_);
v_stop_boxed_3502_ = lean_unbox_usize(v_stop_3499_);
lean_dec(v_stop_3499_);
v_res_3503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3496_, v_as_3497_, v_i_boxed_3501_, v_stop_boxed_3502_, v_b_3500_);
lean_dec_ref(v_as_3497_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3504_, lean_object* v_as_3505_, size_t v_i_3506_, size_t v_stop_3507_, lean_object* v_b_3508_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3505_, v_i_3506_, v_stop_3507_, v_b_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3510_, lean_object* v_as_3511_, lean_object* v_i_3512_, lean_object* v_stop_3513_, lean_object* v_b_3514_){
_start:
{
size_t v_i_boxed_3515_; size_t v_stop_boxed_3516_; lean_object* v_res_3517_; 
v_i_boxed_3515_ = lean_unbox_usize(v_i_3512_);
lean_dec(v_i_3512_);
v_stop_boxed_3516_ = lean_unbox_usize(v_stop_3513_);
lean_dec(v_stop_3513_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3510_, v_as_3511_, v_i_boxed_3515_, v_stop_boxed_3516_, v_b_3514_);
lean_dec_ref(v_as_3511_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3518_, lean_object* v_j_3519_, lean_object* v_x_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_apply_2(v_f_3518_, v_j_3519_, v_x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3541_, lean_object* v_x1_3542_, lean_object* v_x2_3543_){
_start:
{
lean_object* v___x_3544_; size_t v_sz_3545_; size_t v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3544_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3545_ = lean_array_size(v_x2_3543_);
v___x_3546_ = ((size_t)0ULL);
v___x_3547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3544_, v___f_3541_, v_sz_3545_, v___x_3546_, v_x2_3543_);
v___x_3548_ = l_Array_append___redArg(v_x1_3542_, v___x_3547_);
lean_dec(v___x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3549_, lean_object* v_mr_3550_, lean_object* v_f_3551_, lean_object* v_i_3552_, lean_object* v_x_3553_, lean_object* v_r_3554_){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v_j_3557_; lean_object* v_b_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3555_ = lean_unsigned_to_nat(1u);
v___x_3556_ = lean_nat_sub(v_n_3549_, v___x_3555_);
v_j_3557_ = lean_nat_sub(v___x_3556_, v_i_3552_);
lean_dec(v___x_3556_);
v_b_3558_ = lean_array_fget_borrowed(v_mr_3550_, v_j_3557_);
v___x_3559_ = lean_unsigned_to_nat(0u);
v___x_3560_ = lean_array_get_size(v_b_3558_);
v___x_3561_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3562_ = lean_nat_dec_lt(v___x_3559_, v___x_3560_);
if (v___x_3562_ == 0)
{
lean_dec(v_j_3557_);
lean_dec(v_f_3551_);
return v_r_3554_;
}
else
{
lean_object* v___f_3563_; lean_object* v___f_3564_; uint8_t v___x_3565_; 
v___f_3563_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3563_, 0, v_f_3551_);
lean_closure_set(v___f_3563_, 1, v_j_3557_);
v___f_3564_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3564_, 0, v___f_3563_);
v___x_3565_ = lean_nat_dec_le(v___x_3560_, v___x_3560_);
if (v___x_3565_ == 0)
{
if (v___x_3562_ == 0)
{
lean_dec_ref(v___f_3564_);
return v_r_3554_;
}
else
{
size_t v___x_3566_; size_t v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = ((size_t)0ULL);
v___x_3567_ = lean_usize_of_nat(v___x_3560_);
lean_inc(v_b_3558_);
v___x_3568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3561_, v___f_3564_, v_b_3558_, v___x_3566_, v___x_3567_, v_r_3554_);
return v___x_3568_;
}
}
else
{
size_t v___x_3569_; size_t v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = ((size_t)0ULL);
v___x_3570_ = lean_usize_of_nat(v___x_3560_);
lean_inc(v_b_3558_);
v___x_3571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3561_, v___f_3564_, v_b_3558_, v___x_3569_, v___x_3570_, v_r_3554_);
return v___x_3571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3572_, lean_object* v_mr_3573_, lean_object* v_f_3574_, lean_object* v_i_3575_, lean_object* v_x_3576_, lean_object* v_r_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3572_, v_mr_3573_, v_f_3574_, v_i_3575_, v_x_3576_, v_r_3577_);
lean_dec(v_i_3575_);
lean_dec_ref(v_mr_3573_);
lean_dec(v_n_3572_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3579_, lean_object* v_a_3580_, lean_object* v_f_3581_){
_start:
{
lean_object* v_n_3582_; lean_object* v___f_3583_; lean_object* v___x_3584_; 
v_n_3582_ = lean_array_get_size(v_mr_3579_);
v___f_3583_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3583_, 0, v_n_3582_);
lean_closure_set(v___f_3583_, 1, v_mr_3579_);
lean_closure_set(v___f_3583_, 2, v_f_3581_);
v___x_3584_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3582_, v___f_3583_, v_n_3582_, lean_box(0), v_a_3580_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3585_, lean_object* v_00_u03b2_3586_, lean_object* v_mr_3587_, lean_object* v_a_3588_, lean_object* v_f_3589_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3587_, v_a_3588_, v_f_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3591_, size_t v_i_3592_, lean_object* v_bs_3593_){
_start:
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_usize_dec_lt(v_i_3592_, v_sz_3591_);
if (v___x_3594_ == 0)
{
return v_bs_3593_;
}
else
{
lean_object* v_v_3595_; lean_object* v___x_3596_; lean_object* v_bs_x27_3597_; size_t v___x_3598_; size_t v___x_3599_; lean_object* v___x_3600_; 
v_v_3595_ = lean_array_uget(v_bs_3593_, v_i_3592_);
v___x_3596_ = lean_unsigned_to_nat(0u);
v_bs_x27_3597_ = lean_array_uset(v_bs_3593_, v_i_3592_, v___x_3596_);
v___x_3598_ = ((size_t)1ULL);
v___x_3599_ = lean_usize_add(v_i_3592_, v___x_3598_);
v___x_3600_ = lean_array_uset(v_bs_x27_3597_, v_i_3592_, v_v_3595_);
v_i_3592_ = v___x_3599_;
v_bs_3593_ = v___x_3600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3602_, lean_object* v_i_3603_, lean_object* v_bs_3604_){
_start:
{
size_t v_sz_boxed_3605_; size_t v_i_boxed_3606_; lean_object* v_res_3607_; 
v_sz_boxed_3605_ = lean_unbox_usize(v_sz_3602_);
lean_dec(v_sz_3602_);
v_i_boxed_3606_ = lean_unbox_usize(v_i_3603_);
lean_dec(v_i_3603_);
v_res_3607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3605_, v_i_boxed_3606_, v_bs_3604_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3608_, size_t v_i_3609_, size_t v_stop_3610_, lean_object* v_b_3611_){
_start:
{
uint8_t v___x_3612_; 
v___x_3612_ = lean_usize_dec_eq(v_i_3609_, v_stop_3610_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; size_t v_sz_3614_; size_t v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; size_t v___x_3618_; size_t v___x_3619_; 
v___x_3613_ = lean_array_uget_borrowed(v_as_3608_, v_i_3609_);
v_sz_3614_ = lean_array_size(v___x_3613_);
v___x_3615_ = ((size_t)0ULL);
lean_inc(v___x_3613_);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3614_, v___x_3615_, v___x_3613_);
v___x_3617_ = l_Array_append___redArg(v_b_3611_, v___x_3616_);
lean_dec_ref(v___x_3616_);
v___x_3618_ = ((size_t)1ULL);
v___x_3619_ = lean_usize_add(v_i_3609_, v___x_3618_);
v_i_3609_ = v___x_3619_;
v_b_3611_ = v___x_3617_;
goto _start;
}
else
{
return v_b_3611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3621_, lean_object* v_i_3622_, lean_object* v_stop_3623_, lean_object* v_b_3624_){
_start:
{
size_t v_i_boxed_3625_; size_t v_stop_boxed_3626_; lean_object* v_res_3627_; 
v_i_boxed_3625_ = lean_unbox_usize(v_i_3622_);
lean_dec(v_i_3622_);
v_stop_boxed_3626_ = lean_unbox_usize(v_stop_3623_);
lean_dec(v_stop_3623_);
v_res_3627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3621_, v_i_boxed_3625_, v_stop_boxed_3626_, v_b_3624_);
lean_dec_ref(v_as_3621_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3628_, lean_object* v_aa_3629_, lean_object* v_n_3630_, lean_object* v_j_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_zero_3633_; uint8_t v_isZero_3634_; 
v_zero_3633_ = lean_unsigned_to_nat(0u);
v_isZero_3634_ = lean_nat_dec_eq(v_j_3631_, v_zero_3633_);
if (v_isZero_3634_ == 1)
{
lean_dec(v_j_3631_);
return v_a_3632_;
}
else
{
lean_object* v_one_3635_; lean_object* v_n_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v_j_3639_; lean_object* v_b_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; 
v_one_3635_ = lean_unsigned_to_nat(1u);
v_n_3636_ = lean_nat_sub(v_j_3631_, v_one_3635_);
v___x_3637_ = lean_nat_sub(v_n_3630_, v_j_3631_);
lean_dec(v_j_3631_);
v___x_3638_ = lean_nat_sub(v_n_3628_, v_one_3635_);
v_j_3639_ = lean_nat_sub(v___x_3638_, v___x_3637_);
lean_dec(v___x_3637_);
lean_dec(v___x_3638_);
v_b_3640_ = lean_array_fget_borrowed(v_aa_3629_, v_j_3639_);
lean_dec(v_j_3639_);
v___x_3641_ = lean_array_get_size(v_b_3640_);
v___x_3642_ = lean_nat_dec_lt(v_zero_3633_, v___x_3641_);
if (v___x_3642_ == 0)
{
v_j_3631_ = v_n_3636_;
goto _start;
}
else
{
uint8_t v___x_3644_; 
v___x_3644_ = lean_nat_dec_le(v___x_3641_, v___x_3641_);
if (v___x_3644_ == 0)
{
if (v___x_3642_ == 0)
{
v_j_3631_ = v_n_3636_;
goto _start;
}
else
{
size_t v___x_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v___x_3646_ = ((size_t)0ULL);
v___x_3647_ = lean_usize_of_nat(v___x_3641_);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3640_, v___x_3646_, v___x_3647_, v_a_3632_);
v_j_3631_ = v_n_3636_;
v_a_3632_ = v___x_3648_;
goto _start;
}
}
else
{
size_t v___x_3650_; size_t v___x_3651_; lean_object* v___x_3652_; 
v___x_3650_ = ((size_t)0ULL);
v___x_3651_ = lean_usize_of_nat(v___x_3641_);
v___x_3652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3640_, v___x_3650_, v___x_3651_, v_a_3632_);
v_j_3631_ = v_n_3636_;
v_a_3632_ = v___x_3652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3654_, lean_object* v_aa_3655_, lean_object* v_n_3656_, lean_object* v_j_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3654_, v_aa_3655_, v_n_3656_, v_j_3657_, v_a_3658_);
lean_dec(v_n_3656_);
lean_dec_ref(v_aa_3655_);
lean_dec(v_n_3654_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v_n_3662_; lean_object* v___x_3663_; 
v_n_3662_ = lean_array_get_size(v_mr_3660_);
v___x_3663_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3662_, v_mr_3660_, v_n_3662_, v_n_3662_, v_a_3661_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3664_, v_a_3665_);
lean_dec_ref(v_mr_3664_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3667_, v_a_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3670_, lean_object* v_a_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3670_, v_a_3671_);
lean_dec_ref(v_mr_3670_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3673_, lean_object* v_mr_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3674_, v_a_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3677_, lean_object* v_mr_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3677_, v_mr_3678_, v_a_3679_);
lean_dec_ref(v_mr_3678_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3681_, lean_object* v_mr_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3682_, v_a_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3685_, lean_object* v_mr_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3685_, v_mr_3686_, v_a_3687_);
lean_dec_ref(v_mr_3686_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3689_, size_t v_sz_3690_, size_t v_i_3691_, lean_object* v_bs_3692_){
_start:
{
lean_object* v___x_3693_; 
v___x_3693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3690_, v_i_3691_, v_bs_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3694_, lean_object* v_sz_3695_, lean_object* v_i_3696_, lean_object* v_bs_3697_){
_start:
{
size_t v_sz_boxed_3698_; size_t v_i_boxed_3699_; lean_object* v_res_3700_; 
v_sz_boxed_3698_ = lean_unbox_usize(v_sz_3695_);
lean_dec(v_sz_3695_);
v_i_boxed_3699_ = lean_unbox_usize(v_i_3696_);
lean_dec(v_i_3696_);
v_res_3700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3694_, v_sz_boxed_3698_, v_i_boxed_3699_, v_bs_3697_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3701_, lean_object* v_as_3702_, size_t v_i_3703_, size_t v_stop_3704_, lean_object* v_b_3705_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3702_, v_i_3703_, v_stop_3704_, v_b_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3707_, lean_object* v_as_3708_, lean_object* v_i_3709_, lean_object* v_stop_3710_, lean_object* v_b_3711_){
_start:
{
size_t v_i_boxed_3712_; size_t v_stop_boxed_3713_; lean_object* v_res_3714_; 
v_i_boxed_3712_ = lean_unbox_usize(v_i_3709_);
lean_dec(v_i_3709_);
v_stop_boxed_3713_ = lean_unbox_usize(v_stop_3710_);
lean_dec(v_stop_3710_);
v_res_3714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3707_, v_as_3708_, v_i_boxed_3712_, v_stop_boxed_3713_, v_b_3711_);
lean_dec_ref(v_as_3708_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3715_, lean_object* v_n_3716_, lean_object* v_aa_3717_, lean_object* v_n_3718_, lean_object* v_j_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3716_, v_aa_3717_, v_n_3718_, v_j_3719_, v_a_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3723_, lean_object* v_n_3724_, lean_object* v_aa_3725_, lean_object* v_n_3726_, lean_object* v_j_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3723_, v_n_3724_, v_aa_3725_, v_n_3726_, v_j_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_n_3726_);
lean_dec_ref(v_aa_3725_);
lean_dec(v_n_3724_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3738_, lean_object* v___x_3739_, lean_object* v_score_3740_, lean_object* v___x_3741_, lean_object* v_k_3742_, lean_object* v_args_3743_, lean_object* v_cases_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3738_, v_k_3742_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_dec_ref(v___x_3739_);
return v_cases_3744_;
}
else
{
lean_object* v_val_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_val_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_val_3746_);
lean_dec_ref(v___x_3745_);
v___x_3747_ = l_Array_append___redArg(v___x_3739_, v_args_3743_);
v___x_3748_ = lean_nat_add(v_score_3740_, v___x_3741_);
v___x_3749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
lean_ctor_set(v___x_3749_, 2, v_val_3746_);
v___x_3750_ = lean_array_push(v_cases_3744_, v___x_3749_);
return v___x_3750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3751_, lean_object* v___x_3752_, lean_object* v_score_3753_, lean_object* v___x_3754_, lean_object* v_k_3755_, lean_object* v_args_3756_, lean_object* v_cases_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3751_, v___x_3752_, v_score_3753_, v___x_3754_, v_k_3755_, v_args_3756_, v_cases_3757_);
lean_dec_ref(v_args_3756_);
lean_dec(v_k_3755_);
lean_dec(v___x_3754_);
lean_dec(v_score_3753_);
lean_dec_ref(v_snd_3751_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3759_, lean_object* v_result_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; uint8_t v___x_3769_; 
v___x_3767_ = lean_array_get_size(v_cases_3759_);
v___x_3768_ = lean_unsigned_to_nat(0u);
v___x_3769_ = lean_nat_dec_eq(v___x_3767_, v___x_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v_ca_3773_; lean_object* v_todo_3774_; lean_object* v_score_3775_; lean_object* v_c_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3842_; 
v___x_3770_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3771_ = lean_unsigned_to_nat(1u);
v___x_3772_ = lean_nat_sub(v___x_3767_, v___x_3771_);
v_ca_3773_ = lean_array_get(v___x_3770_, v_cases_3759_, v___x_3772_);
lean_dec(v___x_3772_);
v_todo_3774_ = lean_ctor_get(v_ca_3773_, 0);
v_score_3775_ = lean_ctor_get(v_ca_3773_, 1);
v_c_3776_ = lean_ctor_get(v_ca_3773_, 2);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_ca_3773_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3778_ = v_ca_3773_;
v_isShared_3779_ = v_isSharedCheck_3842_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_c_3776_);
lean_inc(v_score_3775_);
lean_inc(v_todo_3774_);
lean_dec(v_ca_3773_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3842_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3776_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_);
lean_dec(v_c_3776_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; uint8_t v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v_snd_3809_; lean_object* v_fst_3810_; lean_object* v_fst_3811_; lean_object* v_snd_3812_; lean_object* v_cases_3813_; lean_object* v___x_3814_; uint8_t v___y_3816_; uint8_t v___x_3828_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref(v___x_3780_);
v_snd_3809_ = lean_ctor_get(v_a_3781_, 1);
lean_inc(v_snd_3809_);
v_fst_3810_ = lean_ctor_get(v_a_3781_, 0);
lean_inc(v_fst_3810_);
lean_dec(v_a_3781_);
v_fst_3811_ = lean_ctor_get(v_snd_3809_, 0);
lean_inc(v_fst_3811_);
v_snd_3812_ = lean_ctor_get(v_snd_3809_, 1);
lean_inc(v_snd_3812_);
lean_dec(v_snd_3809_);
v_cases_3813_ = lean_array_pop(v_cases_3759_);
v___x_3814_ = lean_array_get_size(v_todo_3774_);
v___x_3828_ = lean_nat_dec_eq(v___x_3814_, v___x_3768_);
if (v___x_3828_ == 0)
{
uint8_t v___x_3829_; 
lean_dec(v_fst_3810_);
v___x_3829_ = lean_nat_dec_eq(v_fst_3811_, v___x_3768_);
if (v___x_3829_ == 0)
{
v___y_3816_ = v___x_3829_;
goto v___jp_3815_;
}
else
{
lean_object* v_size_3830_; uint8_t v___x_3831_; 
v_size_3830_ = lean_ctor_get(v_snd_3812_, 0);
v___x_3831_ = lean_nat_dec_eq(v_size_3830_, v___x_3768_);
v___y_3816_ = v___x_3831_;
goto v___jp_3815_;
}
}
else
{
lean_object* v___x_3832_; 
lean_dec(v_snd_3812_);
lean_dec(v_fst_3811_);
lean_del_object(v___x_3778_);
lean_dec_ref(v_todo_3774_);
v___x_3832_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3760_, v_score_3775_, v_fst_3810_);
lean_dec(v_score_3775_);
v_cases_3759_ = v_cases_3813_;
v_result_3760_ = v___x_3832_;
goto _start;
}
v___jp_3782_:
{
uint8_t v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = 1;
v___x_3788_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3784_, v___x_3787_, v___y_3783_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v_fst_3790_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref(v___x_3788_);
v_fst_3790_ = lean_ctor_get(v_a_3789_, 0);
lean_inc(v_fst_3790_);
switch(lean_obj_tag(v_fst_3790_))
{
case 3:
{
lean_dec(v_a_3789_);
lean_dec_ref(v___y_3785_);
v_cases_3759_ = v___y_3786_;
goto _start;
}
case 5:
{
lean_object* v_snd_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_snd_3792_ = lean_ctor_get(v_a_3789_, 1);
lean_inc(v_snd_3792_);
lean_dec(v_a_3789_);
v___x_3793_ = lean_box(4);
v___x_3794_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3785_);
v___x_3795_ = lean_apply_3(v___y_3785_, v___x_3793_, v___x_3794_, v___y_3786_);
v___x_3796_ = lean_apply_3(v___y_3785_, v_fst_3790_, v_snd_3792_, v___x_3795_);
v_cases_3759_ = v___x_3796_;
goto _start;
}
default: 
{
lean_object* v_snd_3798_; lean_object* v___x_3799_; 
v_snd_3798_ = lean_ctor_get(v_a_3789_, 1);
lean_inc(v_snd_3798_);
lean_dec(v_a_3789_);
v___x_3799_ = lean_apply_3(v___y_3785_, v_fst_3790_, v_snd_3798_, v___y_3786_);
v_cases_3759_ = v___x_3799_;
goto _start;
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec_ref(v_result_3760_);
v_a_3801_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3788_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3788_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
v___jp_3815_:
{
if (v___y_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___f_3821_; uint8_t v___x_3822_; 
v___x_3817_ = l_Lean_instInhabitedExpr;
v___x_3818_ = lean_nat_sub(v___x_3814_, v___x_3771_);
v___x_3819_ = lean_array_get(v___x_3817_, v_todo_3774_, v___x_3818_);
lean_dec(v___x_3818_);
v___x_3820_ = lean_array_pop(v_todo_3774_);
lean_inc(v_score_3775_);
lean_inc_ref(v___x_3820_);
v___f_3821_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3821_, 0, v_snd_3812_);
lean_closure_set(v___f_3821_, 1, v___x_3820_);
lean_closure_set(v___f_3821_, 2, v_score_3775_);
lean_closure_set(v___f_3821_, 3, v___x_3771_);
v___x_3822_ = lean_nat_dec_eq(v_fst_3811_, v___x_3768_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3824_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 2, v_fst_3811_);
lean_ctor_set(v___x_3778_, 0, v___x_3820_);
v___x_3824_ = v___x_3778_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_score_3775_);
lean_ctor_set(v_reuseFailAlloc_3826_, 2, v_fst_3811_);
v___x_3824_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3825_; 
v___x_3825_ = lean_array_push(v_cases_3813_, v___x_3824_);
v___y_3783_ = v___y_3816_;
v___y_3784_ = v___x_3819_;
v___y_3785_ = v___f_3821_;
v___y_3786_ = v___x_3825_;
goto v___jp_3782_;
}
}
else
{
lean_dec_ref(v___x_3820_);
lean_dec(v_fst_3811_);
lean_del_object(v___x_3778_);
lean_dec(v_score_3775_);
v___y_3783_ = v___y_3816_;
v___y_3784_ = v___x_3819_;
v___y_3785_ = v___f_3821_;
v___y_3786_ = v_cases_3813_;
goto v___jp_3782_;
}
}
else
{
lean_dec(v_snd_3812_);
lean_dec(v_fst_3811_);
lean_del_object(v___x_3778_);
lean_dec(v_score_3775_);
lean_dec_ref(v_todo_3774_);
v_cases_3759_ = v_cases_3813_;
goto _start;
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_del_object(v___x_3778_);
lean_dec(v_score_3775_);
lean_dec_ref(v_todo_3774_);
lean_dec_ref(v_result_3760_);
lean_dec_ref(v_cases_3759_);
v_a_3834_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3780_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3780_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
else
{
lean_object* v___x_3843_; 
lean_dec_ref(v_cases_3759_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_result_3760_);
return v___x_3843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3844_, lean_object* v_result_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3844_, v_result_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
lean_dec(v_a_3846_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3853_, lean_object* v_cases_3854_, lean_object* v_result_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3854_, v_result_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3863_, lean_object* v_cases_3864_, lean_object* v_result_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3863_, v_cases_3864_, v_result_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_box(3);
v___x_3883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3875_, v___x_3882_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
return v___x_3885_;
}
else
{
lean_object* v_val_3886_; lean_object* v___x_3887_; 
v_val_3886_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_val_3886_);
lean_dec_ref(v___x_3883_);
v___x_3887_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3886_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_);
lean_dec(v_val_3886_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3899_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3890_ = v___x_3887_;
v_isShared_3891_ = v_isSharedCheck_3899_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3887_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3899_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v_fst_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
v_fst_3892_ = lean_ctor_get(v_a_3888_, 0);
lean_inc(v_fst_3892_);
lean_dec(v_a_3888_);
v___x_3893_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3894_ = lean_unsigned_to_nat(1u);
v___x_3895_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3893_, v___x_3894_, v_fst_3892_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 0, v___x_3895_);
v___x_3897_ = v___x_3890_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
v_a_3900_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3887_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3887_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_root_3908_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3916_, lean_object* v_root_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3925_, lean_object* v_root_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3925_, v_root_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec_ref(v_root_3926_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3934_, lean_object* v_k_3935_, lean_object* v_args_3936_, lean_object* v_cases_3937_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3934_, v_k_3935_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_dec_ref(v_args_3936_);
return v_cases_3937_;
}
else
{
lean_object* v_val_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_val_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_val_3939_);
lean_dec_ref(v___x_3938_);
v___x_3940_ = lean_unsigned_to_nat(1u);
v___x_3941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3941_, 0, v_args_3936_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
lean_ctor_set(v___x_3941_, 2, v_val_3939_);
v___x_3942_ = lean_array_push(v_cases_3937_, v___x_3941_);
return v___x_3942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3943_, lean_object* v_k_3944_, lean_object* v_args_3945_, lean_object* v_cases_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3943_, v_k_3944_, v_args_3945_, v_cases_3946_);
lean_dec(v_k_3944_);
lean_dec_ref(v_r_3943_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3950_, lean_object* v_e_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3950_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; uint8_t v___x_3960_; lean_object* v___x_3961_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref(v___x_3958_);
v___x_3960_ = 1;
v___x_3961_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3951_, v___x_3960_, v___x_3960_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v_fst_3963_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref(v___x_3961_);
v_fst_3963_ = lean_ctor_get(v_a_3962_, 0);
lean_inc(v_fst_3963_);
switch(lean_obj_tag(v_fst_3963_))
{
case 3:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_dec(v_a_3962_);
v___x_3964_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3965_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3964_, v_a_3959_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
return v___x_3965_;
}
case 5:
{
lean_object* v_snd_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v_snd_3966_ = lean_ctor_get(v_a_3962_, 1);
lean_inc(v_snd_3966_);
lean_dec(v_a_3962_);
v___x_3967_ = lean_box(4);
v___x_3968_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_3969_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3950_, v___x_3967_, v___x_3968_, v___x_3968_);
v___x_3970_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3950_, v_fst_3963_, v_snd_3966_, v___x_3969_);
v___x_3971_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3970_, v_a_3959_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
return v___x_3971_;
}
default: 
{
lean_object* v_snd_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v_snd_3972_ = lean_ctor_get(v_a_3962_, 1);
lean_inc(v_snd_3972_);
lean_dec(v_a_3962_);
v___x_3973_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3974_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3950_, v_fst_3963_, v_snd_3972_, v___x_3973_);
lean_dec(v_fst_3963_);
v___x_3975_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3974_, v_a_3959_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
return v___x_3975_;
}
}
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
lean_dec(v_a_3959_);
v_a_3976_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3961_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3961_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
else
{
lean_dec_ref(v_e_3951_);
return v___x_3958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_3984_, lean_object* v_e_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3984_, v_e_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_a_3986_);
lean_dec_ref(v_root_3984_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_3993_, lean_object* v_root_3994_, lean_object* v_e_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3994_, v_e_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_4003_, lean_object* v_root_4004_, lean_object* v_e_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_4003_, v_root_4004_, v_e_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
lean_dec(v_a_4006_);
lean_dec_ref(v_root_4004_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_4013_, lean_object* v_e_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v_roots_4020_; lean_object* v___x_4021_; uint8_t v_foApprox_4022_; uint8_t v_ctxApprox_4023_; uint8_t v_quasiPatternApprox_4024_; uint8_t v_constApprox_4025_; uint8_t v_isDefEqStuckEx_4026_; uint8_t v_unificationHints_4027_; uint8_t v_proofIrrelevance_4028_; uint8_t v_assignSyntheticOpaque_4029_; uint8_t v_offsetCnstrs_4030_; uint8_t v_etaStruct_4031_; uint8_t v_univApprox_4032_; uint8_t v_iota_4033_; uint8_t v_beta_4034_; uint8_t v_proj_4035_; uint8_t v_zeta_4036_; uint8_t v_zetaDelta_4037_; uint8_t v_zetaUnused_4038_; uint8_t v_zetaHave_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4067_; 
v_roots_4020_ = lean_ctor_get(v_d_4013_, 1);
v___x_4021_ = l_Lean_Meta_Context_config(v_a_4015_);
v_foApprox_4022_ = lean_ctor_get_uint8(v___x_4021_, 0);
v_ctxApprox_4023_ = lean_ctor_get_uint8(v___x_4021_, 1);
v_quasiPatternApprox_4024_ = lean_ctor_get_uint8(v___x_4021_, 2);
v_constApprox_4025_ = lean_ctor_get_uint8(v___x_4021_, 3);
v_isDefEqStuckEx_4026_ = lean_ctor_get_uint8(v___x_4021_, 4);
v_unificationHints_4027_ = lean_ctor_get_uint8(v___x_4021_, 5);
v_proofIrrelevance_4028_ = lean_ctor_get_uint8(v___x_4021_, 6);
v_assignSyntheticOpaque_4029_ = lean_ctor_get_uint8(v___x_4021_, 7);
v_offsetCnstrs_4030_ = lean_ctor_get_uint8(v___x_4021_, 8);
v_etaStruct_4031_ = lean_ctor_get_uint8(v___x_4021_, 10);
v_univApprox_4032_ = lean_ctor_get_uint8(v___x_4021_, 11);
v_iota_4033_ = lean_ctor_get_uint8(v___x_4021_, 12);
v_beta_4034_ = lean_ctor_get_uint8(v___x_4021_, 13);
v_proj_4035_ = lean_ctor_get_uint8(v___x_4021_, 14);
v_zeta_4036_ = lean_ctor_get_uint8(v___x_4021_, 15);
v_zetaDelta_4037_ = lean_ctor_get_uint8(v___x_4021_, 16);
v_zetaUnused_4038_ = lean_ctor_get_uint8(v___x_4021_, 17);
v_zetaHave_4039_ = lean_ctor_get_uint8(v___x_4021_, 18);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4041_ = v___x_4021_;
v_isShared_4042_ = v_isSharedCheck_4067_;
goto v_resetjp_4040_;
}
else
{
lean_dec(v___x_4021_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4067_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
uint8_t v_trackZetaDelta_4043_; lean_object* v_zetaDeltaSet_4044_; lean_object* v_lctx_4045_; lean_object* v_localInstances_4046_; lean_object* v_defEqCtx_x3f_4047_; lean_object* v_synthPendingDepth_4048_; lean_object* v_canUnfold_x3f_4049_; uint8_t v_univApprox_4050_; uint8_t v_inTypeClassResolution_4051_; uint8_t v_cacheInferType_4052_; uint8_t v___x_4053_; lean_object* v_config_4055_; 
v_trackZetaDelta_4043_ = lean_ctor_get_uint8(v_a_4015_, sizeof(void*)*7);
v_zetaDeltaSet_4044_ = lean_ctor_get(v_a_4015_, 1);
v_lctx_4045_ = lean_ctor_get(v_a_4015_, 2);
v_localInstances_4046_ = lean_ctor_get(v_a_4015_, 3);
v_defEqCtx_x3f_4047_ = lean_ctor_get(v_a_4015_, 4);
v_synthPendingDepth_4048_ = lean_ctor_get(v_a_4015_, 5);
v_canUnfold_x3f_4049_ = lean_ctor_get(v_a_4015_, 6);
v_univApprox_4050_ = lean_ctor_get_uint8(v_a_4015_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4051_ = lean_ctor_get_uint8(v_a_4015_, sizeof(void*)*7 + 2);
v_cacheInferType_4052_ = lean_ctor_get_uint8(v_a_4015_, sizeof(void*)*7 + 3);
v___x_4053_ = 2;
if (v_isShared_4042_ == 0)
{
v_config_4055_ = v___x_4041_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 0, v_foApprox_4022_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 1, v_ctxApprox_4023_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 2, v_quasiPatternApprox_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 3, v_constApprox_4025_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 4, v_isDefEqStuckEx_4026_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 5, v_unificationHints_4027_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 6, v_proofIrrelevance_4028_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 7, v_assignSyntheticOpaque_4029_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 8, v_offsetCnstrs_4030_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 10, v_etaStruct_4031_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 11, v_univApprox_4032_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 12, v_iota_4033_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 13, v_beta_4034_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 14, v_proj_4035_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 15, v_zeta_4036_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 16, v_zetaDelta_4037_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 17, v_zetaUnused_4038_);
lean_ctor_set_uint8(v_reuseFailAlloc_4066_, 18, v_zetaHave_4039_);
v_config_4055_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
uint64_t v___x_4056_; uint64_t v___x_4057_; uint64_t v___x_4058_; lean_object* v___x_4059_; uint64_t v___x_4060_; uint64_t v___x_4061_; uint64_t v_key_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_ctor_set_uint8(v_config_4055_, 9, v___x_4053_);
v___x_4056_ = l_Lean_Meta_Context_configKey(v_a_4015_);
v___x_4057_ = 2ULL;
v___x_4058_ = lean_uint64_shift_right(v___x_4056_, v___x_4057_);
lean_inc_ref(v_roots_4020_);
v___x_4059_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4059_, 0, lean_box(0));
lean_closure_set(v___x_4059_, 1, v_roots_4020_);
lean_closure_set(v___x_4059_, 2, v_e_4014_);
v___x_4060_ = lean_uint64_shift_left(v___x_4058_, v___x_4057_);
v___x_4061_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0);
v_key_4062_ = lean_uint64_lor(v___x_4060_, v___x_4061_);
v___x_4063_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4063_, 0, v_config_4055_);
lean_ctor_set_uint64(v___x_4063_, sizeof(void*)*1, v_key_4062_);
lean_inc(v_canUnfold_x3f_4049_);
lean_inc(v_synthPendingDepth_4048_);
lean_inc(v_defEqCtx_x3f_4047_);
lean_inc_ref(v_localInstances_4046_);
lean_inc_ref(v_lctx_4045_);
lean_inc(v_zetaDeltaSet_4044_);
v___x_4064_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
lean_ctor_set(v___x_4064_, 1, v_zetaDeltaSet_4044_);
lean_ctor_set(v___x_4064_, 2, v_lctx_4045_);
lean_ctor_set(v___x_4064_, 3, v_localInstances_4046_);
lean_ctor_set(v___x_4064_, 4, v_defEqCtx_x3f_4047_);
lean_ctor_set(v___x_4064_, 5, v_synthPendingDepth_4048_);
lean_ctor_set(v___x_4064_, 6, v_canUnfold_x3f_4049_);
lean_ctor_set_uint8(v___x_4064_, sizeof(void*)*7, v_trackZetaDelta_4043_);
lean_ctor_set_uint8(v___x_4064_, sizeof(void*)*7 + 1, v_univApprox_4050_);
lean_ctor_set_uint8(v___x_4064_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4051_);
lean_ctor_set_uint8(v___x_4064_, sizeof(void*)*7 + 3, v_cacheInferType_4052_);
v___x_4065_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_4013_, v___x_4059_, v___x_4064_, v_a_4016_, v_a_4017_, v_a_4018_);
lean_dec_ref(v___x_4064_);
return v___x_4065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4068_, lean_object* v_e_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4068_, v_e_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_);
lean_dec(v_a_4073_);
lean_dec_ref(v_a_4072_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4076_, lean_object* v_d_4077_, lean_object* v_e_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4077_, v_e_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4085_, lean_object* v_d_4086_, lean_object* v_e_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4085_, v_d_4086_, v_e_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
return v_res_4093_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4097_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
lean_ctor_set(v___x_4098_, 1, v___x_4096_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_a_4099_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4100_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4102_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4104_, lean_object* v_k_4105_, lean_object* v_f_4106_){
_start:
{
lean_object* v_roots_4107_; lean_object* v_tries_4108_; lean_object* v___x_4109_; 
v_roots_4107_ = lean_ctor_get(v_d_4104_, 0);
v_tries_4108_ = lean_ctor_get(v_d_4104_, 1);
v___x_4109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4107_, v_k_4105_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4121_; 
lean_inc_ref(v_tries_4108_);
lean_inc_ref(v_roots_4107_);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_d_4104_);
if (v_isSharedCheck_4121_ == 0)
{
lean_object* v_unused_4122_; lean_object* v_unused_4123_; 
v_unused_4122_ = lean_ctor_get(v_d_4104_, 1);
lean_dec(v_unused_4122_);
v_unused_4123_ = lean_ctor_get(v_d_4104_, 0);
lean_dec(v_unused_4123_);
v___x_4111_ = v_d_4104_;
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
else
{
lean_dec(v_d_4104_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4113_; lean_object* v_roots_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4119_; 
v___x_4113_ = lean_array_get_size(v_tries_4108_);
v_roots_4114_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4107_, v_k_4105_, v___x_4113_);
v___x_4115_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_evalNode___redArg___closed__0));
v___x_4116_ = lean_apply_1(v_f_4106_, v___x_4115_);
v___x_4117_ = lean_array_push(v_tries_4108_, v___x_4116_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 1, v___x_4117_);
lean_ctor_set(v___x_4111_, 0, v_roots_4114_);
v___x_4119_ = v___x_4111_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_roots_4114_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
else
{
lean_object* v_val_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; 
lean_dec(v_k_4105_);
v_val_4124_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_val_4124_);
lean_dec_ref(v___x_4109_);
v___x_4125_ = lean_array_get_size(v_tries_4108_);
v___x_4126_ = lean_nat_dec_lt(v_val_4124_, v___x_4125_);
if (v___x_4126_ == 0)
{
lean_dec(v_val_4124_);
lean_dec_ref(v_f_4106_);
return v_d_4104_;
}
else
{
lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4138_; 
lean_inc_ref(v_tries_4108_);
lean_inc_ref(v_roots_4107_);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_d_4104_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; lean_object* v_unused_4140_; 
v_unused_4139_ = lean_ctor_get(v_d_4104_, 1);
lean_dec(v_unused_4139_);
v_unused_4140_ = lean_ctor_get(v_d_4104_, 0);
lean_dec(v_unused_4140_);
v___x_4128_ = v_d_4104_;
v_isShared_4129_ = v_isSharedCheck_4138_;
goto v_resetjp_4127_;
}
else
{
lean_dec(v_d_4104_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4138_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v_v_4130_; lean_object* v___x_4131_; lean_object* v_xs_x27_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v_v_4130_ = lean_array_fget(v_tries_4108_, v_val_4124_);
v___x_4131_ = lean_box(0);
v_xs_x27_4132_ = lean_array_fset(v_tries_4108_, v_val_4124_, v___x_4131_);
v___x_4133_ = lean_apply_1(v_f_4106_, v_v_4130_);
v___x_4134_ = lean_array_fset(v_xs_x27_4132_, v_val_4124_, v___x_4133_);
lean_dec(v_val_4124_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 1, v___x_4134_);
v___x_4136_ = v___x_4128_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_roots_4107_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4141_, lean_object* v_d_4142_, lean_object* v_k_4143_, lean_object* v_f_4144_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4142_, v_k_4143_, v_f_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4146_, lean_object* v_x_4147_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = lean_array_push(v_x_4147_, v_e_4146_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4149_, lean_object* v_k_4150_, lean_object* v_e_4151_){
_start:
{
lean_object* v___f_4152_; lean_object* v___x_4153_; 
v___f_4152_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4152_, 0, v_e_4151_);
v___x_4153_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4149_, v_k_4150_, v___f_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4154_, lean_object* v_d_4155_, lean_object* v_k_4156_, lean_object* v_e_4157_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4155_, v_k_4156_, v_e_4157_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4159_, size_t v_i_4160_, lean_object* v_bs_4161_){
_start:
{
uint8_t v___x_4162_; 
v___x_4162_ = lean_usize_dec_lt(v_i_4160_, v_sz_4159_);
if (v___x_4162_ == 0)
{
return v_bs_4161_;
}
else
{
lean_object* v_v_4163_; lean_object* v___x_4164_; lean_object* v_bs_x27_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; size_t v___x_4169_; size_t v___x_4170_; lean_object* v___x_4171_; 
v_v_4163_ = lean_array_uget(v_bs_4161_, v_i_4160_);
v___x_4164_ = lean_unsigned_to_nat(0u);
v_bs_x27_4165_ = lean_array_uset(v_bs_4161_, v_i_4160_, v___x_4164_);
v___x_4166_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4167_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set(v___x_4168_, 1, v___x_4164_);
lean_ctor_set(v___x_4168_, 2, v___x_4167_);
lean_ctor_set(v___x_4168_, 3, v_v_4163_);
v___x_4169_ = ((size_t)1ULL);
v___x_4170_ = lean_usize_add(v_i_4160_, v___x_4169_);
v___x_4171_ = lean_array_uset(v_bs_x27_4165_, v_i_4160_, v___x_4168_);
v_i_4160_ = v___x_4170_;
v_bs_4161_ = v___x_4171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4173_, lean_object* v_i_4174_, lean_object* v_bs_4175_){
_start:
{
size_t v_sz_boxed_4176_; size_t v_i_boxed_4177_; lean_object* v_res_4178_; 
v_sz_boxed_4176_ = lean_unbox_usize(v_sz_4173_);
lean_dec(v_sz_4173_);
v_i_boxed_4177_ = lean_unbox_usize(v_i_4174_);
lean_dec(v_i_4174_);
v_res_4178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4176_, v_i_boxed_4177_, v_bs_4175_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4179_, lean_object* v_x_4180_){
_start:
{
if (lean_obj_tag(v_x_4180_) == 0)
{
return v_x_4179_;
}
else
{
lean_object* v_key_4181_; lean_object* v_value_4182_; lean_object* v_tail_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v_key_4181_ = lean_ctor_get(v_x_4180_, 0);
lean_inc(v_key_4181_);
v_value_4182_ = lean_ctor_get(v_x_4180_, 1);
lean_inc(v_value_4182_);
v_tail_4183_ = lean_ctor_get(v_x_4180_, 2);
lean_inc(v_tail_4183_);
lean_dec_ref(v_x_4180_);
v___x_4184_ = lean_unsigned_to_nat(1u);
v___x_4185_ = lean_nat_add(v_value_4182_, v___x_4184_);
lean_dec(v_value_4182_);
v___x_4186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4179_, v_key_4181_, v___x_4185_);
v_x_4179_ = v___x_4186_;
v_x_4180_ = v_tail_4183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4188_, size_t v_i_4189_, size_t v_stop_4190_, lean_object* v_b_4191_){
_start:
{
uint8_t v___x_4192_; 
v___x_4192_ = lean_usize_dec_eq(v_i_4189_, v_stop_4190_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; lean_object* v___x_4194_; size_t v___x_4195_; size_t v___x_4196_; 
v___x_4193_ = lean_array_uget_borrowed(v_as_4188_, v_i_4189_);
lean_inc(v___x_4193_);
v___x_4194_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4191_, v___x_4193_);
v___x_4195_ = ((size_t)1ULL);
v___x_4196_ = lean_usize_add(v_i_4189_, v___x_4195_);
v_i_4189_ = v___x_4196_;
v_b_4191_ = v___x_4194_;
goto _start;
}
else
{
return v_b_4191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4198_, lean_object* v_i_4199_, lean_object* v_stop_4200_, lean_object* v_b_4201_){
_start:
{
size_t v_i_boxed_4202_; size_t v_stop_boxed_4203_; lean_object* v_res_4204_; 
v_i_boxed_4202_ = lean_unbox_usize(v_i_4199_);
lean_dec(v_i_4199_);
v_stop_boxed_4203_ = lean_unbox_usize(v_stop_4200_);
lean_dec(v_stop_4200_);
v_res_4204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4198_, v_i_boxed_4202_, v_stop_boxed_4203_, v_b_4201_);
lean_dec_ref(v_as_4198_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4205_){
_start:
{
lean_object* v_roots_4206_; lean_object* v_tries_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4234_; 
v_roots_4206_ = lean_ctor_get(v_d_4205_, 0);
v_tries_4207_ = lean_ctor_get(v_d_4205_, 1);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_d_4205_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4209_ = v_d_4205_;
v_isShared_4210_ = v_isSharedCheck_4234_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_tries_4207_);
lean_inc(v_roots_4206_);
lean_dec(v_d_4205_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4234_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___y_4212_; lean_object* v_buckets_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; 
v_buckets_4223_ = lean_ctor_get(v_roots_4206_, 1);
v___x_4224_ = lean_unsigned_to_nat(0u);
v___x_4225_ = lean_array_get_size(v_buckets_4223_);
v___x_4226_ = lean_nat_dec_lt(v___x_4224_, v___x_4225_);
if (v___x_4226_ == 0)
{
v___y_4212_ = v_roots_4206_;
goto v___jp_4211_;
}
else
{
uint8_t v___x_4227_; 
v___x_4227_ = lean_nat_dec_le(v___x_4225_, v___x_4225_);
if (v___x_4227_ == 0)
{
if (v___x_4226_ == 0)
{
v___y_4212_ = v_roots_4206_;
goto v___jp_4211_;
}
else
{
size_t v___x_4228_; size_t v___x_4229_; lean_object* v___x_4230_; 
lean_inc_ref(v_buckets_4223_);
v___x_4228_ = ((size_t)0ULL);
v___x_4229_ = lean_usize_of_nat(v___x_4225_);
v___x_4230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4223_, v___x_4228_, v___x_4229_, v_roots_4206_);
lean_dec_ref(v_buckets_4223_);
v___y_4212_ = v___x_4230_;
goto v___jp_4211_;
}
}
else
{
size_t v___x_4231_; size_t v___x_4232_; lean_object* v___x_4233_; 
lean_inc_ref(v_buckets_4223_);
v___x_4231_ = ((size_t)0ULL);
v___x_4232_ = lean_usize_of_nat(v___x_4225_);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4223_, v___x_4231_, v___x_4232_, v_roots_4206_);
lean_dec_ref(v_buckets_4223_);
v___y_4212_ = v___x_4233_;
goto v___jp_4211_;
}
}
v___jp_4211_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; size_t v_sz_4216_; size_t v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4221_; 
v___x_4213_ = lean_unsigned_to_nat(1u);
v___x_4214_ = lean_mk_empty_array_with_capacity(v___x_4213_);
lean_dec_ref(v___x_4214_);
v___x_4215_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4216_ = lean_array_size(v_tries_4207_);
v___x_4217_ = ((size_t)0ULL);
v___x_4218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4216_, v___x_4217_, v_tries_4207_);
v___x_4219_ = l_Array_append___redArg(v___x_4215_, v___x_4218_);
lean_dec_ref(v___x_4218_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 1, v___y_4212_);
lean_ctor_set(v___x_4209_, 0, v___x_4219_);
v___x_4221_ = v___x_4209_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
lean_ctor_set(v_reuseFailAlloc_4222_, 1, v___y_4212_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4235_, lean_object* v_d_4236_){
_start:
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4238_, size_t v_sz_4239_, size_t v_i_4240_, lean_object* v_bs_4241_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4239_, v_i_4240_, v_bs_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4243_, lean_object* v_sz_4244_, lean_object* v_i_4245_, lean_object* v_bs_4246_){
_start:
{
size_t v_sz_boxed_4247_; size_t v_i_boxed_4248_; lean_object* v_res_4249_; 
v_sz_boxed_4247_ = lean_unbox_usize(v_sz_4244_);
lean_dec(v_sz_4244_);
v_i_boxed_4248_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_res_4249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4243_, v_sz_boxed_4247_, v_i_boxed_4248_, v_bs_4246_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4250_, lean_object* v_x_4251_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Array_append___redArg(v_x_4251_, v_y_4250_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4253_, lean_object* v_x_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4253_, v_x_4254_);
lean_dec_ref(v_y_4253_);
return v_res_4255_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Array_instInhabited(lean_box(0));
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4257_, lean_object* v_snd_4258_, lean_object* v_x_4259_, lean_object* v_x_4260_){
_start:
{
if (lean_obj_tag(v_x_4260_) == 0)
{
lean_dec_ref(v_snd_4258_);
return v_x_4259_;
}
else
{
lean_object* v_key_4261_; lean_object* v_value_4262_; lean_object* v_tail_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v_key_4261_ = lean_ctor_get(v_x_4260_, 0);
lean_inc(v_key_4261_);
v_value_4262_ = lean_ctor_get(v_x_4260_, 1);
lean_inc(v_value_4262_);
v_tail_4263_ = lean_ctor_get(v_x_4260_, 2);
lean_inc(v_tail_4263_);
lean_dec_ref(v_x_4260_);
v___x_4264_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4265_ = lean_array_get_borrowed(v___x_4264_, v_tries_4257_, v_value_4262_);
lean_dec(v_value_4262_);
lean_inc_ref(v_snd_4258_);
lean_inc(v___x_4265_);
v___x_4266_ = lean_apply_1(v_snd_4258_, v___x_4265_);
v___x_4267_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4259_, v_key_4261_, v___x_4266_);
v_x_4259_ = v___x_4267_;
v_x_4260_ = v_tail_4263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4269_, lean_object* v_snd_4270_, lean_object* v_x_4271_, lean_object* v_x_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4269_, v_snd_4270_, v_x_4271_, v_x_4272_);
lean_dec_ref(v_tries_4269_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4274_, lean_object* v_snd_4275_, lean_object* v_as_4276_, size_t v_i_4277_, size_t v_stop_4278_, lean_object* v_b_4279_){
_start:
{
uint8_t v___x_4280_; 
v___x_4280_ = lean_usize_dec_eq(v_i_4277_, v_stop_4278_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4282_; size_t v___x_4283_; size_t v___x_4284_; 
v___x_4281_ = lean_array_uget_borrowed(v_as_4276_, v_i_4277_);
lean_inc(v___x_4281_);
lean_inc_ref(v_snd_4275_);
v___x_4282_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4274_, v_snd_4275_, v_b_4279_, v___x_4281_);
v___x_4283_ = ((size_t)1ULL);
v___x_4284_ = lean_usize_add(v_i_4277_, v___x_4283_);
v_i_4277_ = v___x_4284_;
v_b_4279_ = v___x_4282_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4275_);
return v_b_4279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4286_, lean_object* v_snd_4287_, lean_object* v_as_4288_, lean_object* v_i_4289_, lean_object* v_stop_4290_, lean_object* v_b_4291_){
_start:
{
size_t v_i_boxed_4292_; size_t v_stop_boxed_4293_; lean_object* v_res_4294_; 
v_i_boxed_4292_ = lean_unbox_usize(v_i_4289_);
lean_dec(v_i_4289_);
v_stop_boxed_4293_ = lean_unbox_usize(v_stop_4290_);
lean_dec(v_stop_4290_);
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4286_, v_snd_4287_, v_as_4288_, v_i_boxed_4292_, v_stop_boxed_4293_, v_b_4291_);
lean_dec_ref(v_as_4288_);
lean_dec_ref(v_tries_4286_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4297_, lean_object* v_y_4298_){
_start:
{
lean_object* v_fst_4300_; lean_object* v_buckets_4301_; lean_object* v_tries_4302_; lean_object* v_snd_4303_; lean_object* v_roots_4314_; lean_object* v_roots_4315_; lean_object* v_tries_4316_; lean_object* v_size_4317_; lean_object* v_buckets_4318_; lean_object* v_tries_4319_; lean_object* v_size_4320_; lean_object* v_buckets_4321_; uint8_t v___x_4322_; 
v_roots_4314_ = lean_ctor_get(v_y_4298_, 0);
v_roots_4315_ = lean_ctor_get(v_x_4297_, 0);
v_tries_4316_ = lean_ctor_get(v_y_4298_, 1);
v_size_4317_ = lean_ctor_get(v_roots_4314_, 0);
v_buckets_4318_ = lean_ctor_get(v_roots_4314_, 1);
v_tries_4319_ = lean_ctor_get(v_x_4297_, 1);
v_size_4320_ = lean_ctor_get(v_roots_4315_, 0);
v_buckets_4321_ = lean_ctor_get(v_roots_4315_, 1);
v___x_4322_ = lean_nat_dec_le(v_size_4317_, v_size_4320_);
if (v___x_4322_ == 0)
{
lean_object* v___f_4323_; 
lean_inc_ref(v_buckets_4321_);
lean_inc_ref(v_tries_4319_);
lean_dec_ref(v_x_4297_);
v___f_4323_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4300_ = v_y_4298_;
v_buckets_4301_ = v_buckets_4321_;
v_tries_4302_ = v_tries_4319_;
v_snd_4303_ = v___f_4323_;
goto v___jp_4299_;
}
else
{
lean_object* v___f_4324_; 
lean_inc_ref(v_buckets_4318_);
lean_inc_ref(v_tries_4316_);
lean_dec_ref(v_y_4298_);
v___f_4324_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4300_ = v_x_4297_;
v_buckets_4301_ = v_buckets_4318_;
v_tries_4302_ = v_tries_4316_;
v_snd_4303_ = v___f_4324_;
goto v___jp_4299_;
}
v___jp_4299_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4304_ = lean_unsigned_to_nat(0u);
v___x_4305_ = lean_array_get_size(v_buckets_4301_);
v___x_4306_ = lean_nat_dec_lt(v___x_4304_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_dec_ref(v_tries_4302_);
lean_dec_ref(v_buckets_4301_);
return v_fst_4300_;
}
else
{
uint8_t v___x_4307_; 
v___x_4307_ = lean_nat_dec_le(v___x_4305_, v___x_4305_);
if (v___x_4307_ == 0)
{
if (v___x_4306_ == 0)
{
lean_dec_ref(v_tries_4302_);
lean_dec_ref(v_buckets_4301_);
return v_fst_4300_;
}
else
{
size_t v___x_4308_; size_t v___x_4309_; lean_object* v___x_4310_; 
v___x_4308_ = ((size_t)0ULL);
v___x_4309_ = lean_usize_of_nat(v___x_4305_);
lean_inc_ref(v_snd_4303_);
v___x_4310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4302_, v_snd_4303_, v_buckets_4301_, v___x_4308_, v___x_4309_, v_fst_4300_);
lean_dec_ref(v_buckets_4301_);
lean_dec_ref(v_tries_4302_);
return v___x_4310_;
}
}
else
{
size_t v___x_4311_; size_t v___x_4312_; lean_object* v___x_4313_; 
v___x_4311_ = ((size_t)0ULL);
v___x_4312_ = lean_usize_of_nat(v___x_4305_);
lean_inc_ref(v_snd_4303_);
v___x_4313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4302_, v_snd_4303_, v_buckets_4301_, v___x_4311_, v___x_4312_, v_fst_4300_);
lean_dec_ref(v_buckets_4301_);
lean_dec_ref(v_tries_4302_);
return v___x_4313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4325_, lean_object* v_x_4326_, lean_object* v_y_4327_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4326_, v_y_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4329_, lean_object* v_tries_4330_, lean_object* v_snd_4331_, lean_object* v_x_4332_, lean_object* v_x_4333_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4330_, v_snd_4331_, v_x_4332_, v_x_4333_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4335_, lean_object* v_tries_4336_, lean_object* v_snd_4337_, lean_object* v_x_4338_, lean_object* v_x_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4335_, v_tries_4336_, v_snd_4337_, v_x_4338_, v_x_4339_);
lean_dec_ref(v_tries_4336_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4341_, lean_object* v_tries_4342_, lean_object* v_snd_4343_, lean_object* v_as_4344_, size_t v_i_4345_, size_t v_stop_4346_, lean_object* v_b_4347_){
_start:
{
lean_object* v___x_4348_; 
v___x_4348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4342_, v_snd_4343_, v_as_4344_, v_i_4345_, v_stop_4346_, v_b_4347_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4349_, lean_object* v_tries_4350_, lean_object* v_snd_4351_, lean_object* v_as_4352_, lean_object* v_i_4353_, lean_object* v_stop_4354_, lean_object* v_b_4355_){
_start:
{
size_t v_i_boxed_4356_; size_t v_stop_boxed_4357_; lean_object* v_res_4358_; 
v_i_boxed_4356_ = lean_unbox_usize(v_i_4353_);
lean_dec(v_i_4353_);
v_stop_boxed_4357_ = lean_unbox_usize(v_stop_4354_);
lean_dec(v_stop_4354_);
v_res_4358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4349_, v_tries_4350_, v_snd_4351_, v_as_4352_, v_i_boxed_4356_, v_stop_boxed_4357_, v_b_4355_);
lean_dec_ref(v_as_4352_);
lean_dec_ref(v_tries_4350_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4360_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0));
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4362_, lean_object* v_value_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4362_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4391_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4372_ = v___x_4369_;
v_isShared_4373_ = v_isSharedCheck_4391_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4369_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4391_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v_fst_4374_; lean_object* v_snd_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4390_; 
v_fst_4374_ = lean_ctor_get(v_a_4370_, 0);
v_snd_4375_ = lean_ctor_get(v_a_4370_, 1);
v_isSharedCheck_4390_ = !lean_is_exclusive(v_a_4370_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4377_ = v_a_4370_;
v_isShared_4378_ = v_isSharedCheck_4390_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_snd_4375_);
lean_inc(v_fst_4374_);
lean_dec(v_a_4370_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4390_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v_lctx_4379_; lean_object* v_localInstances_4380_; lean_object* v___x_4382_; 
v_lctx_4379_ = lean_ctor_get(v_a_4364_, 2);
v_localInstances_4380_ = lean_ctor_get(v_a_4364_, 3);
lean_inc_ref(v_localInstances_4380_);
lean_inc_ref(v_lctx_4379_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 1, v_localInstances_4380_);
lean_ctor_set(v___x_4377_, 0, v_lctx_4379_);
v___x_4382_ = v___x_4377_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_lctx_4379_);
lean_ctor_set(v_reuseFailAlloc_4389_, 1, v_localInstances_4380_);
v___x_4382_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4387_; 
v___x_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
lean_ctor_set(v___x_4383_, 1, v_value_4363_);
v___x_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4384_, 0, v_snd_4375_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
v___x_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4385_, 0, v_fst_4374_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 0, v___x_4385_);
v___x_4387_ = v___x_4372_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
lean_dec(v_value_4363_);
v_a_4392_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4369_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4369_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4400_, lean_object* v_value_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4400_, v_value_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_);
lean_dec(v_a_4405_);
lean_dec_ref(v_a_4404_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4408_, lean_object* v_expr_4409_, lean_object* v_value_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4409_, v_value_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4417_, lean_object* v_expr_4418_, lean_object* v_value_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4417_, v_expr_4418_, v_value_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
lean_dec(v_a_4421_);
lean_dec_ref(v_a_4420_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4426_, lean_object* v_idx_4427_, lean_object* v_value_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_){
_start:
{
lean_object* v_entry_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4480_; 
v_entry_4434_ = lean_ctor_get(v_e_4426_, 1);
v_isSharedCheck_4480_ = !lean_is_exclusive(v_e_4426_);
if (v_isSharedCheck_4480_ == 0)
{
lean_object* v_unused_4481_; 
v_unused_4481_ = lean_ctor_get(v_e_4426_, 0);
lean_dec(v_unused_4481_);
v___x_4436_ = v_e_4426_;
v_isShared_4437_ = v_isSharedCheck_4480_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_entry_4434_);
lean_dec(v_e_4426_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4480_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v_snd_4438_; lean_object* v_fst_4439_; lean_object* v_fst_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4478_; 
v_snd_4438_ = lean_ctor_get(v_entry_4434_, 1);
lean_inc(v_snd_4438_);
v_fst_4439_ = lean_ctor_get(v_entry_4434_, 0);
lean_inc(v_fst_4439_);
lean_dec_ref(v_entry_4434_);
v_fst_4440_ = lean_ctor_get(v_snd_4438_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_snd_4438_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; 
v_unused_4479_ = lean_ctor_get(v_snd_4438_, 1);
lean_dec(v_unused_4479_);
v___x_4442_ = v_snd_4438_;
v_isShared_4443_ = v_isSharedCheck_4478_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_fst_4440_);
lean_dec(v_snd_4438_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4478_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4444_ = l_Lean_instInhabitedExpr;
v___x_4445_ = lean_array_get(v___x_4444_, v_fst_4439_, v_idx_4427_);
lean_dec(v_fst_4439_);
v___x_4446_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4445_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4469_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4469_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4469_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v_fst_4451_; lean_object* v_snd_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4468_; 
v_fst_4451_ = lean_ctor_get(v_a_4447_, 0);
v_snd_4452_ = lean_ctor_get(v_a_4447_, 1);
v_isSharedCheck_4468_ = !lean_is_exclusive(v_a_4447_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4454_ = v_a_4447_;
v_isShared_4455_ = v_isSharedCheck_4468_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_snd_4452_);
lean_inc(v_fst_4451_);
lean_dec(v_a_4447_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4468_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 1, v_value_4428_);
lean_ctor_set(v___x_4454_, 0, v_fst_4440_);
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_fst_4440_);
lean_ctor_set(v_reuseFailAlloc_4467_, 1, v_value_4428_);
v___x_4457_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4459_; 
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 1, v___x_4457_);
lean_ctor_set(v___x_4442_, 0, v_snd_4452_);
v___x_4459_ = v___x_4442_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_snd_4452_);
lean_ctor_set(v_reuseFailAlloc_4466_, 1, v___x_4457_);
v___x_4459_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4461_; 
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 1, v___x_4459_);
lean_ctor_set(v___x_4436_, 0, v_fst_4451_);
v___x_4461_ = v___x_4436_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_fst_4451_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v___x_4459_);
v___x_4461_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
lean_object* v___x_4463_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4461_);
v___x_4463_ = v___x_4449_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4461_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_del_object(v___x_4442_);
lean_dec(v_fst_4440_);
lean_del_object(v___x_4436_);
lean_dec(v_value_4428_);
v_a_4470_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4446_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4446_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4482_, lean_object* v_idx_4483_, lean_object* v_value_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4482_, v_idx_4483_, v_value_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_);
lean_dec(v_a_4488_);
lean_dec_ref(v_a_4487_);
lean_dec(v_a_4486_);
lean_dec_ref(v_a_4485_);
lean_dec(v_idx_4483_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4491_, lean_object* v_e_4492_, lean_object* v_idx_4493_, lean_object* v_value_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4492_, v_idx_4493_, v_value_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4501_, lean_object* v_e_4502_, lean_object* v_idx_4503_, lean_object* v_value_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4501_, v_e_4502_, v_idx_4503_, v_value_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_idx_4503_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4514_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4515_ = lean_st_mk_ref(v___x_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4517_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4518_; 
v___x_4518_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4518_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4519_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
return v___x_4520_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
lean_ctor_set(v___x_4522_, 1, v___x_4521_);
return v___x_4522_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4524_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
lean_ctor_set(v___x_4524_, 1, v___x_4523_);
lean_ctor_set(v___x_4524_, 2, v___x_4523_);
lean_ctor_set(v___x_4524_, 3, v___x_4523_);
lean_ctor_set(v___x_4524_, 4, v___x_4523_);
lean_ctor_set(v___x_4524_, 5, v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4525_){
_start:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4526_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4527_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4528_, 0, v_ngen_4525_);
lean_ctor_set(v___x_4528_, 1, v___x_4526_);
lean_ctor_set(v___x_4528_, 2, v___x_4527_);
return v___x_4528_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4529_, lean_object* v_declName_4530_){
_start:
{
uint8_t v___x_4531_; 
v___x_4531_ = l_Lean_isPrivateName(v_declName_4530_);
if (v___x_4531_ == 0)
{
return v___x_4531_;
}
else
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4529_, v_declName_4530_);
if (lean_obj_tag(v___x_4532_) == 0)
{
return v___x_4531_;
}
else
{
lean_object* v_val_4533_; lean_object* v___x_4534_; uint8_t v_isModule_4535_; 
v_val_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_val_4533_);
lean_dec_ref(v___x_4532_);
v___x_4534_ = l_Lean_Environment_header(v_env_4529_);
v_isModule_4535_ = lean_ctor_get_uint8(v___x_4534_, sizeof(void*)*7 + 4);
if (v_isModule_4535_ == 0)
{
lean_dec_ref(v___x_4534_);
lean_dec(v_val_4533_);
return v_isModule_4535_;
}
else
{
lean_object* v_modules_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; 
v_modules_4536_ = lean_ctor_get(v___x_4534_, 3);
lean_inc_ref(v_modules_4536_);
lean_dec_ref(v___x_4534_);
v___x_4537_ = lean_array_get_size(v_modules_4536_);
v___x_4538_ = lean_nat_dec_lt(v_val_4533_, v___x_4537_);
if (v___x_4538_ == 0)
{
lean_dec_ref(v_modules_4536_);
lean_dec(v_val_4533_);
return v___x_4538_;
}
else
{
lean_object* v___x_4539_; lean_object* v_toImport_4540_; uint8_t v_importAll_4541_; 
v___x_4539_ = lean_array_fget(v_modules_4536_, v_val_4533_);
lean_dec(v_val_4533_);
lean_dec_ref(v_modules_4536_);
v_toImport_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc_ref(v_toImport_4540_);
lean_dec(v___x_4539_);
v_importAll_4541_ = lean_ctor_get_uint8(v_toImport_4540_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4540_);
return v_importAll_4541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4542_, lean_object* v_declName_4543_){
_start:
{
uint8_t v_res_4544_; lean_object* v_r_4545_; 
v_res_4544_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4542_, v_declName_4543_);
lean_dec(v_declName_4543_);
lean_dec_ref(v_env_4542_);
v_r_4545_ = lean_box(v_res_4544_);
return v_r_4545_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4551_, lean_object* v_declName_4552_){
_start:
{
uint8_t v___x_4553_; 
lean_inc(v_declName_4552_);
lean_inc_ref(v_env_4551_);
v___x_4553_ = l_Lean_Meta_allowCompletion(v_env_4551_, v_declName_4552_);
if (v___x_4553_ == 0)
{
uint8_t v___x_4554_; 
lean_dec(v_declName_4552_);
lean_dec_ref(v_env_4551_);
v___x_4554_ = 1;
return v___x_4554_;
}
else
{
lean_object* v___x_4555_; uint8_t v___x_4556_; uint8_t v___y_4566_; 
v___x_4555_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4556_ = lean_name_eq(v_declName_4552_, v___x_4555_);
if (v___x_4556_ == 0)
{
uint8_t v___x_4567_; 
lean_inc(v_declName_4552_);
v___x_4567_ = l_Lean_Name_isInternalDetail(v_declName_4552_);
if (v___x_4567_ == 0)
{
lean_dec_ref(v_env_4551_);
v___y_4566_ = v___x_4567_;
goto v___jp_4565_;
}
else
{
uint8_t v___x_4568_; 
v___x_4568_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4551_, v_declName_4552_);
lean_dec_ref(v_env_4551_);
if (v___x_4568_ == 0)
{
v___y_4566_ = v___x_4567_;
goto v___jp_4565_;
}
else
{
goto v___jp_4561_;
}
}
}
else
{
lean_dec(v_declName_4552_);
lean_dec_ref(v_env_4551_);
return v___x_4556_;
}
v___jp_4557_:
{
if (lean_obj_tag(v_declName_4552_) == 1)
{
lean_object* v_str_4558_; lean_object* v___x_4559_; uint8_t v___x_4560_; 
v_str_4558_ = lean_ctor_get(v_declName_4552_, 1);
lean_inc_ref(v_str_4558_);
lean_dec_ref(v_declName_4552_);
v___x_4559_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4560_ = lean_string_dec_eq(v_str_4558_, v___x_4559_);
lean_dec_ref(v_str_4558_);
if (v___x_4560_ == 0)
{
return v___x_4556_;
}
else
{
return v___x_4553_;
}
}
else
{
lean_dec(v_declName_4552_);
return v___x_4556_;
}
}
v___jp_4561_:
{
if (lean_obj_tag(v_declName_4552_) == 1)
{
lean_object* v_str_4562_; lean_object* v___x_4563_; uint8_t v___x_4564_; 
v_str_4562_ = lean_ctor_get(v_declName_4552_, 1);
v___x_4563_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4564_ = lean_string_dec_eq(v_str_4562_, v___x_4563_);
if (v___x_4564_ == 0)
{
goto v___jp_4557_;
}
else
{
lean_dec_ref(v_declName_4552_);
return v___x_4553_;
}
}
else
{
goto v___jp_4557_;
}
}
v___jp_4565_:
{
if (v___y_4566_ == 0)
{
goto v___jp_4561_;
}
else
{
lean_dec(v_declName_4552_);
return v___y_4566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4569_, lean_object* v_declName_4570_){
_start:
{
uint8_t v_res_4571_; lean_object* v_r_4572_; 
v_res_4571_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4569_, v_declName_4570_);
v_r_4572_ = lean_box(v_res_4571_);
return v_r_4572_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4573_, lean_object* v_opt_4574_){
_start:
{
lean_object* v_name_4575_; lean_object* v_defValue_4576_; lean_object* v_map_4577_; lean_object* v___x_4578_; 
v_name_4575_ = lean_ctor_get(v_opt_4574_, 0);
v_defValue_4576_ = lean_ctor_get(v_opt_4574_, 1);
v_map_4577_ = lean_ctor_get(v_opts_4573_, 0);
v___x_4578_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4577_, v_name_4575_);
if (lean_obj_tag(v___x_4578_) == 0)
{
uint8_t v___x_4579_; 
v___x_4579_ = lean_unbox(v_defValue_4576_);
return v___x_4579_;
}
else
{
lean_object* v_val_4580_; 
v_val_4580_ = lean_ctor_get(v___x_4578_, 0);
lean_inc(v_val_4580_);
lean_dec_ref(v___x_4578_);
if (lean_obj_tag(v_val_4580_) == 1)
{
uint8_t v_v_4581_; 
v_v_4581_ = lean_ctor_get_uint8(v_val_4580_, 0);
lean_dec_ref(v_val_4580_);
return v_v_4581_;
}
else
{
uint8_t v___x_4582_; 
lean_dec(v_val_4580_);
v___x_4582_ = lean_unbox(v_defValue_4576_);
return v___x_4582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4583_, lean_object* v_opt_4584_){
_start:
{
uint8_t v_res_4585_; lean_object* v_r_4586_; 
v_res_4585_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4583_, v_opt_4584_);
lean_dec_ref(v_opt_4584_);
lean_dec_ref(v_opts_4583_);
v_r_4586_ = lean_box(v_res_4585_);
return v_r_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4587_, lean_object* v_opt_4588_){
_start:
{
lean_object* v_name_4589_; lean_object* v_defValue_4590_; lean_object* v_map_4591_; lean_object* v___x_4592_; 
v_name_4589_ = lean_ctor_get(v_opt_4588_, 0);
v_defValue_4590_ = lean_ctor_get(v_opt_4588_, 1);
v_map_4591_ = lean_ctor_get(v_opts_4587_, 0);
v___x_4592_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4591_, v_name_4589_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_inc(v_defValue_4590_);
return v_defValue_4590_;
}
else
{
lean_object* v_val_4593_; 
v_val_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_val_4593_);
lean_dec_ref(v___x_4592_);
if (lean_obj_tag(v_val_4593_) == 3)
{
lean_object* v_v_4594_; 
v_v_4594_ = lean_ctor_get(v_val_4593_, 0);
lean_inc(v_v_4594_);
lean_dec_ref(v_val_4593_);
return v_v_4594_;
}
else
{
lean_dec(v_val_4593_);
lean_inc(v_defValue_4590_);
return v_defValue_4590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4595_, lean_object* v_opt_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4595_, v_opt_4596_);
lean_dec_ref(v_opt_4596_);
lean_dec_ref(v_opts_4595_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4598_, size_t v_i_4599_, size_t v_stop_4600_, lean_object* v_b_4601_){
_start:
{
uint8_t v___x_4602_; 
v___x_4602_ = lean_usize_dec_eq(v_i_4599_, v_stop_4600_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; lean_object* v_key_4604_; lean_object* v_entry_4605_; lean_object* v___x_4606_; size_t v___x_4607_; size_t v___x_4608_; 
v___x_4603_ = lean_array_uget_borrowed(v_as_4598_, v_i_4599_);
v_key_4604_ = lean_ctor_get(v___x_4603_, 0);
v_entry_4605_ = lean_ctor_get(v___x_4603_, 1);
lean_inc_ref(v_entry_4605_);
lean_inc(v_key_4604_);
v___x_4606_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4601_, v_key_4604_, v_entry_4605_);
v___x_4607_ = ((size_t)1ULL);
v___x_4608_ = lean_usize_add(v_i_4599_, v___x_4607_);
v_i_4599_ = v___x_4608_;
v_b_4601_ = v___x_4606_;
goto _start;
}
else
{
return v_b_4601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4610_, lean_object* v_i_4611_, lean_object* v_stop_4612_, lean_object* v_b_4613_){
_start:
{
size_t v_i_boxed_4614_; size_t v_stop_boxed_4615_; lean_object* v_res_4616_; 
v_i_boxed_4614_ = lean_unbox_usize(v_i_4611_);
lean_dec(v_i_4611_);
v_stop_boxed_4615_ = lean_unbox_usize(v_stop_4612_);
lean_dec(v_stop_4612_);
v_res_4616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4610_, v_i_boxed_4614_, v_stop_boxed_4615_, v_b_4613_);
lean_dec_ref(v_as_4610_);
return v_res_4616_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4617_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
return v___x_4619_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4620_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4621_ = lean_unsigned_to_nat(0u);
v___x_4622_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
lean_ctor_set(v___x_4622_, 1, v___x_4621_);
lean_ctor_set(v___x_4622_, 2, v___x_4621_);
lean_ctor_set(v___x_4622_, 3, v___x_4621_);
lean_ctor_set(v___x_4622_, 4, v___x_4620_);
lean_ctor_set(v___x_4622_, 5, v___x_4620_);
lean_ctor_set(v___x_4622_, 6, v___x_4620_);
lean_ctor_set(v___x_4622_, 7, v___x_4620_);
lean_ctor_set(v___x_4622_, 8, v___x_4620_);
lean_ctor_set(v___x_4622_, 9, v___x_4620_);
return v___x_4622_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4623_ = lean_unsigned_to_nat(32u);
v___x_4624_ = lean_mk_empty_array_with_capacity(v___x_4623_);
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4624_);
return v___x_4625_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4626_ = ((size_t)5ULL);
v___x_4627_ = lean_unsigned_to_nat(0u);
v___x_4628_ = lean_unsigned_to_nat(32u);
v___x_4629_ = lean_mk_empty_array_with_capacity(v___x_4628_);
v___x_4630_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4631_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
lean_ctor_set(v___x_4631_, 1, v___x_4629_);
lean_ctor_set(v___x_4631_, 2, v___x_4627_);
lean_ctor_set(v___x_4631_, 3, v___x_4627_);
lean_ctor_set_usize(v___x_4631_, 4, v___x_4626_);
return v___x_4631_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4632_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
lean_ctor_set(v___x_4633_, 2, v___x_4632_);
lean_ctor_set(v___x_4633_, 3, v___x_4632_);
lean_ctor_set(v___x_4633_, 4, v___x_4632_);
return v___x_4633_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4634_ = lean_box(1);
v___x_4635_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4636_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
lean_ctor_set(v___x_4637_, 1, v___x_4635_);
lean_ctor_set(v___x_4637_, 2, v___x_4634_);
return v___x_4637_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4640_ = lean_unsigned_to_nat(1u);
v___x_4641_ = l_Lean_firstFrontendMacroScope;
v___x_4642_ = lean_nat_add(v___x_4641_, v___x_4640_);
return v___x_4642_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4647_; uint64_t v___x_4648_; lean_object* v___x_4649_; 
v___x_4647_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4648_ = 0ULL;
v___x_4649_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4649_, 0, v___x_4647_);
lean_ctor_set_uint64(v___x_4649_, sizeof(void*)*1, v___x_4648_);
return v___x_4649_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4650_ = l_Lean_NameSet_empty;
v___x_4651_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4651_);
lean_ctor_set(v___x_4652_, 1, v___x_4651_);
lean_ctor_set(v___x_4652_, 2, v___x_4650_);
return v___x_4652_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; uint8_t v___x_4655_; lean_object* v___x_4656_; 
v___x_4653_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4654_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4655_ = 1;
v___x_4656_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4656_, 0, v___x_4654_);
lean_ctor_set(v___x_4656_, 1, v___x_4654_);
lean_ctor_set(v___x_4656_, 2, v___x_4653_);
lean_ctor_set_uint8(v___x_4656_, sizeof(void*)*3, v___x_4655_);
return v___x_4656_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
lean_ctor_set(v___x_4658_, 1, v___x_4657_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4659_, lean_object* v_env_4660_, lean_object* v_modName_4661_, lean_object* v_d_4662_, lean_object* v_cacheRef_4663_, lean_object* v_tree_4664_, lean_object* v_act_4665_, lean_object* v_name_4666_, lean_object* v_constInfo_4667_){
_start:
{
uint8_t v___x_4669_; 
v___x_4669_ = l_Lean_ConstantInfo_isUnsafe(v_constInfo_4667_);
if (v___x_4669_ == 0)
{
uint8_t v___x_4670_; 
lean_inc(v_name_4666_);
lean_inc_ref(v_env_4660_);
v___x_4670_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4660_, v_name_4666_);
if (v___x_4670_ == 0)
{
lean_object* v___x_4671_; lean_object* v_ngen_4672_; lean_object* v_core_4673_; lean_object* v_meta_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4808_; 
v___x_4671_ = lean_st_ref_get(v_cacheRef_4663_);
v_ngen_4672_ = lean_ctor_get(v___x_4671_, 0);
v_core_4673_ = lean_ctor_get(v___x_4671_, 1);
v_meta_4674_ = lean_ctor_get(v___x_4671_, 2);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4676_ = v___x_4671_;
v_isShared_4677_ = v_isSharedCheck_4808_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_meta_4674_);
lean_inc(v_core_4673_);
lean_inc(v_ngen_4672_);
lean_dec(v___x_4671_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4808_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; uint8_t v___x_4688_; uint8_t v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v_fileName_4706_; lean_object* v_fileMap_4707_; lean_object* v_options_4708_; lean_object* v_currRecDepth_4709_; lean_object* v_maxRecDepth_4710_; lean_object* v_ref_4711_; lean_object* v_currNamespace_4712_; lean_object* v_openDecls_4713_; lean_object* v_initHeartbeats_4714_; lean_object* v_maxHeartbeats_4715_; lean_object* v_quotContext_4716_; lean_object* v_currMacroScope_4717_; uint8_t v_diag_4718_; lean_object* v_cancelTk_x3f_4719_; uint8_t v_suppressElabErrors_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4806_; 
v___x_4678_ = lean_unsigned_to_nat(0u);
v___x_4679_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4680_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4681_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4672_);
v___x_4682_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4672_);
v___x_4683_ = lean_st_ref_set(v_cacheRef_4663_, v___x_4682_);
v___x_4684_ = lean_box(1);
v___x_4685_ = 1;
v___x_4686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4679_);
lean_ctor_set(v___x_4686_, 1, v_meta_4674_);
lean_ctor_set(v___x_4686_, 2, v___x_4684_);
lean_ctor_set(v___x_4686_, 3, v___x_4680_);
lean_ctor_set(v___x_4686_, 4, v___x_4681_);
v___x_4687_ = 2;
v___x_4688_ = 0;
v___x_4689_ = 2;
v___x_4690_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4690_, 0, v___x_4670_);
lean_ctor_set_uint8(v___x_4690_, 1, v___x_4670_);
lean_ctor_set_uint8(v___x_4690_, 2, v___x_4670_);
lean_ctor_set_uint8(v___x_4690_, 3, v___x_4670_);
lean_ctor_set_uint8(v___x_4690_, 4, v___x_4670_);
lean_ctor_set_uint8(v___x_4690_, 5, v___x_4685_);
lean_ctor_set_uint8(v___x_4690_, 6, v___x_4685_);
lean_ctor_set_uint8(v___x_4690_, 7, v___x_4670_);
lean_ctor_set_uint8(v___x_4690_, 8, v___x_4685_);
lean_ctor_set_uint8(v___x_4690_, 9, v___x_4687_);
lean_ctor_set_uint8(v___x_4690_, 10, v___x_4688_);
lean_ctor_set_uint8(v___x_4690_, 11, v___x_4685_);
lean_ctor_set_uint8(v___x_4690_, 12, v___x_4685_);
lean_ctor_set_uint8(v___x_4690_, 13, v___x_4685_);
lean_ctor_set_uint8(v___x_4690_, 14, v___x_4689_);
lean_ctor_set_uint8(v___x_4690_, 15, v___x_4685_);
lean_ctor_set_uint8(v___x_4690_, 16, v___x_4685_);
lean_ctor_set_uint8(v___x_4690_, 17, v___x_4685_);
lean_ctor_set_uint8(v___x_4690_, 18, v___x_4685_);
v___x_4691_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4690_);
v___x_4692_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4693_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4694_ = lean_box(0);
v___x_4695_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4695_, 0, v___x_4691_);
lean_ctor_set(v___x_4695_, 1, v___x_4684_);
lean_ctor_set(v___x_4695_, 2, v___x_4692_);
lean_ctor_set(v___x_4695_, 3, v___x_4693_);
lean_ctor_set(v___x_4695_, 4, v___x_4694_);
lean_ctor_set(v___x_4695_, 5, v___x_4678_);
lean_ctor_set(v___x_4695_, 6, v___x_4694_);
lean_ctor_set_uint8(v___x_4695_, sizeof(void*)*7, v___x_4670_);
lean_ctor_set_uint8(v___x_4695_, sizeof(void*)*7 + 1, v___x_4670_);
lean_ctor_set_uint8(v___x_4695_, sizeof(void*)*7 + 2, v___x_4670_);
lean_ctor_set_uint8(v___x_4695_, sizeof(void*)*7 + 3, v___x_4685_);
v___x_4696_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4697_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4698_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4699_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4700_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4701_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4701_, 0, v_env_4660_);
lean_ctor_set(v___x_4701_, 1, v___x_4696_);
lean_ctor_set(v___x_4701_, 2, v_ngen_4672_);
lean_ctor_set(v___x_4701_, 3, v___x_4697_);
lean_ctor_set(v___x_4701_, 4, v___x_4698_);
lean_ctor_set(v___x_4701_, 5, v_core_4673_);
lean_ctor_set(v___x_4701_, 6, v___x_4699_);
lean_ctor_set(v___x_4701_, 7, v___x_4700_);
lean_ctor_set(v___x_4701_, 8, v___x_4693_);
v___x_4702_ = lean_st_mk_ref(v___x_4701_);
v___x_4703_ = l_Lean_inheritedTraceOptions;
v___x_4704_ = lean_st_ref_get(v___x_4703_);
v___x_4705_ = lean_st_ref_get(v___x_4702_);
v_fileName_4706_ = lean_ctor_get(v_cctx_4659_, 0);
v_fileMap_4707_ = lean_ctor_get(v_cctx_4659_, 1);
v_options_4708_ = lean_ctor_get(v_cctx_4659_, 2);
v_currRecDepth_4709_ = lean_ctor_get(v_cctx_4659_, 3);
v_maxRecDepth_4710_ = lean_ctor_get(v_cctx_4659_, 4);
v_ref_4711_ = lean_ctor_get(v_cctx_4659_, 5);
v_currNamespace_4712_ = lean_ctor_get(v_cctx_4659_, 6);
v_openDecls_4713_ = lean_ctor_get(v_cctx_4659_, 7);
v_initHeartbeats_4714_ = lean_ctor_get(v_cctx_4659_, 8);
v_maxHeartbeats_4715_ = lean_ctor_get(v_cctx_4659_, 9);
v_quotContext_4716_ = lean_ctor_get(v_cctx_4659_, 10);
v_currMacroScope_4717_ = lean_ctor_get(v_cctx_4659_, 11);
v_diag_4718_ = lean_ctor_get_uint8(v_cctx_4659_, sizeof(void*)*14);
v_cancelTk_x3f_4719_ = lean_ctor_get(v_cctx_4659_, 12);
v_suppressElabErrors_4720_ = lean_ctor_get_uint8(v_cctx_4659_, sizeof(void*)*14 + 1);
v_isSharedCheck_4806_ = !lean_is_exclusive(v_cctx_4659_);
if (v_isSharedCheck_4806_ == 0)
{
lean_object* v_unused_4807_; 
v_unused_4807_ = lean_ctor_get(v_cctx_4659_, 13);
lean_dec(v_unused_4807_);
v___x_4722_ = v_cctx_4659_;
v_isShared_4723_ = v_isSharedCheck_4806_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_cancelTk_x3f_4719_);
lean_inc(v_currMacroScope_4717_);
lean_inc(v_quotContext_4716_);
lean_inc(v_maxHeartbeats_4715_);
lean_inc(v_initHeartbeats_4714_);
lean_inc(v_openDecls_4713_);
lean_inc(v_currNamespace_4712_);
lean_inc(v_ref_4711_);
lean_inc(v_maxRecDepth_4710_);
lean_inc(v_currRecDepth_4709_);
lean_inc(v_options_4708_);
lean_inc(v_fileMap_4707_);
lean_inc(v_fileName_4706_);
lean_dec(v_cctx_4659_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4806_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v_env_4724_; lean_object* v___x_4726_; 
v_env_4724_ = lean_ctor_get(v___x_4705_, 0);
lean_inc_ref(v_env_4724_);
lean_dec(v___x_4705_);
lean_inc_ref(v_options_4708_);
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 13, v___x_4704_);
v___x_4726_ = v___x_4722_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_fileName_4706_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_fileMap_4707_);
lean_ctor_set(v_reuseFailAlloc_4805_, 2, v_options_4708_);
lean_ctor_set(v_reuseFailAlloc_4805_, 3, v_currRecDepth_4709_);
lean_ctor_set(v_reuseFailAlloc_4805_, 4, v_maxRecDepth_4710_);
lean_ctor_set(v_reuseFailAlloc_4805_, 5, v_ref_4711_);
lean_ctor_set(v_reuseFailAlloc_4805_, 6, v_currNamespace_4712_);
lean_ctor_set(v_reuseFailAlloc_4805_, 7, v_openDecls_4713_);
lean_ctor_set(v_reuseFailAlloc_4805_, 8, v_initHeartbeats_4714_);
lean_ctor_set(v_reuseFailAlloc_4805_, 9, v_maxHeartbeats_4715_);
lean_ctor_set(v_reuseFailAlloc_4805_, 10, v_quotContext_4716_);
lean_ctor_set(v_reuseFailAlloc_4805_, 11, v_currMacroScope_4717_);
lean_ctor_set(v_reuseFailAlloc_4805_, 12, v_cancelTk_x3f_4719_);
lean_ctor_set(v_reuseFailAlloc_4805_, 13, v___x_4704_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, sizeof(void*)*14, v_diag_4718_);
lean_ctor_set_uint8(v_reuseFailAlloc_4805_, sizeof(void*)*14 + 1, v_suppressElabErrors_4720_);
v___x_4726_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
lean_object* v___x_4727_; uint8_t v___x_4728_; lean_object* v___y_4730_; lean_object* v___y_4731_; uint8_t v___y_4783_; uint8_t v___x_4804_; 
v___x_4727_ = l_Lean_diagnostics;
v___x_4728_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4708_, v___x_4727_);
v___x_4804_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4724_);
lean_dec_ref(v_env_4724_);
if (v___x_4804_ == 0)
{
if (v___x_4728_ == 0)
{
lean_inc(v___x_4702_);
v___y_4730_ = v___x_4726_;
v___y_4731_ = v___x_4702_;
goto v___jp_4729_;
}
else
{
v___y_4783_ = v___x_4804_;
goto v___jp_4782_;
}
}
else
{
v___y_4783_ = v___x_4728_;
goto v___jp_4782_;
}
v___jp_4729_:
{
lean_object* v___x_4732_; lean_object* v_fileName_4733_; lean_object* v_fileMap_4734_; lean_object* v_currRecDepth_4735_; lean_object* v_ref_4736_; lean_object* v_currNamespace_4737_; lean_object* v_openDecls_4738_; lean_object* v_initHeartbeats_4739_; lean_object* v_maxHeartbeats_4740_; lean_object* v_quotContext_4741_; lean_object* v_currMacroScope_4742_; lean_object* v_cancelTk_x3f_4743_; uint8_t v_suppressElabErrors_4744_; lean_object* v_inheritedTraceOptions_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4779_; 
v___x_4732_ = lean_st_mk_ref(v___x_4686_);
v_fileName_4733_ = lean_ctor_get(v___y_4730_, 0);
v_fileMap_4734_ = lean_ctor_get(v___y_4730_, 1);
v_currRecDepth_4735_ = lean_ctor_get(v___y_4730_, 3);
v_ref_4736_ = lean_ctor_get(v___y_4730_, 5);
v_currNamespace_4737_ = lean_ctor_get(v___y_4730_, 6);
v_openDecls_4738_ = lean_ctor_get(v___y_4730_, 7);
v_initHeartbeats_4739_ = lean_ctor_get(v___y_4730_, 8);
v_maxHeartbeats_4740_ = lean_ctor_get(v___y_4730_, 9);
v_quotContext_4741_ = lean_ctor_get(v___y_4730_, 10);
v_currMacroScope_4742_ = lean_ctor_get(v___y_4730_, 11);
v_cancelTk_x3f_4743_ = lean_ctor_get(v___y_4730_, 12);
v_suppressElabErrors_4744_ = lean_ctor_get_uint8(v___y_4730_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4745_ = lean_ctor_get(v___y_4730_, 13);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___y_4730_);
if (v_isSharedCheck_4779_ == 0)
{
lean_object* v_unused_4780_; lean_object* v_unused_4781_; 
v_unused_4780_ = lean_ctor_get(v___y_4730_, 4);
lean_dec(v_unused_4780_);
v_unused_4781_ = lean_ctor_get(v___y_4730_, 2);
lean_dec(v_unused_4781_);
v___x_4747_ = v___y_4730_;
v_isShared_4748_ = v_isSharedCheck_4779_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_inheritedTraceOptions_4745_);
lean_inc(v_cancelTk_x3f_4743_);
lean_inc(v_currMacroScope_4742_);
lean_inc(v_quotContext_4741_);
lean_inc(v_maxHeartbeats_4740_);
lean_inc(v_initHeartbeats_4739_);
lean_inc(v_openDecls_4738_);
lean_inc(v_currNamespace_4737_);
lean_inc(v_ref_4736_);
lean_inc(v_currRecDepth_4735_);
lean_inc(v_fileMap_4734_);
lean_inc(v_fileName_4733_);
lean_dec(v___y_4730_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4779_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4752_; 
v___x_4749_ = l_Lean_maxRecDepth;
v___x_4750_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4708_, v___x_4749_);
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 4, v___x_4750_);
lean_ctor_set(v___x_4747_, 2, v_options_4708_);
v___x_4752_ = v___x_4747_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_fileName_4733_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_fileMap_4734_);
lean_ctor_set(v_reuseFailAlloc_4778_, 2, v_options_4708_);
lean_ctor_set(v_reuseFailAlloc_4778_, 3, v_currRecDepth_4735_);
lean_ctor_set(v_reuseFailAlloc_4778_, 4, v___x_4750_);
lean_ctor_set(v_reuseFailAlloc_4778_, 5, v_ref_4736_);
lean_ctor_set(v_reuseFailAlloc_4778_, 6, v_currNamespace_4737_);
lean_ctor_set(v_reuseFailAlloc_4778_, 7, v_openDecls_4738_);
lean_ctor_set(v_reuseFailAlloc_4778_, 8, v_initHeartbeats_4739_);
lean_ctor_set(v_reuseFailAlloc_4778_, 9, v_maxHeartbeats_4740_);
lean_ctor_set(v_reuseFailAlloc_4778_, 10, v_quotContext_4741_);
lean_ctor_set(v_reuseFailAlloc_4778_, 11, v_currMacroScope_4742_);
lean_ctor_set(v_reuseFailAlloc_4778_, 12, v_cancelTk_x3f_4743_);
lean_ctor_set(v_reuseFailAlloc_4778_, 13, v_inheritedTraceOptions_4745_);
lean_ctor_set_uint8(v_reuseFailAlloc_4778_, sizeof(void*)*14 + 1, v_suppressElabErrors_4744_);
v___x_4752_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
lean_object* v___x_4753_; 
lean_ctor_set_uint8(v___x_4752_, sizeof(void*)*14, v___x_4728_);
lean_inc(v___x_4732_);
lean_inc(v_name_4666_);
v___x_4753_ = lean_apply_7(v_act_4665_, v_name_4666_, v_constInfo_4667_, v___x_4695_, v___x_4732_, v___x_4752_, v___y_4731_, lean_box(0));
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_object* v_a_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v_ngen_4757_; lean_object* v_cache_4758_; lean_object* v_cache_4759_; lean_object* v___x_4761_; 
lean_dec(v_name_4666_);
lean_dec(v_modName_4661_);
v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
lean_inc(v_a_4754_);
lean_dec_ref(v___x_4753_);
v___x_4755_ = lean_st_ref_get(v___x_4732_);
lean_dec(v___x_4732_);
v___x_4756_ = lean_st_ref_get(v___x_4702_);
lean_dec(v___x_4702_);
v_ngen_4757_ = lean_ctor_get(v___x_4756_, 2);
lean_inc_ref(v_ngen_4757_);
v_cache_4758_ = lean_ctor_get(v___x_4756_, 5);
lean_inc_ref(v_cache_4758_);
lean_dec(v___x_4756_);
v_cache_4759_ = lean_ctor_get(v___x_4755_, 1);
lean_inc_ref(v_cache_4759_);
lean_dec(v___x_4755_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 2, v_cache_4759_);
lean_ctor_set(v___x_4676_, 1, v_cache_4758_);
lean_ctor_set(v___x_4676_, 0, v_ngen_4757_);
v___x_4761_ = v___x_4676_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_ngen_4757_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v_cache_4758_);
lean_ctor_set(v_reuseFailAlloc_4772_, 2, v_cache_4759_);
v___x_4761_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; 
v___x_4762_ = lean_st_ref_set(v_cacheRef_4663_, v___x_4761_);
v___x_4763_ = lean_array_get_size(v_a_4754_);
v___x_4764_ = lean_nat_dec_lt(v___x_4678_, v___x_4763_);
if (v___x_4764_ == 0)
{
lean_dec(v_a_4754_);
return v_tree_4664_;
}
else
{
uint8_t v___x_4765_; 
v___x_4765_ = lean_nat_dec_le(v___x_4763_, v___x_4763_);
if (v___x_4765_ == 0)
{
if (v___x_4764_ == 0)
{
lean_dec(v_a_4754_);
return v_tree_4664_;
}
else
{
size_t v___x_4766_; size_t v___x_4767_; lean_object* v___x_4768_; 
v___x_4766_ = ((size_t)0ULL);
v___x_4767_ = lean_usize_of_nat(v___x_4763_);
v___x_4768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4754_, v___x_4766_, v___x_4767_, v_tree_4664_);
lean_dec(v_a_4754_);
return v___x_4768_;
}
}
else
{
size_t v___x_4769_; size_t v___x_4770_; lean_object* v___x_4771_; 
v___x_4769_ = ((size_t)0ULL);
v___x_4770_ = lean_usize_of_nat(v___x_4763_);
v___x_4771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4754_, v___x_4769_, v___x_4770_, v_tree_4664_);
lean_dec(v_a_4754_);
return v___x_4771_;
}
}
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
lean_dec(v___x_4732_);
lean_dec(v___x_4702_);
lean_del_object(v___x_4676_);
v_a_4773_ = lean_ctor_get(v___x_4753_, 0);
lean_inc(v_a_4773_);
lean_dec_ref(v___x_4753_);
v___x_4774_ = lean_st_ref_take(v_d_4662_);
v___x_4775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4775_, 0, v_modName_4661_);
lean_ctor_set(v___x_4775_, 1, v_name_4666_);
lean_ctor_set(v___x_4775_, 2, v_a_4773_);
v___x_4776_ = lean_array_push(v___x_4774_, v___x_4775_);
v___x_4777_ = lean_st_ref_set(v_d_4662_, v___x_4776_);
return v_tree_4664_;
}
}
}
}
v___jp_4782_:
{
if (v___y_4783_ == 0)
{
lean_object* v___x_4784_; lean_object* v_env_4785_; lean_object* v_nextMacroScope_4786_; lean_object* v_ngen_4787_; lean_object* v_auxDeclNGen_4788_; lean_object* v_traceState_4789_; lean_object* v_messages_4790_; lean_object* v_infoState_4791_; lean_object* v_snapshotTasks_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4802_; 
v___x_4784_ = lean_st_ref_take(v___x_4702_);
v_env_4785_ = lean_ctor_get(v___x_4784_, 0);
v_nextMacroScope_4786_ = lean_ctor_get(v___x_4784_, 1);
v_ngen_4787_ = lean_ctor_get(v___x_4784_, 2);
v_auxDeclNGen_4788_ = lean_ctor_get(v___x_4784_, 3);
v_traceState_4789_ = lean_ctor_get(v___x_4784_, 4);
v_messages_4790_ = lean_ctor_get(v___x_4784_, 6);
v_infoState_4791_ = lean_ctor_get(v___x_4784_, 7);
v_snapshotTasks_4792_ = lean_ctor_get(v___x_4784_, 8);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4802_ == 0)
{
lean_object* v_unused_4803_; 
v_unused_4803_ = lean_ctor_get(v___x_4784_, 5);
lean_dec(v_unused_4803_);
v___x_4794_ = v___x_4784_;
v_isShared_4795_ = v_isSharedCheck_4802_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_snapshotTasks_4792_);
lean_inc(v_infoState_4791_);
lean_inc(v_messages_4790_);
lean_inc(v_traceState_4789_);
lean_inc(v_auxDeclNGen_4788_);
lean_inc(v_ngen_4787_);
lean_inc(v_nextMacroScope_4786_);
lean_inc(v_env_4785_);
lean_dec(v___x_4784_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4802_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4799_; 
v___x_4796_ = l_Lean_Kernel_enableDiag(v_env_4785_, v___x_4728_);
v___x_4797_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 5, v___x_4797_);
lean_ctor_set(v___x_4794_, 0, v___x_4796_);
v___x_4799_ = v___x_4794_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4796_);
lean_ctor_set(v_reuseFailAlloc_4801_, 1, v_nextMacroScope_4786_);
lean_ctor_set(v_reuseFailAlloc_4801_, 2, v_ngen_4787_);
lean_ctor_set(v_reuseFailAlloc_4801_, 3, v_auxDeclNGen_4788_);
lean_ctor_set(v_reuseFailAlloc_4801_, 4, v_traceState_4789_);
lean_ctor_set(v_reuseFailAlloc_4801_, 5, v___x_4797_);
lean_ctor_set(v_reuseFailAlloc_4801_, 6, v_messages_4790_);
lean_ctor_set(v_reuseFailAlloc_4801_, 7, v_infoState_4791_);
lean_ctor_set(v_reuseFailAlloc_4801_, 8, v_snapshotTasks_4792_);
v___x_4799_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
lean_object* v___x_4800_; 
v___x_4800_ = lean_st_ref_set(v___x_4702_, v___x_4799_);
lean_inc(v___x_4702_);
v___y_4730_ = v___x_4726_;
v___y_4731_ = v___x_4702_;
goto v___jp_4729_;
}
}
}
else
{
lean_inc(v___x_4702_);
v___y_4730_ = v___x_4726_;
v___y_4731_ = v___x_4702_;
goto v___jp_4729_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_constInfo_4667_);
lean_dec(v_name_4666_);
lean_dec_ref(v_act_4665_);
lean_dec(v_modName_4661_);
lean_dec_ref(v_env_4660_);
lean_dec_ref(v_cctx_4659_);
return v_tree_4664_;
}
}
else
{
lean_dec_ref(v_constInfo_4667_);
lean_dec(v_name_4666_);
lean_dec_ref(v_act_4665_);
lean_dec(v_modName_4661_);
lean_dec_ref(v_env_4660_);
lean_dec_ref(v_cctx_4659_);
return v_tree_4664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4809_, lean_object* v_env_4810_, lean_object* v_modName_4811_, lean_object* v_d_4812_, lean_object* v_cacheRef_4813_, lean_object* v_tree_4814_, lean_object* v_act_4815_, lean_object* v_name_4816_, lean_object* v_constInfo_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4809_, v_env_4810_, v_modName_4811_, v_d_4812_, v_cacheRef_4813_, v_tree_4814_, v_act_4815_, v_name_4816_, v_constInfo_4817_);
lean_dec(v_cacheRef_4813_);
lean_dec(v_d_4812_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4820_, lean_object* v_cctx_4821_, lean_object* v_env_4822_, lean_object* v_modName_4823_, lean_object* v_d_4824_, lean_object* v_cacheRef_4825_, lean_object* v_tree_4826_, lean_object* v_act_4827_, lean_object* v_name_4828_, lean_object* v_constInfo_4829_){
_start:
{
lean_object* v___x_4831_; 
v___x_4831_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4821_, v_env_4822_, v_modName_4823_, v_d_4824_, v_cacheRef_4825_, v_tree_4826_, v_act_4827_, v_name_4828_, v_constInfo_4829_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4832_, lean_object* v_cctx_4833_, lean_object* v_env_4834_, lean_object* v_modName_4835_, lean_object* v_d_4836_, lean_object* v_cacheRef_4837_, lean_object* v_tree_4838_, lean_object* v_act_4839_, lean_object* v_name_4840_, lean_object* v_constInfo_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4832_, v_cctx_4833_, v_env_4834_, v_modName_4835_, v_d_4836_, v_cacheRef_4837_, v_tree_4838_, v_act_4839_, v_name_4840_, v_constInfo_4841_);
lean_dec(v_cacheRef_4837_);
lean_dec(v_d_4836_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object* v_00_u03b1_4844_, lean_object* v_as_4845_, size_t v_i_4846_, size_t v_stop_4847_, lean_object* v_b_4848_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4845_, v_i_4846_, v_stop_4847_, v_b_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object* v_00_u03b1_4850_, lean_object* v_as_4851_, lean_object* v_i_4852_, lean_object* v_stop_4853_, lean_object* v_b_4854_){
_start:
{
size_t v_i_boxed_4855_; size_t v_stop_boxed_4856_; lean_object* v_res_4857_; 
v_i_boxed_4855_ = lean_unbox_usize(v_i_4852_);
lean_dec(v_i_4852_);
v_stop_boxed_4856_ = lean_unbox_usize(v_stop_4853_);
lean_dec(v_stop_4853_);
v_res_4857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(v_00_u03b1_4850_, v_as_4851_, v_i_boxed_4855_, v_stop_boxed_4856_, v_b_4854_);
lean_dec_ref(v_as_4851_);
return v_res_4857_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1(void){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4860_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0));
v___x_4861_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
lean_ctor_set(v___x_4862_, 1, v___x_4860_);
return v___x_4862_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2(void){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4863_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0));
v___x_4864_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1);
v___x_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
lean_ctor_set(v___x_4865_, 1, v___x_4863_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4866_){
_start:
{
lean_object* v___x_4867_; 
v___x_4867_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4868_, lean_object* v_y_4869_){
_start:
{
lean_object* v_tree_4870_; lean_object* v_errors_4871_; lean_object* v_tree_4872_; lean_object* v_errors_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4882_; 
v_tree_4870_ = lean_ctor_get(v_x_4868_, 0);
lean_inc_ref(v_tree_4870_);
v_errors_4871_ = lean_ctor_get(v_x_4868_, 1);
lean_inc_ref(v_errors_4871_);
lean_dec_ref(v_x_4868_);
v_tree_4872_ = lean_ctor_get(v_y_4869_, 0);
v_errors_4873_ = lean_ctor_get(v_y_4869_, 1);
v_isSharedCheck_4882_ = !lean_is_exclusive(v_y_4869_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4875_ = v_y_4869_;
v_isShared_4876_ = v_isSharedCheck_4882_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_errors_4873_);
lean_inc(v_tree_4872_);
lean_dec(v_y_4869_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4882_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4880_; 
v___x_4877_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4870_, v_tree_4872_);
v___x_4878_ = l_Array_append___redArg(v_errors_4871_, v_errors_4873_);
lean_dec_ref(v_errors_4873_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 1, v___x_4878_);
lean_ctor_set(v___x_4875_, 0, v___x_4877_);
v___x_4880_ = v___x_4875_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4877_);
lean_ctor_set(v_reuseFailAlloc_4881_, 1, v___x_4878_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4883_, lean_object* v_x_4884_, lean_object* v_y_4885_){
_start:
{
lean_object* v___x_4886_; 
v___x_4886_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4884_, v_y_4885_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4888_){
_start:
{
lean_object* v___x_4889_; 
v___x_4889_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
return v___x_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4890_, lean_object* v_tree_4891_){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4893_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4894_ = lean_st_ref_swap(v_d_4890_, v___x_4893_);
v___x_4895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4895_, 0, v_tree_4891_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4896_, lean_object* v_tree_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4896_, v_tree_4897_);
lean_dec(v_d_4896_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4900_, lean_object* v_d_4901_, lean_object* v_tree_4902_){
_start:
{
lean_object* v___x_4904_; 
v___x_4904_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4901_, v_tree_4902_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4905_, lean_object* v_d_4906_, lean_object* v_tree_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4905_, v_d_4906_, v_tree_4907_);
lean_dec(v_d_4906_);
return v_res_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4910_, lean_object* v_env_4911_, lean_object* v_act_4912_, lean_object* v_d_4913_, lean_object* v_cacheRef_4914_, lean_object* v_tree_4915_, lean_object* v_mname_4916_, lean_object* v_mdata_4917_, lean_object* v_i_4918_){
_start:
{
lean_object* v_constants_4920_; lean_object* v___x_4921_; uint8_t v___x_4922_; 
v_constants_4920_ = lean_ctor_get(v_mdata_4917_, 2);
v___x_4921_ = lean_array_get_size(v_constants_4920_);
v___x_4922_ = lean_nat_dec_lt(v_i_4918_, v___x_4921_);
if (v___x_4922_ == 0)
{
lean_dec(v_i_4918_);
lean_dec(v_mname_4916_);
lean_dec_ref(v_act_4912_);
lean_dec_ref(v_env_4911_);
lean_dec_ref(v_cctx_4910_);
return v_tree_4915_;
}
else
{
lean_object* v_constInfo_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_constInfo_4923_ = lean_array_fget_borrowed(v_constants_4920_, v_i_4918_);
v___x_4924_ = l_Lean_ConstantInfo_name(v_constInfo_4923_);
lean_inc(v_constInfo_4923_);
lean_inc_ref(v_act_4912_);
lean_inc(v_mname_4916_);
lean_inc_ref(v_env_4911_);
lean_inc_ref(v_cctx_4910_);
v___x_4925_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4910_, v_env_4911_, v_mname_4916_, v_d_4913_, v_cacheRef_4914_, v_tree_4915_, v_act_4912_, v___x_4924_, v_constInfo_4923_);
v___x_4926_ = lean_unsigned_to_nat(1u);
v___x_4927_ = lean_nat_add(v_i_4918_, v___x_4926_);
lean_dec(v_i_4918_);
v_tree_4915_ = v___x_4925_;
v_i_4918_ = v___x_4927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4929_, lean_object* v_env_4930_, lean_object* v_act_4931_, lean_object* v_d_4932_, lean_object* v_cacheRef_4933_, lean_object* v_tree_4934_, lean_object* v_mname_4935_, lean_object* v_mdata_4936_, lean_object* v_i_4937_, lean_object* v_a_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4929_, v_env_4930_, v_act_4931_, v_d_4932_, v_cacheRef_4933_, v_tree_4934_, v_mname_4935_, v_mdata_4936_, v_i_4937_);
lean_dec_ref(v_mdata_4936_);
lean_dec(v_cacheRef_4933_);
lean_dec(v_d_4932_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4940_, lean_object* v_cctx_4941_, lean_object* v_env_4942_, lean_object* v_act_4943_, lean_object* v_d_4944_, lean_object* v_cacheRef_4945_, lean_object* v_tree_4946_, lean_object* v_mname_4947_, lean_object* v_mdata_4948_, lean_object* v_i_4949_){
_start:
{
lean_object* v___x_4951_; 
v___x_4951_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4941_, v_env_4942_, v_act_4943_, v_d_4944_, v_cacheRef_4945_, v_tree_4946_, v_mname_4947_, v_mdata_4948_, v_i_4949_);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4952_, lean_object* v_cctx_4953_, lean_object* v_env_4954_, lean_object* v_act_4955_, lean_object* v_d_4956_, lean_object* v_cacheRef_4957_, lean_object* v_tree_4958_, lean_object* v_mname_4959_, lean_object* v_mdata_4960_, lean_object* v_i_4961_, lean_object* v_a_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4952_, v_cctx_4953_, v_env_4954_, v_act_4955_, v_d_4956_, v_cacheRef_4957_, v_tree_4958_, v_mname_4959_, v_mdata_4960_, v_i_4961_);
lean_dec_ref(v_mdata_4960_);
lean_dec(v_cacheRef_4957_);
lean_dec(v_d_4956_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4964_, lean_object* v_env_4965_, lean_object* v_act_4966_, lean_object* v_d_4967_, lean_object* v_cacheRef_4968_, lean_object* v_tree_4969_, lean_object* v_start_4970_, lean_object* v_stop_4971_){
_start:
{
uint8_t v___x_4973_; 
v___x_4973_ = lean_nat_dec_lt(v_start_4970_, v_stop_4971_);
if (v___x_4973_ == 0)
{
lean_object* v___x_4974_; 
lean_dec(v_start_4970_);
lean_dec_ref(v_act_4966_);
lean_dec_ref(v_env_4965_);
lean_dec_ref(v_cctx_4964_);
v___x_4974_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4967_, v_tree_4969_);
return v___x_4974_;
}
else
{
lean_object* v___x_4975_; lean_object* v_moduleData_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v_mname_4979_; lean_object* v___x_4980_; lean_object* v_mdata_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4975_ = l_Lean_Environment_header(v_env_4965_);
v_moduleData_4976_ = lean_ctor_get(v___x_4975_, 6);
lean_inc_ref(v_moduleData_4976_);
v___x_4977_ = lean_box(0);
v___x_4978_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4975_);
v_mname_4979_ = lean_array_get(v___x_4977_, v___x_4978_, v_start_4970_);
lean_dec_ref(v___x_4978_);
v___x_4980_ = l_Lean_instInhabitedModuleData_default;
v_mdata_4981_ = lean_array_get(v___x_4980_, v_moduleData_4976_, v_start_4970_);
lean_dec_ref(v_moduleData_4976_);
v___x_4982_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4966_);
lean_inc_ref(v_env_4965_);
lean_inc_ref(v_cctx_4964_);
v___x_4983_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4964_, v_env_4965_, v_act_4966_, v_d_4967_, v_cacheRef_4968_, v_tree_4969_, v_mname_4979_, v_mdata_4981_, v___x_4982_);
lean_dec(v_mdata_4981_);
v___x_4984_ = lean_unsigned_to_nat(1u);
v___x_4985_ = lean_nat_add(v_start_4970_, v___x_4984_);
lean_dec(v_start_4970_);
v_tree_4969_ = v___x_4983_;
v_start_4970_ = v___x_4985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_4987_, lean_object* v_env_4988_, lean_object* v_act_4989_, lean_object* v_d_4990_, lean_object* v_cacheRef_4991_, lean_object* v_tree_4992_, lean_object* v_start_4993_, lean_object* v_stop_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4987_, v_env_4988_, v_act_4989_, v_d_4990_, v_cacheRef_4991_, v_tree_4992_, v_start_4993_, v_stop_4994_);
lean_dec(v_stop_4994_);
lean_dec(v_cacheRef_4991_);
lean_dec(v_d_4990_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_4997_, lean_object* v_cctx_4998_, lean_object* v_env_4999_, lean_object* v_act_5000_, lean_object* v_d_5001_, lean_object* v_cacheRef_5002_, lean_object* v_tree_5003_, lean_object* v_start_5004_, lean_object* v_stop_5005_){
_start:
{
lean_object* v___x_5007_; 
v___x_5007_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4998_, v_env_4999_, v_act_5000_, v_d_5001_, v_cacheRef_5002_, v_tree_5003_, v_start_5004_, v_stop_5005_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_5008_, lean_object* v_cctx_5009_, lean_object* v_env_5010_, lean_object* v_act_5011_, lean_object* v_d_5012_, lean_object* v_cacheRef_5013_, lean_object* v_tree_5014_, lean_object* v_start_5015_, lean_object* v_stop_5016_, lean_object* v_a_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_5008_, v_cctx_5009_, v_env_5010_, v_act_5011_, v_d_5012_, v_cacheRef_5013_, v_tree_5014_, v_start_5015_, v_stop_5016_);
lean_dec(v_stop_5016_);
lean_dec(v_cacheRef_5013_);
lean_dec(v_d_5012_);
return v_res_5018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5019_, lean_object* v_ngen_5020_, lean_object* v_env_5021_, lean_object* v_act_5022_, lean_object* v_start_5023_, lean_object* v_stop_5024_){
_start:
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5026_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5020_);
v___x_5027_ = lean_st_mk_ref(v___x_5026_);
v___x_5028_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5029_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1);
v___x_5030_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5019_, v_env_5021_, v_act_5022_, v___x_5028_, v___x_5027_, v___x_5029_, v_start_5023_, v_stop_5024_);
lean_dec(v___x_5027_);
lean_dec(v___x_5028_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5031_, lean_object* v_ngen_5032_, lean_object* v_env_5033_, lean_object* v_act_5034_, lean_object* v_start_5035_, lean_object* v_stop_5036_, lean_object* v_a_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5031_, v_ngen_5032_, v_env_5033_, v_act_5034_, v_start_5035_, v_stop_5036_);
lean_dec(v_stop_5036_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5039_, lean_object* v_cctx_5040_, lean_object* v_ngen_5041_, lean_object* v_env_5042_, lean_object* v_act_5043_, lean_object* v_start_5044_, lean_object* v_stop_5045_){
_start:
{
lean_object* v___x_5047_; 
v___x_5047_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5040_, v_ngen_5041_, v_env_5042_, v_act_5043_, v_start_5044_, v_stop_5045_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5048_, lean_object* v_cctx_5049_, lean_object* v_ngen_5050_, lean_object* v_env_5051_, lean_object* v_act_5052_, lean_object* v_start_5053_, lean_object* v_stop_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5048_, v_cctx_5049_, v_ngen_5050_, v_env_5051_, v_act_5052_, v_start_5053_, v_stop_5054_);
lean_dec(v_stop_5054_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5057_, lean_object* v_x1_5058_, lean_object* v_x2_5059_){
_start:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5060_ = lean_task_get_own(v_x2_5059_);
v___x_5061_ = lean_apply_2(v_inst_5057_, v_x1_5058_, v___x_5060_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5062_, lean_object* v_z_5063_, lean_object* v_tasks_5064_){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; uint8_t v___x_5068_; 
v___x_5065_ = lean_unsigned_to_nat(0u);
v___x_5066_ = lean_array_get_size(v_tasks_5064_);
v___x_5067_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5068_ = lean_nat_dec_lt(v___x_5065_, v___x_5066_);
if (v___x_5068_ == 0)
{
lean_dec_ref(v_tasks_5064_);
lean_dec(v_inst_5062_);
return v_z_5063_;
}
else
{
lean_object* v___f_5069_; uint8_t v___x_5070_; 
v___f_5069_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5069_, 0, v_inst_5062_);
v___x_5070_ = lean_nat_dec_le(v___x_5066_, v___x_5066_);
if (v___x_5070_ == 0)
{
if (v___x_5068_ == 0)
{
lean_dec_ref(v___f_5069_);
lean_dec_ref(v_tasks_5064_);
return v_z_5063_;
}
else
{
size_t v___x_5071_; size_t v___x_5072_; lean_object* v___x_5073_; 
v___x_5071_ = ((size_t)0ULL);
v___x_5072_ = lean_usize_of_nat(v___x_5066_);
v___x_5073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5067_, v___f_5069_, v_tasks_5064_, v___x_5071_, v___x_5072_, v_z_5063_);
return v___x_5073_;
}
}
else
{
size_t v___x_5074_; size_t v___x_5075_; lean_object* v___x_5076_; 
v___x_5074_ = ((size_t)0ULL);
v___x_5075_ = lean_usize_of_nat(v___x_5066_);
v___x_5076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5067_, v___f_5069_, v_tasks_5064_, v___x_5074_, v___x_5075_, v_z_5063_);
return v___x_5076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5077_, lean_object* v_inst_5078_, lean_object* v_z_5079_, lean_object* v_tasks_5080_){
_start:
{
lean_object* v___x_5081_; 
v___x_5081_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5078_, v_z_5079_, v_tasks_5080_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5082_, lean_object* v___x_5083_, lean_object* v_____r_5084_){
_start:
{
lean_object* v___x_5085_; 
v___x_5085_ = lean_apply_2(v_toPure_5082_, lean_box(0), v___x_5083_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5086_, lean_object* v_setNGen_5087_, lean_object* v_toBind_5088_, lean_object* v_ngen_5089_){
_start:
{
lean_object* v_namePrefix_5090_; lean_object* v_idx_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5105_; 
v_namePrefix_5090_ = lean_ctor_get(v_ngen_5089_, 0);
v_idx_5091_ = lean_ctor_get(v_ngen_5089_, 1);
v_isSharedCheck_5105_ = !lean_is_exclusive(v_ngen_5089_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5093_ = v_ngen_5089_;
v_isShared_5094_ = v_isSharedCheck_5105_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_idx_5091_);
lean_inc(v_namePrefix_5090_);
lean_dec(v_ngen_5089_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5105_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5098_; 
lean_inc(v_idx_5091_);
lean_inc(v_namePrefix_5090_);
v___x_5095_ = l_Lean_Name_num___override(v_namePrefix_5090_, v_idx_5091_);
v___x_5096_ = lean_unsigned_to_nat(1u);
if (v_isShared_5094_ == 0)
{
lean_ctor_set(v___x_5093_, 1, v___x_5096_);
lean_ctor_set(v___x_5093_, 0, v___x_5095_);
v___x_5098_ = v___x_5093_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5095_);
lean_ctor_set(v_reuseFailAlloc_5104_, 1, v___x_5096_);
v___x_5098_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
lean_object* v___f_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___f_5099_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5099_, 0, v_toPure_5086_);
lean_closure_set(v___f_5099_, 1, v___x_5098_);
v___x_5100_ = lean_nat_add(v_idx_5091_, v___x_5096_);
lean_dec(v_idx_5091_);
v___x_5101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5101_, 0, v_namePrefix_5090_);
lean_ctor_set(v___x_5101_, 1, v___x_5100_);
v___x_5102_ = lean_apply_1(v_setNGen_5087_, v___x_5101_);
v___x_5103_ = lean_apply_4(v_toBind_5088_, lean_box(0), lean_box(0), v___x_5102_, v___f_5099_);
return v___x_5103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5106_, lean_object* v_inst_5107_){
_start:
{
lean_object* v_toApplicative_5108_; lean_object* v_toBind_5109_; lean_object* v_getNGen_5110_; lean_object* v_setNGen_5111_; lean_object* v_toPure_5112_; lean_object* v___f_5113_; lean_object* v___x_5114_; 
v_toApplicative_5108_ = lean_ctor_get(v_inst_5106_, 0);
lean_inc_ref(v_toApplicative_5108_);
v_toBind_5109_ = lean_ctor_get(v_inst_5106_, 1);
lean_inc_n(v_toBind_5109_, 2);
lean_dec_ref(v_inst_5106_);
v_getNGen_5110_ = lean_ctor_get(v_inst_5107_, 0);
lean_inc(v_getNGen_5110_);
v_setNGen_5111_ = lean_ctor_get(v_inst_5107_, 1);
lean_inc(v_setNGen_5111_);
lean_dec_ref(v_inst_5107_);
v_toPure_5112_ = lean_ctor_get(v_toApplicative_5108_, 1);
lean_inc(v_toPure_5112_);
lean_dec_ref(v_toApplicative_5108_);
v___f_5113_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5113_, 0, v_toPure_5112_);
lean_closure_set(v___f_5113_, 1, v_setNGen_5111_);
lean_closure_set(v___f_5113_, 2, v_toBind_5109_);
v___x_5114_ = lean_apply_4(v_toBind_5109_, lean_box(0), lean_box(0), v_getNGen_5110_, v___f_5113_);
return v___x_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5115_, lean_object* v_inst_5116_, lean_object* v_inst_5117_){
_start:
{
lean_object* v___x_5118_; 
v___x_5118_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5116_, v_inst_5117_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0(lean_object* v_cctx_5119_, lean_object* v_env_5120_, lean_object* v_mainModule_5121_, lean_object* v_d_5122_, lean_object* v_val_5123_, lean_object* v_act_5124_, lean_object* v_t_5125_, lean_object* v_n_5126_, lean_object* v_c_5127_){
_start:
{
lean_object* v___x_5129_; 
v___x_5129_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5119_, v_env_5120_, v_mainModule_5121_, v_d_5122_, v_val_5123_, v_t_5125_, v_act_5124_, v_n_5126_, v_c_5127_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0___boxed(lean_object* v_cctx_5130_, lean_object* v_env_5131_, lean_object* v_mainModule_5132_, lean_object* v_d_5133_, lean_object* v_val_5134_, lean_object* v_act_5135_, lean_object* v_t_5136_, lean_object* v_n_5137_, lean_object* v_c_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0(v_cctx_5130_, v_env_5131_, v_mainModule_5132_, v_d_5133_, v_val_5134_, v_act_5135_, v_t_5136_, v_n_5137_, v_c_5138_);
lean_dec(v_val_5134_);
lean_dec(v_d_5133_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(lean_object* v_f_5141_, lean_object* v_keys_5142_, lean_object* v_vals_5143_, lean_object* v_i_5144_, lean_object* v_acc_5145_){
_start:
{
lean_object* v___x_5147_; uint8_t v___x_5148_; 
v___x_5147_ = lean_array_get_size(v_keys_5142_);
v___x_5148_ = lean_nat_dec_lt(v_i_5144_, v___x_5147_);
if (v___x_5148_ == 0)
{
lean_dec(v_i_5144_);
lean_dec_ref(v_f_5141_);
return v_acc_5145_;
}
else
{
lean_object* v_k_5149_; lean_object* v_v_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
v_k_5149_ = lean_array_fget_borrowed(v_keys_5142_, v_i_5144_);
v_v_5150_ = lean_array_fget_borrowed(v_vals_5143_, v_i_5144_);
lean_inc_ref(v_f_5141_);
lean_inc(v_v_5150_);
lean_inc(v_k_5149_);
v___x_5151_ = lean_apply_4(v_f_5141_, v_acc_5145_, v_k_5149_, v_v_5150_, lean_box(0));
v___x_5152_ = lean_unsigned_to_nat(1u);
v___x_5153_ = lean_nat_add(v_i_5144_, v___x_5152_);
lean_dec(v_i_5144_);
v_i_5144_ = v___x_5153_;
v_acc_5145_ = v___x_5151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_5155_, lean_object* v_keys_5156_, lean_object* v_vals_5157_, lean_object* v_i_5158_, lean_object* v_acc_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(v_f_5155_, v_keys_5156_, v_vals_5157_, v_i_5158_, v_acc_5159_);
lean_dec_ref(v_vals_5157_);
lean_dec_ref(v_keys_5156_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(lean_object* v_f_5162_, lean_object* v_x_5163_, lean_object* v_x_5164_){
_start:
{
if (lean_obj_tag(v_x_5163_) == 0)
{
lean_object* v_es_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; uint8_t v___x_5169_; 
v_es_5166_ = lean_ctor_get(v_x_5163_, 0);
v___x_5167_ = lean_unsigned_to_nat(0u);
v___x_5168_ = lean_array_get_size(v_es_5166_);
v___x_5169_ = lean_nat_dec_lt(v___x_5167_, v___x_5168_);
if (v___x_5169_ == 0)
{
lean_dec_ref(v_f_5162_);
return v_x_5164_;
}
else
{
uint8_t v___x_5170_; 
v___x_5170_ = lean_nat_dec_le(v___x_5168_, v___x_5168_);
if (v___x_5170_ == 0)
{
if (v___x_5169_ == 0)
{
lean_dec_ref(v_f_5162_);
return v_x_5164_;
}
else
{
size_t v___x_5171_; size_t v___x_5172_; lean_object* v___x_5173_; 
v___x_5171_ = ((size_t)0ULL);
v___x_5172_ = lean_usize_of_nat(v___x_5168_);
v___x_5173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5162_, v_es_5166_, v___x_5171_, v___x_5172_, v_x_5164_);
return v___x_5173_;
}
}
else
{
size_t v___x_5174_; size_t v___x_5175_; lean_object* v___x_5176_; 
v___x_5174_ = ((size_t)0ULL);
v___x_5175_ = lean_usize_of_nat(v___x_5168_);
v___x_5176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5162_, v_es_5166_, v___x_5174_, v___x_5175_, v_x_5164_);
return v___x_5176_;
}
}
}
else
{
lean_object* v_ks_5177_; lean_object* v_vs_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v_ks_5177_ = lean_ctor_get(v_x_5163_, 0);
v_vs_5178_ = lean_ctor_get(v_x_5163_, 1);
v___x_5179_ = lean_unsigned_to_nat(0u);
v___x_5180_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(v_f_5162_, v_ks_5177_, v_vs_5178_, v___x_5179_, v_x_5164_);
return v___x_5180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(lean_object* v_f_5181_, lean_object* v_as_5182_, size_t v_i_5183_, size_t v_stop_5184_, lean_object* v_b_5185_){
_start:
{
lean_object* v_val_5188_; lean_object* v___y_5193_; uint8_t v___x_5194_; 
v___x_5194_ = lean_usize_dec_eq(v_i_5183_, v_stop_5184_);
if (v___x_5194_ == 0)
{
lean_object* v___x_5195_; 
v___x_5195_ = lean_array_uget_borrowed(v_as_5182_, v_i_5183_);
switch(lean_obj_tag(v___x_5195_))
{
case 0:
{
lean_object* v_key_5196_; lean_object* v_val_5197_; lean_object* v___x_5198_; 
v_key_5196_ = lean_ctor_get(v___x_5195_, 0);
v_val_5197_ = lean_ctor_get(v___x_5195_, 1);
lean_inc_ref(v_f_5181_);
lean_inc(v_val_5197_);
lean_inc(v_key_5196_);
v___x_5198_ = lean_apply_4(v_f_5181_, v_b_5185_, v_key_5196_, v_val_5197_, lean_box(0));
v___y_5193_ = v___x_5198_;
goto v___jp_5192_;
}
case 1:
{
lean_object* v_node_5199_; lean_object* v___x_5200_; 
v_node_5199_ = lean_ctor_get(v___x_5195_, 0);
lean_inc_ref(v_f_5181_);
v___x_5200_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5181_, v_node_5199_, v_b_5185_);
v___y_5193_ = v___x_5200_;
goto v___jp_5192_;
}
default: 
{
v_val_5188_ = v_b_5185_;
goto v___jp_5187_;
}
}
}
else
{
lean_dec_ref(v_f_5181_);
return v_b_5185_;
}
v___jp_5187_:
{
size_t v___x_5189_; size_t v___x_5190_; 
v___x_5189_ = ((size_t)1ULL);
v___x_5190_ = lean_usize_add(v_i_5183_, v___x_5189_);
v_i_5183_ = v___x_5190_;
v_b_5185_ = v_val_5188_;
goto _start;
}
v___jp_5192_:
{
v_val_5188_ = v___y_5193_;
goto v___jp_5187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_5201_, lean_object* v_as_5202_, lean_object* v_i_5203_, lean_object* v_stop_5204_, lean_object* v_b_5205_, lean_object* v___y_5206_){
_start:
{
size_t v_i_boxed_5207_; size_t v_stop_boxed_5208_; lean_object* v_res_5209_; 
v_i_boxed_5207_ = lean_unbox_usize(v_i_5203_);
lean_dec(v_i_5203_);
v_stop_boxed_5208_ = lean_unbox_usize(v_stop_5204_);
lean_dec(v_stop_5204_);
v_res_5209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5201_, v_as_5202_, v_i_boxed_5207_, v_stop_boxed_5208_, v_b_5205_);
lean_dec_ref(v_as_5202_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg___boxed(lean_object* v_f_5210_, lean_object* v_x_5211_, lean_object* v_x_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v_res_5214_; 
v_res_5214_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5210_, v_x_5211_, v_x_5212_);
lean_dec_ref(v_x_5211_);
return v_res_5214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5215_, lean_object* v_ngen_5216_, lean_object* v_env_5217_, lean_object* v_d_5218_, lean_object* v_act_5219_){
_start:
{
lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v_mainModule_5224_; lean_object* v___x_5225_; lean_object* v_map_u2082_5226_; lean_object* v___f_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v___x_5221_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5216_);
v___x_5222_ = lean_st_mk_ref(v___x_5221_);
v___x_5223_ = l_Lean_Environment_header(v_env_5217_);
v_mainModule_5224_ = lean_ctor_get(v___x_5223_, 0);
lean_inc(v_mainModule_5224_);
lean_dec_ref(v___x_5223_);
lean_inc_ref(v_env_5217_);
v___x_5225_ = l_Lean_Environment_constants(v_env_5217_);
v_map_u2082_5226_ = lean_ctor_get(v___x_5225_, 1);
lean_inc_ref(v_map_u2082_5226_);
lean_dec_ref(v___x_5225_);
v___f_5227_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0___boxed), 10, 6);
lean_closure_set(v___f_5227_, 0, v_cctx_5215_);
lean_closure_set(v___f_5227_, 1, v_env_5217_);
lean_closure_set(v___f_5227_, 2, v_mainModule_5224_);
lean_closure_set(v___f_5227_, 3, v_d_5218_);
lean_closure_set(v___f_5227_, 4, v___x_5222_);
lean_closure_set(v___f_5227_, 5, v_act_5219_);
v___x_5228_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1);
v___x_5229_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v___f_5227_, v_map_u2082_5226_, v___x_5228_);
lean_dec_ref(v_map_u2082_5226_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5230_, lean_object* v_ngen_5231_, lean_object* v_env_5232_, lean_object* v_d_5233_, lean_object* v_act_5234_, lean_object* v_a_5235_){
_start:
{
lean_object* v_res_5236_; 
v_res_5236_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5230_, v_ngen_5231_, v_env_5232_, v_d_5233_, v_act_5234_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5237_, lean_object* v_cctx_5238_, lean_object* v_ngen_5239_, lean_object* v_env_5240_, lean_object* v_d_5241_, lean_object* v_act_5242_){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5238_, v_ngen_5239_, v_env_5240_, v_d_5241_, v_act_5242_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5245_, lean_object* v_cctx_5246_, lean_object* v_ngen_5247_, lean_object* v_env_5248_, lean_object* v_d_5249_, lean_object* v_act_5250_, lean_object* v_a_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5245_, v_cctx_5246_, v_ngen_5247_, v_env_5248_, v_d_5249_, v_act_5250_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_map_5253_, lean_object* v_f_5254_, lean_object* v_init_5255_){
_start:
{
lean_object* v___x_5257_; 
v___x_5257_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5254_, v_map_5253_, v_init_5255_);
return v___x_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_map_5258_, lean_object* v_f_5259_, lean_object* v_init_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_map_5258_, v_f_5259_, v_init_5260_);
lean_dec_ref(v_map_5258_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03c3_5263_, lean_object* v_00_u03b2_5264_, lean_object* v_map_5265_, lean_object* v_f_5266_, lean_object* v_init_5267_){
_start:
{
lean_object* v___x_5269_; 
v___x_5269_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5266_, v_map_5265_, v_init_5267_);
return v___x_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03c3_5270_, lean_object* v_00_u03b2_5271_, lean_object* v_map_5272_, lean_object* v_f_5273_, lean_object* v_init_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03c3_5270_, v_00_u03b2_5271_, v_map_5272_, v_f_5273_, v_init_5274_);
lean_dec_ref(v_map_5272_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0(lean_object* v_00_u03c3_5277_, lean_object* v_00_u03b1_5278_, lean_object* v_00_u03b2_5279_, lean_object* v_f_5280_, lean_object* v_x_5281_, lean_object* v_x_5282_){
_start:
{
lean_object* v___x_5284_; 
v___x_5284_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5280_, v_x_5281_, v_x_5282_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___boxed(lean_object* v_00_u03c3_5285_, lean_object* v_00_u03b1_5286_, lean_object* v_00_u03b2_5287_, lean_object* v_f_5288_, lean_object* v_x_5289_, lean_object* v_x_5290_, lean_object* v___y_5291_){
_start:
{
lean_object* v_res_5292_; 
v_res_5292_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0(v_00_u03c3_5285_, v_00_u03b1_5286_, v_00_u03b2_5287_, v_f_5288_, v_x_5289_, v_x_5290_);
lean_dec_ref(v_x_5289_);
return v_res_5292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5293_, lean_object* v_00_u03b2_5294_, lean_object* v_00_u03c3_5295_, lean_object* v_f_5296_, lean_object* v_as_5297_, size_t v_i_5298_, size_t v_stop_5299_, lean_object* v_b_5300_){
_start:
{
lean_object* v___x_5302_; 
v___x_5302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5296_, v_as_5297_, v_i_5298_, v_stop_5299_, v_b_5300_);
return v___x_5302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5303_, lean_object* v_00_u03b2_5304_, lean_object* v_00_u03c3_5305_, lean_object* v_f_5306_, lean_object* v_as_5307_, lean_object* v_i_5308_, lean_object* v_stop_5309_, lean_object* v_b_5310_, lean_object* v___y_5311_){
_start:
{
size_t v_i_boxed_5312_; size_t v_stop_boxed_5313_; lean_object* v_res_5314_; 
v_i_boxed_5312_ = lean_unbox_usize(v_i_5308_);
lean_dec(v_i_5308_);
v_stop_boxed_5313_ = lean_unbox_usize(v_stop_5309_);
lean_dec(v_stop_5309_);
v_res_5314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1(v_00_u03b1_5303_, v_00_u03b2_5304_, v_00_u03c3_5305_, v_f_5306_, v_as_5307_, v_i_boxed_5312_, v_stop_boxed_5313_, v_b_5310_);
lean_dec_ref(v_as_5307_);
return v_res_5314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_5315_, lean_object* v_00_u03b1_5316_, lean_object* v_00_u03b2_5317_, lean_object* v_f_5318_, lean_object* v_keys_5319_, lean_object* v_vals_5320_, lean_object* v_heq_5321_, lean_object* v_i_5322_, lean_object* v_acc_5323_){
_start:
{
lean_object* v___x_5325_; 
v___x_5325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(v_f_5318_, v_keys_5319_, v_vals_5320_, v_i_5322_, v_acc_5323_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_5326_, lean_object* v_00_u03b1_5327_, lean_object* v_00_u03b2_5328_, lean_object* v_f_5329_, lean_object* v_keys_5330_, lean_object* v_vals_5331_, lean_object* v_heq_5332_, lean_object* v_i_5333_, lean_object* v_acc_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2(v_00_u03c3_5326_, v_00_u03b1_5327_, v_00_u03b2_5328_, v_f_5329_, v_keys_5330_, v_vals_5331_, v_heq_5332_, v_i_5333_, v_acc_5334_);
lean_dec_ref(v_vals_5331_);
lean_dec_ref(v_keys_5330_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5337_, lean_object* v_x_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_){
_start:
{
if (lean_obj_tag(v_x_5338_) == 0)
{
lean_object* v___x_5344_; 
v___x_5344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5344_, 0, v_x_5337_);
return v___x_5344_;
}
else
{
lean_object* v_head_5345_; lean_object* v_tail_5346_; lean_object* v___x_5347_; 
v_head_5345_ = lean_ctor_get(v_x_5338_, 0);
lean_inc(v_head_5345_);
v_tail_5346_ = lean_ctor_get(v_x_5338_, 1);
lean_inc(v_tail_5346_);
lean_dec_ref(v_x_5338_);
v___x_5347_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5337_, v_head_5345_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_);
if (lean_obj_tag(v___x_5347_) == 0)
{
lean_object* v_a_5348_; 
v_a_5348_ = lean_ctor_get(v___x_5347_, 0);
lean_inc(v_a_5348_);
lean_dec_ref(v___x_5347_);
v_x_5337_ = v_a_5348_;
v_x_5338_ = v_tail_5346_;
goto _start;
}
else
{
lean_dec(v_tail_5346_);
return v___x_5347_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5350_, lean_object* v_x_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
lean_object* v_res_5357_; 
v_res_5357_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5350_, v_x_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
return v_res_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5358_, lean_object* v_keys_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_){
_start:
{
lean_object* v___x_5365_; 
v___x_5365_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5358_, v_keys_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_);
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5366_, lean_object* v_keys_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5366_, v_keys_5367_, v_a_5368_, v_a_5369_, v_a_5370_, v_a_5371_);
lean_dec(v_a_5371_);
lean_dec_ref(v_a_5370_);
lean_dec(v_a_5369_);
lean_dec_ref(v_a_5368_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5374_, lean_object* v_t_5375_, lean_object* v_keys_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v___x_5382_; 
v___x_5382_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5375_, v_keys_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5383_, lean_object* v_t_5384_, lean_object* v_keys_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5383_, v_t_5384_, v_keys_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_);
lean_dec(v_a_5389_);
lean_dec_ref(v_a_5388_);
lean_dec(v_a_5387_);
lean_dec_ref(v_a_5386_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5392_, lean_object* v_x_5393_, lean_object* v_x_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
lean_object* v___x_5400_; 
v___x_5400_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5393_, v_x_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_);
return v___x_5400_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5401_, lean_object* v_x_5402_, lean_object* v_x_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_){
_start:
{
lean_object* v_res_5409_; 
v_res_5409_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5401_, v_x_5402_, v_x_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_);
lean_dec(v___y_5407_);
lean_dec_ref(v___y_5406_);
lean_dec(v___y_5405_);
lean_dec_ref(v___y_5404_);
return v_res_5409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5410_, size_t v_sz_5411_, size_t v_i_5412_, lean_object* v_b_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_){
_start:
{
uint8_t v___x_5420_; 
v___x_5420_ = lean_usize_dec_lt(v_i_5412_, v_sz_5411_);
if (v___x_5420_ == 0)
{
lean_object* v___x_5421_; 
v___x_5421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5421_, 0, v_b_5413_);
return v___x_5421_;
}
else
{
lean_object* v_a_5422_; lean_object* v___x_5423_; 
v_a_5422_ = lean_array_uget_borrowed(v_as_5410_, v_i_5412_);
v___x_5423_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5422_, v_b_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5436_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5426_ = v___x_5423_;
v_isShared_5427_ = v_isSharedCheck_5436_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5436_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
if (lean_obj_tag(v_a_5424_) == 0)
{
lean_object* v_a_5428_; lean_object* v___x_5430_; 
v_a_5428_ = lean_ctor_get(v_a_5424_, 0);
lean_inc(v_a_5428_);
lean_dec_ref(v_a_5424_);
if (v_isShared_5427_ == 0)
{
lean_ctor_set(v___x_5426_, 0, v_a_5428_);
v___x_5430_ = v___x_5426_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_a_5428_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
else
{
lean_object* v_a_5432_; size_t v___x_5433_; size_t v___x_5434_; 
lean_del_object(v___x_5426_);
v_a_5432_ = lean_ctor_get(v_a_5424_, 0);
lean_inc(v_a_5432_);
lean_dec_ref(v_a_5424_);
v___x_5433_ = ((size_t)1ULL);
v___x_5434_ = lean_usize_add(v_i_5412_, v___x_5433_);
v_i_5412_ = v___x_5434_;
v_b_5413_ = v_a_5432_;
goto _start;
}
}
}
else
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5444_; 
v_a_5437_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5439_ = v___x_5423_;
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5423_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_){
_start:
{
lean_object* v___x_5452_; uint8_t v___x_5453_; 
v___x_5452_ = lean_unsigned_to_nat(0u);
v___x_5453_ = lean_nat_dec_eq(v_next_5445_, v___x_5452_);
if (v___x_5453_ == 0)
{
lean_object* v___x_5454_; 
v___x_5454_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5445_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; lean_object* v_snd_5456_; lean_object* v_fst_5457_; lean_object* v_fst_5458_; lean_object* v_snd_5459_; lean_object* v___x_5460_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_a_5455_);
lean_dec_ref(v___x_5454_);
v_snd_5456_ = lean_ctor_get(v_a_5455_, 1);
lean_inc(v_snd_5456_);
v_fst_5457_ = lean_ctor_get(v_a_5455_, 0);
lean_inc(v_fst_5457_);
lean_dec(v_a_5455_);
v_fst_5458_ = lean_ctor_get(v_snd_5456_, 0);
lean_inc(v_fst_5458_);
v_snd_5459_ = lean_ctor_get(v_snd_5456_, 1);
lean_inc(v_snd_5459_);
lean_dec(v_snd_5456_);
v___x_5460_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5458_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v_a_5461_; lean_object* v_buckets_5462_; lean_object* v___x_5463_; size_t v_sz_5464_; size_t v___x_5465_; lean_object* v___x_5466_; 
v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
lean_inc(v_a_5461_);
lean_dec_ref(v___x_5460_);
v_buckets_5462_ = lean_ctor_get(v_snd_5459_, 1);
v___x_5463_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v_sz_5464_ = lean_array_size(v_buckets_5462_);
v___x_5465_ = ((size_t)0ULL);
v___x_5466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5462_, v_sz_5464_, v___x_5465_, v___x_5463_, v_a_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v_a_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5480_; 
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5480_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5480_ == 0)
{
v___x_5469_ = v___x_5466_;
v_isShared_5470_ = v_isSharedCheck_5480_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_a_5467_);
lean_dec(v___x_5466_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5480_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5478_; 
v___x_5471_ = lean_st_ref_take(v_a_5446_);
v___x_5472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5472_, 0, v___x_5463_);
lean_ctor_set(v___x_5472_, 1, v_fst_5458_);
lean_ctor_set(v___x_5472_, 2, v_snd_5459_);
lean_ctor_set(v___x_5472_, 3, v___x_5463_);
v___x_5473_ = lean_array_set(v___x_5471_, v_next_5445_, v___x_5472_);
v___x_5474_ = lean_st_ref_set(v_a_5446_, v___x_5473_);
v___x_5475_ = l_Array_append___redArg(v_fst_5457_, v_a_5461_);
lean_dec(v_a_5461_);
v___x_5476_ = l_Array_append___redArg(v___x_5475_, v_a_5467_);
lean_dec(v_a_5467_);
if (v_isShared_5470_ == 0)
{
lean_ctor_set(v___x_5469_, 0, v___x_5476_);
v___x_5478_ = v___x_5469_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v___x_5476_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
}
else
{
lean_dec(v_a_5461_);
lean_dec(v_snd_5459_);
lean_dec(v_fst_5458_);
lean_dec(v_fst_5457_);
return v___x_5466_;
}
}
else
{
lean_dec(v_snd_5459_);
lean_dec(v_fst_5458_);
lean_dec(v_fst_5457_);
return v___x_5460_;
}
}
else
{
lean_object* v_a_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5488_; 
v_a_5481_ = lean_ctor_get(v___x_5454_, 0);
v_isSharedCheck_5488_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5488_ == 0)
{
v___x_5483_ = v___x_5454_;
v_isShared_5484_ = v_isSharedCheck_5488_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_a_5481_);
lean_dec(v___x_5454_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5488_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5486_; 
if (v_isShared_5484_ == 0)
{
v___x_5486_ = v___x_5483_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_a_5481_);
v___x_5486_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
return v___x_5486_;
}
}
}
}
else
{
lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5489_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5490_, 0, v___x_5489_);
return v___x_5490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_){
_start:
{
if (lean_obj_tag(v_a_5491_) == 0)
{
lean_object* v___x_5499_; lean_object* v___x_5500_; 
v___x_5499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5499_, 0, v_a_5492_);
v___x_5500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5500_, 0, v___x_5499_);
return v___x_5500_;
}
else
{
lean_object* v_value_5501_; lean_object* v_tail_5502_; lean_object* v___x_5503_; 
v_value_5501_ = lean_ctor_get(v_a_5491_, 1);
v_tail_5502_ = lean_ctor_get(v_a_5491_, 2);
v___x_5503_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5501_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_);
if (lean_obj_tag(v___x_5503_) == 0)
{
lean_object* v_a_5504_; lean_object* v___x_5505_; 
v_a_5504_ = lean_ctor_get(v___x_5503_, 0);
lean_inc(v_a_5504_);
lean_dec_ref(v___x_5503_);
v___x_5505_ = l_Array_append___redArg(v_a_5492_, v_a_5504_);
lean_dec(v_a_5504_);
v_a_5491_ = v_tail_5502_;
v_a_5492_ = v___x_5505_;
goto _start;
}
else
{
lean_object* v_a_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5514_; 
lean_dec_ref(v_a_5492_);
v_a_5507_ = lean_ctor_get(v___x_5503_, 0);
v_isSharedCheck_5514_ = !lean_is_exclusive(v___x_5503_);
if (v_isSharedCheck_5514_ == 0)
{
v___x_5509_ = v___x_5503_;
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_a_5507_);
lean_dec(v___x_5503_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5512_; 
if (v_isShared_5510_ == 0)
{
v___x_5512_ = v___x_5509_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_a_5507_);
v___x_5512_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
return v___x_5512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_){
_start:
{
lean_object* v_res_5523_; 
v_res_5523_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5515_, v_a_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec(v_a_5515_);
return v_res_5523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5524_, lean_object* v_sz_5525_, lean_object* v_i_5526_, lean_object* v_b_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_){
_start:
{
size_t v_sz_boxed_5534_; size_t v_i_boxed_5535_; lean_object* v_res_5536_; 
v_sz_boxed_5534_ = lean_unbox_usize(v_sz_5525_);
lean_dec(v_sz_5525_);
v_i_boxed_5535_ = lean_unbox_usize(v_i_5526_);
lean_dec(v_i_5526_);
v_res_5536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5524_, v_sz_boxed_5534_, v_i_boxed_5535_, v_b_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
lean_dec(v___y_5532_);
lean_dec_ref(v___y_5531_);
lean_dec(v___y_5530_);
lean_dec_ref(v___y_5529_);
lean_dec(v___y_5528_);
lean_dec_ref(v_as_5524_);
return v_res_5536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_){
_start:
{
lean_object* v_res_5544_; 
v_res_5544_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5537_, v_a_5538_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_);
lean_dec(v_a_5542_);
lean_dec_ref(v_a_5541_);
lean_dec(v_a_5540_);
lean_dec_ref(v_a_5539_);
lean_dec(v_a_5538_);
lean_dec(v_next_5537_);
return v_res_5544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5545_, lean_object* v_next_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_){
_start:
{
lean_object* v___x_5553_; 
v___x_5553_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_);
return v___x_5553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5554_, lean_object* v_next_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_){
_start:
{
lean_object* v_res_5562_; 
v_res_5562_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5554_, v_next_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_);
lean_dec(v_a_5560_);
lean_dec_ref(v_a_5559_);
lean_dec(v_a_5558_);
lean_dec_ref(v_a_5557_);
lean_dec(v_a_5556_);
lean_dec(v_next_5555_);
return v_res_5562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_){
_start:
{
lean_object* v___x_5572_; 
v___x_5572_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5564_, v_a_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
return v___x_5572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_){
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5573_, v_a_5574_, v_a_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_);
lean_dec(v___y_5580_);
lean_dec_ref(v___y_5579_);
lean_dec(v___y_5578_);
lean_dec_ref(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec(v_a_5574_);
return v_res_5582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5583_, lean_object* v_as_5584_, size_t v_sz_5585_, size_t v_i_5586_, lean_object* v_b_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_){
_start:
{
lean_object* v___x_5594_; 
v___x_5594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5584_, v_sz_5585_, v_i_5586_, v_b_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_);
return v___x_5594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5595_, lean_object* v_as_5596_, lean_object* v_sz_5597_, lean_object* v_i_5598_, lean_object* v_b_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_){
_start:
{
size_t v_sz_boxed_5606_; size_t v_i_boxed_5607_; lean_object* v_res_5608_; 
v_sz_boxed_5606_ = lean_unbox_usize(v_sz_5597_);
lean_dec(v_sz_5597_);
v_i_boxed_5607_ = lean_unbox_usize(v_i_5598_);
lean_dec(v_i_5598_);
v_res_5608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5595_, v_as_5596_, v_sz_boxed_5606_, v_i_boxed_5607_, v_b_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec_ref(v_as_5596_);
return v_res_5608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5609_, lean_object* v_rest_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_){
_start:
{
lean_object* v___x_5617_; uint8_t v___x_5618_; 
v___x_5617_ = lean_unsigned_to_nat(0u);
v___x_5618_ = lean_nat_dec_eq(v_next_5609_, v___x_5617_);
if (v___x_5618_ == 0)
{
lean_object* v___x_5619_; 
v___x_5619_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5609_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_);
if (lean_obj_tag(v___x_5619_) == 0)
{
lean_object* v_a_5620_; lean_object* v_snd_5621_; 
v_a_5620_ = lean_ctor_get(v___x_5619_, 0);
lean_inc(v_a_5620_);
lean_dec_ref(v___x_5619_);
v_snd_5621_ = lean_ctor_get(v_a_5620_, 1);
lean_inc(v_snd_5621_);
lean_dec(v_a_5620_);
if (lean_obj_tag(v_rest_5610_) == 0)
{
lean_object* v___x_5622_; 
lean_dec(v_snd_5621_);
v___x_5622_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5609_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_);
lean_dec(v_next_5609_);
return v___x_5622_;
}
else
{
lean_object* v_fst_5623_; lean_object* v_snd_5624_; lean_object* v_head_5625_; lean_object* v_tail_5626_; lean_object* v___x_5627_; uint8_t v___x_5628_; 
lean_dec(v_next_5609_);
v_fst_5623_ = lean_ctor_get(v_snd_5621_, 0);
lean_inc(v_fst_5623_);
v_snd_5624_ = lean_ctor_get(v_snd_5621_, 1);
lean_inc(v_snd_5624_);
lean_dec(v_snd_5621_);
v_head_5625_ = lean_ctor_get(v_rest_5610_, 0);
v_tail_5626_ = lean_ctor_get(v_rest_5610_, 1);
v___x_5627_ = lean_box(3);
v___x_5628_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5625_, v___x_5627_);
if (v___x_5628_ == 0)
{
lean_object* v___x_5629_; 
lean_dec(v_fst_5623_);
v___x_5629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5624_, v_head_5625_, v___x_5617_);
lean_dec(v_snd_5624_);
v_next_5609_ = v___x_5629_;
v_rest_5610_ = v_tail_5626_;
goto _start;
}
else
{
lean_dec(v_snd_5624_);
v_next_5609_ = v_fst_5623_;
v_rest_5610_ = v_tail_5626_;
goto _start;
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec(v_next_5609_);
v_a_5632_ = lean_ctor_get(v___x_5619_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5619_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5619_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5619_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
else
{
lean_object* v___x_5640_; lean_object* v___x_5641_; 
lean_dec(v_next_5609_);
v___x_5640_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5640_);
return v___x_5641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5642_, lean_object* v_rest_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_){
_start:
{
lean_object* v_res_5650_; 
v_res_5650_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5642_, v_rest_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_);
lean_dec(v_a_5648_);
lean_dec_ref(v_a_5647_);
lean_dec(v_a_5646_);
lean_dec_ref(v_a_5645_);
lean_dec(v_a_5644_);
lean_dec(v_rest_5643_);
return v_res_5650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5651_, lean_object* v_next_5652_, lean_object* v_rest_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_){
_start:
{
lean_object* v___x_5660_; 
v___x_5660_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5652_, v_rest_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_);
return v___x_5660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5661_, lean_object* v_next_5662_, lean_object* v_rest_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_){
_start:
{
lean_object* v_res_5670_; 
v_res_5670_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5661_, v_next_5662_, v_rest_5663_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_);
lean_dec(v_a_5668_);
lean_dec_ref(v_a_5667_);
lean_dec(v_a_5666_);
lean_dec_ref(v_a_5665_);
lean_dec(v_a_5664_);
lean_dec(v_rest_5663_);
return v_res_5670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5671_, lean_object* v_path_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_){
_start:
{
if (lean_obj_tag(v_path_5672_) == 0)
{
lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; 
v___x_5678_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5678_);
lean_ctor_set(v___x_5679_, 1, v_t_5671_);
v___x_5680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5680_, 0, v___x_5679_);
return v___x_5680_;
}
else
{
lean_object* v_head_5681_; lean_object* v_tail_5682_; lean_object* v_roots_5683_; lean_object* v___x_5684_; lean_object* v_idx_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; 
v_head_5681_ = lean_ctor_get(v_path_5672_, 0);
lean_inc(v_head_5681_);
v_tail_5682_ = lean_ctor_get(v_path_5672_, 1);
lean_inc(v_tail_5682_);
lean_dec_ref(v_path_5672_);
v_roots_5683_ = lean_ctor_get(v_t_5671_, 1);
v___x_5684_ = lean_unsigned_to_nat(0u);
v_idx_5685_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5683_, v_head_5681_, v___x_5684_);
lean_dec(v_head_5681_);
v___x_5686_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5686_, 0, lean_box(0));
lean_closure_set(v___x_5686_, 1, v_idx_5685_);
lean_closure_set(v___x_5686_, 2, v_tail_5682_);
v___x_5687_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5671_, v___x_5686_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_);
return v___x_5687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5688_, lean_object* v_path_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_){
_start:
{
lean_object* v_res_5695_; 
v_res_5695_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5688_, v_path_5689_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_);
lean_dec(v_a_5693_);
lean_dec_ref(v_a_5692_);
lean_dec(v_a_5691_);
lean_dec_ref(v_a_5690_);
return v_res_5695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5696_, lean_object* v_t_5697_, lean_object* v_path_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_){
_start:
{
lean_object* v___x_5704_; 
v___x_5704_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5697_, v_path_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
return v___x_5704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5705_, lean_object* v_t_5706_, lean_object* v_path_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_){
_start:
{
lean_object* v_res_5713_; 
v_res_5713_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5705_, v_t_5706_, v_path_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_);
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5714_, lean_object* v_b_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_){
_start:
{
if (lean_obj_tag(v_as_x27_5714_) == 0)
{
lean_object* v___x_5721_; 
v___x_5721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5721_, 0, v_b_5715_);
return v___x_5721_;
}
else
{
lean_object* v_head_5722_; lean_object* v_tail_5723_; lean_object* v_fst_5724_; lean_object* v_snd_5725_; lean_object* v___x_5726_; 
v_head_5722_ = lean_ctor_get(v_as_x27_5714_, 0);
lean_inc(v_head_5722_);
v_tail_5723_ = lean_ctor_get(v_as_x27_5714_, 1);
lean_inc(v_tail_5723_);
lean_dec_ref(v_as_x27_5714_);
v_fst_5724_ = lean_ctor_get(v_b_5715_, 0);
lean_inc(v_fst_5724_);
v_snd_5725_ = lean_ctor_get(v_b_5715_, 1);
lean_inc(v_snd_5725_);
lean_dec_ref(v_b_5715_);
v___x_5726_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5725_, v_head_5722_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_);
if (lean_obj_tag(v___x_5726_) == 0)
{
lean_object* v_a_5727_; lean_object* v_fst_5728_; lean_object* v_snd_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5738_; 
v_a_5727_ = lean_ctor_get(v___x_5726_, 0);
lean_inc(v_a_5727_);
lean_dec_ref(v___x_5726_);
v_fst_5728_ = lean_ctor_get(v_a_5727_, 0);
v_snd_5729_ = lean_ctor_get(v_a_5727_, 1);
v_isSharedCheck_5738_ = !lean_is_exclusive(v_a_5727_);
if (v_isSharedCheck_5738_ == 0)
{
v___x_5731_ = v_a_5727_;
v_isShared_5732_ = v_isSharedCheck_5738_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_snd_5729_);
lean_inc(v_fst_5728_);
lean_dec(v_a_5727_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5738_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5733_; lean_object* v___x_5735_; 
v___x_5733_ = l_Array_append___redArg(v_fst_5724_, v_fst_5728_);
lean_dec(v_fst_5728_);
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 0, v___x_5733_);
v___x_5735_ = v___x_5731_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v___x_5733_);
lean_ctor_set(v_reuseFailAlloc_5737_, 1, v_snd_5729_);
v___x_5735_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
v_as_x27_5714_ = v_tail_5723_;
v_b_5715_ = v___x_5735_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5724_);
lean_dec(v_tail_5723_);
return v___x_5726_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5739_, lean_object* v_b_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v_res_5746_; 
v_res_5746_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5739_, v_b_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_);
lean_dec(v___y_5744_);
lean_dec_ref(v___y_5743_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5747_, lean_object* v_keys_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_){
_start:
{
lean_object* v_allExtracted_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
v_allExtracted_5754_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5755_, 0, v_allExtracted_5754_);
lean_ctor_set(v___x_5755_, 1, v_t_5747_);
v___x_5756_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5748_, v___x_5755_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_);
if (lean_obj_tag(v___x_5756_) == 0)
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5773_; 
v_a_5757_ = lean_ctor_get(v___x_5756_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v___x_5756_);
if (v_isSharedCheck_5773_ == 0)
{
v___x_5759_ = v___x_5756_;
v_isShared_5760_ = v_isSharedCheck_5773_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5756_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5773_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v_fst_5761_; lean_object* v_snd_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5772_; 
v_fst_5761_ = lean_ctor_get(v_a_5757_, 0);
v_snd_5762_ = lean_ctor_get(v_a_5757_, 1);
v_isSharedCheck_5772_ = !lean_is_exclusive(v_a_5757_);
if (v_isSharedCheck_5772_ == 0)
{
v___x_5764_ = v_a_5757_;
v_isShared_5765_ = v_isSharedCheck_5772_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_snd_5762_);
lean_inc(v_fst_5761_);
lean_dec(v_a_5757_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5772_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5767_; 
if (v_isShared_5765_ == 0)
{
v___x_5767_ = v___x_5764_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_fst_5761_);
lean_ctor_set(v_reuseFailAlloc_5771_, 1, v_snd_5762_);
v___x_5767_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
lean_object* v___x_5769_; 
if (v_isShared_5760_ == 0)
{
lean_ctor_set(v___x_5759_, 0, v___x_5767_);
v___x_5769_ = v___x_5759_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v___x_5767_);
v___x_5769_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
return v___x_5769_;
}
}
}
}
}
else
{
return v___x_5756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5774_, lean_object* v_keys_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_){
_start:
{
lean_object* v_res_5781_; 
v_res_5781_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5774_, v_keys_5775_, v_a_5776_, v_a_5777_, v_a_5778_, v_a_5779_);
lean_dec(v_a_5779_);
lean_dec_ref(v_a_5778_);
lean_dec(v_a_5777_);
lean_dec_ref(v_a_5776_);
return v_res_5781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5782_, lean_object* v_t_5783_, lean_object* v_keys_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_){
_start:
{
lean_object* v___x_5790_; 
v___x_5790_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5783_, v_keys_5784_, v_a_5785_, v_a_5786_, v_a_5787_, v_a_5788_);
return v___x_5790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5791_, lean_object* v_t_5792_, lean_object* v_keys_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_){
_start:
{
lean_object* v_res_5799_; 
v_res_5799_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5791_, v_t_5792_, v_keys_5793_, v_a_5794_, v_a_5795_, v_a_5796_, v_a_5797_);
lean_dec(v_a_5797_);
lean_dec_ref(v_a_5796_);
lean_dec(v_a_5795_);
lean_dec_ref(v_a_5794_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5800_, lean_object* v_as_5801_, lean_object* v_as_x27_5802_, lean_object* v_b_5803_, lean_object* v_a_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_){
_start:
{
lean_object* v___x_5810_; 
v___x_5810_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5802_, v_b_5803_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
return v___x_5810_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5811_, lean_object* v_as_5812_, lean_object* v_as_x27_5813_, lean_object* v_b_5814_, lean_object* v_a_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_){
_start:
{
lean_object* v_res_5821_; 
v_res_5821_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5811_, v_as_5812_, v_as_x27_5813_, v_b_5814_, v_a_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_);
lean_dec(v___y_5819_);
lean_dec_ref(v___y_5818_);
lean_dec(v___y_5817_);
lean_dec_ref(v___y_5816_);
lean_dec(v_as_5812_);
return v_res_5821_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; 
v___x_5823_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5824_ = l_Lean_stringToMessageData(v___x_5823_);
return v___x_5824_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5826_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5827_ = l_Lean_stringToMessageData(v___x_5826_);
return v___x_5827_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___x_5829_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5830_ = l_Lean_stringToMessageData(v___x_5829_);
return v___x_5830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5831_, lean_object* v_inst_5832_, lean_object* v_inst_5833_, lean_object* v_inst_5834_, lean_object* v_f_5835_){
_start:
{
lean_object* v_module_5836_; lean_object* v_const_5837_; lean_object* v_exception_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; 
v_module_5836_ = lean_ctor_get(v_f_5835_, 0);
lean_inc(v_module_5836_);
v_const_5837_ = lean_ctor_get(v_f_5835_, 1);
lean_inc(v_const_5837_);
v_exception_5838_ = lean_ctor_get(v_f_5835_, 2);
lean_inc_ref(v_exception_5838_);
lean_dec_ref(v_f_5835_);
v___x_5839_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5840_ = l_Lean_MessageData_ofName(v_const_5837_);
v___x_5841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5841_, 0, v___x_5839_);
lean_ctor_set(v___x_5841_, 1, v___x_5840_);
v___x_5842_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5843_, 0, v___x_5841_);
lean_ctor_set(v___x_5843_, 1, v___x_5842_);
v___x_5844_ = l_Lean_MessageData_ofName(v_module_5836_);
v___x_5845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5845_, 0, v___x_5843_);
lean_ctor_set(v___x_5845_, 1, v___x_5844_);
v___x_5846_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5847_, 0, v___x_5845_);
lean_ctor_set(v___x_5847_, 1, v___x_5846_);
v___x_5848_ = l_Lean_Exception_toMessageData(v_exception_5838_);
v___x_5849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5849_, 0, v___x_5847_);
lean_ctor_set(v___x_5849_, 1, v___x_5848_);
v___x_5850_ = l_Lean_logError___redArg(v_inst_5831_, v_inst_5832_, v_inst_5833_, v_inst_5834_, v___x_5849_);
return v___x_5850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5851_, lean_object* v_inst_5852_, lean_object* v_inst_5853_, lean_object* v_inst_5854_, lean_object* v_inst_5855_, lean_object* v_f_5856_){
_start:
{
lean_object* v___x_5857_; 
v___x_5857_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5852_, v_inst_5853_, v_inst_5854_, v_inst_5855_, v_f_5856_);
return v___x_5857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_toApplicative_5858_, lean_object* v_tasks_5859_, lean_object* v_t_5860_){
_start:
{
lean_object* v_toPure_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; 
v_toPure_5861_ = lean_ctor_get(v_toApplicative_5858_, 1);
lean_inc(v_toPure_5861_);
lean_dec_ref(v_toApplicative_5858_);
v___x_5862_ = lean_array_push(v_tasks_5859_, v_t_5860_);
v___x_5863_ = lean_apply_2(v_toPure_5861_, lean_box(0), v___x_5862_);
return v___x_5863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5864_, lean_object* v_inst_5865_, lean_object* v_cctx_5866_, lean_object* v_env_5867_, lean_object* v_act_5868_, lean_object* v_constantsPerTask_5869_, lean_object* v_n_5870_, lean_object* v_ngen_5871_, lean_object* v_tasks_5872_, lean_object* v_start_5873_, lean_object* v_cnt_5874_, lean_object* v_idx_5875_){
_start:
{
lean_object* v___x_5876_; lean_object* v_moduleData_5877_; lean_object* v___x_5878_; uint8_t v___x_5879_; 
v___x_5876_ = l_Lean_Environment_header(v_env_5867_);
v_moduleData_5877_ = lean_ctor_get(v___x_5876_, 6);
lean_inc_ref(v_moduleData_5877_);
lean_dec_ref(v___x_5876_);
v___x_5878_ = lean_array_get_size(v_moduleData_5877_);
v___x_5879_ = lean_nat_dec_lt(v_idx_5875_, v___x_5878_);
if (v___x_5879_ == 0)
{
uint8_t v___x_5880_; 
lean_dec_ref(v_moduleData_5877_);
lean_dec(v_idx_5875_);
lean_dec(v_cnt_5874_);
lean_dec(v_constantsPerTask_5869_);
v___x_5880_ = lean_nat_dec_lt(v_start_5873_, v_n_5870_);
if (v___x_5880_ == 0)
{
lean_object* v_toApplicative_5881_; lean_object* v_toPure_5882_; lean_object* v___x_5883_; 
lean_dec(v_start_5873_);
lean_dec_ref(v_ngen_5871_);
lean_dec(v_n_5870_);
lean_dec_ref(v_act_5868_);
lean_dec_ref(v_env_5867_);
lean_dec_ref(v_cctx_5866_);
lean_dec(v_inst_5865_);
v_toApplicative_5881_ = lean_ctor_get(v_inst_5864_, 0);
lean_inc_ref(v_toApplicative_5881_);
lean_dec_ref(v_inst_5864_);
v_toPure_5882_ = lean_ctor_get(v_toApplicative_5881_, 1);
lean_inc(v_toPure_5882_);
lean_dec_ref(v_toApplicative_5881_);
v___x_5883_ = lean_apply_2(v_toPure_5882_, lean_box(0), v_tasks_5872_);
return v___x_5883_;
}
else
{
lean_object* v_namePrefix_5884_; lean_object* v_idx_5885_; lean_object* v___x_5887_; uint8_t v_isShared_5888_; uint8_t v_isSharedCheck_5902_; 
v_namePrefix_5884_ = lean_ctor_get(v_ngen_5871_, 0);
v_idx_5885_ = lean_ctor_get(v_ngen_5871_, 1);
v_isSharedCheck_5902_ = !lean_is_exclusive(v_ngen_5871_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5887_ = v_ngen_5871_;
v_isShared_5888_ = v_isSharedCheck_5902_;
goto v_resetjp_5886_;
}
else
{
lean_inc(v_idx_5885_);
lean_inc(v_namePrefix_5884_);
lean_dec(v_ngen_5871_);
v___x_5887_ = lean_box(0);
v_isShared_5888_ = v_isSharedCheck_5902_;
goto v_resetjp_5886_;
}
v_resetjp_5886_:
{
lean_object* v_toApplicative_5889_; lean_object* v_toBind_5890_; lean_object* v___f_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5895_; 
v_toApplicative_5889_ = lean_ctor_get(v_inst_5864_, 0);
lean_inc_ref(v_toApplicative_5889_);
v_toBind_5890_ = lean_ctor_get(v_inst_5864_, 1);
lean_inc(v_toBind_5890_);
lean_dec_ref(v_inst_5864_);
v___f_5891_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5891_, 0, v_toApplicative_5889_);
lean_closure_set(v___f_5891_, 1, v_tasks_5872_);
v___x_5892_ = l_Lean_Name_num___override(v_namePrefix_5884_, v_idx_5885_);
v___x_5893_ = lean_unsigned_to_nat(1u);
if (v_isShared_5888_ == 0)
{
lean_ctor_set(v___x_5887_, 1, v___x_5893_);
lean_ctor_set(v___x_5887_, 0, v___x_5892_);
v___x_5895_ = v___x_5887_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v___x_5892_);
lean_ctor_set(v_reuseFailAlloc_5901_, 1, v___x_5893_);
v___x_5895_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; 
v___x_5896_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5896_, 0, lean_box(0));
lean_closure_set(v___x_5896_, 1, v_cctx_5866_);
lean_closure_set(v___x_5896_, 2, v___x_5895_);
lean_closure_set(v___x_5896_, 3, v_env_5867_);
lean_closure_set(v___x_5896_, 4, v_act_5868_);
lean_closure_set(v___x_5896_, 5, v_start_5873_);
lean_closure_set(v___x_5896_, 6, v_n_5870_);
v___x_5897_ = lean_unsigned_to_nat(0u);
v___x_5898_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5898_, 0, lean_box(0));
lean_closure_set(v___x_5898_, 1, v___x_5896_);
lean_closure_set(v___x_5898_, 2, v___x_5897_);
v___x_5899_ = lean_apply_2(v_inst_5865_, lean_box(0), v___x_5898_);
v___x_5900_ = lean_apply_4(v_toBind_5890_, lean_box(0), lean_box(0), v___x_5899_, v___f_5891_);
return v___x_5900_;
}
}
}
}
else
{
lean_object* v_mdata_5903_; lean_object* v_constants_5904_; lean_object* v___x_5905_; lean_object* v_cnt_5906_; uint8_t v___x_5907_; 
v_mdata_5903_ = lean_array_fget(v_moduleData_5877_, v_idx_5875_);
lean_dec_ref(v_moduleData_5877_);
v_constants_5904_ = lean_ctor_get(v_mdata_5903_, 2);
lean_inc_ref(v_constants_5904_);
lean_dec(v_mdata_5903_);
v___x_5905_ = lean_array_get_size(v_constants_5904_);
lean_dec_ref(v_constants_5904_);
v_cnt_5906_ = lean_nat_add(v_cnt_5874_, v___x_5905_);
lean_dec(v_cnt_5874_);
v___x_5907_ = lean_nat_dec_lt(v_constantsPerTask_5869_, v_cnt_5906_);
if (v___x_5907_ == 0)
{
lean_object* v___x_5908_; lean_object* v___x_5909_; 
v___x_5908_ = lean_unsigned_to_nat(1u);
v___x_5909_ = lean_nat_add(v_idx_5875_, v___x_5908_);
lean_dec(v_idx_5875_);
v_cnt_5874_ = v_cnt_5906_;
v_idx_5875_ = v___x_5909_;
goto _start;
}
else
{
lean_object* v_namePrefix_5911_; lean_object* v_idx_5912_; lean_object* v___x_5914_; uint8_t v_isShared_5915_; uint8_t v_isSharedCheck_5931_; 
lean_dec(v_cnt_5906_);
v_namePrefix_5911_ = lean_ctor_get(v_ngen_5871_, 0);
v_idx_5912_ = lean_ctor_get(v_ngen_5871_, 1);
v_isSharedCheck_5931_ = !lean_is_exclusive(v_ngen_5871_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5914_ = v_ngen_5871_;
v_isShared_5915_ = v_isSharedCheck_5931_;
goto v_resetjp_5913_;
}
else
{
lean_inc(v_idx_5912_);
lean_inc(v_namePrefix_5911_);
lean_dec(v_ngen_5871_);
v___x_5914_ = lean_box(0);
v_isShared_5915_ = v_isSharedCheck_5931_;
goto v_resetjp_5913_;
}
v_resetjp_5913_:
{
lean_object* v_toBind_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5920_; 
v_toBind_5916_ = lean_ctor_get(v_inst_5864_, 1);
lean_inc(v_toBind_5916_);
lean_inc(v_idx_5912_);
lean_inc(v_namePrefix_5911_);
v___x_5917_ = l_Lean_Name_num___override(v_namePrefix_5911_, v_idx_5912_);
v___x_5918_ = lean_unsigned_to_nat(1u);
if (v_isShared_5915_ == 0)
{
lean_ctor_set(v___x_5914_, 1, v___x_5918_);
lean_ctor_set(v___x_5914_, 0, v___x_5917_);
v___x_5920_ = v___x_5914_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v___x_5917_);
lean_ctor_set(v_reuseFailAlloc_5930_, 1, v___x_5918_);
v___x_5920_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___f_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5921_ = lean_nat_add(v_idx_5912_, v___x_5918_);
lean_dec(v_idx_5912_);
v___x_5922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5922_, 0, v_namePrefix_5911_);
lean_ctor_set(v___x_5922_, 1, v___x_5921_);
v___x_5923_ = lean_nat_add(v_idx_5875_, v___x_5918_);
lean_dec(v_idx_5875_);
lean_inc(v___x_5923_);
lean_inc_ref(v_act_5868_);
lean_inc_ref(v_env_5867_);
lean_inc_ref(v_cctx_5866_);
lean_inc(v_inst_5865_);
v___f_5924_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5924_, 0, v_tasks_5872_);
lean_closure_set(v___f_5924_, 1, v_inst_5864_);
lean_closure_set(v___f_5924_, 2, v_inst_5865_);
lean_closure_set(v___f_5924_, 3, v_cctx_5866_);
lean_closure_set(v___f_5924_, 4, v_env_5867_);
lean_closure_set(v___f_5924_, 5, v_act_5868_);
lean_closure_set(v___f_5924_, 6, v_constantsPerTask_5869_);
lean_closure_set(v___f_5924_, 7, v_n_5870_);
lean_closure_set(v___f_5924_, 8, v___x_5922_);
lean_closure_set(v___f_5924_, 9, v___x_5923_);
v___x_5925_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5925_, 0, lean_box(0));
lean_closure_set(v___x_5925_, 1, v_cctx_5866_);
lean_closure_set(v___x_5925_, 2, v___x_5920_);
lean_closure_set(v___x_5925_, 3, v_env_5867_);
lean_closure_set(v___x_5925_, 4, v_act_5868_);
lean_closure_set(v___x_5925_, 5, v_start_5873_);
lean_closure_set(v___x_5925_, 6, v___x_5923_);
v___x_5926_ = lean_unsigned_to_nat(0u);
v___x_5927_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5927_, 0, lean_box(0));
lean_closure_set(v___x_5927_, 1, v___x_5925_);
lean_closure_set(v___x_5927_, 2, v___x_5926_);
v___x_5928_ = lean_apply_2(v_inst_5865_, lean_box(0), v___x_5927_);
v___x_5929_ = lean_apply_4(v_toBind_5916_, lean_box(0), lean_box(0), v___x_5928_, v___f_5924_);
return v___x_5929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5932_, lean_object* v_inst_5933_, lean_object* v_inst_5934_, lean_object* v_cctx_5935_, lean_object* v_env_5936_, lean_object* v_act_5937_, lean_object* v_constantsPerTask_5938_, lean_object* v_n_5939_, lean_object* v___x_5940_, lean_object* v___x_5941_, lean_object* v_t_5942_){
_start:
{
lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; 
v___x_5943_ = lean_array_push(v_tasks_5932_, v_t_5942_);
v___x_5944_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5941_);
v___x_5945_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5933_, v_inst_5934_, v_cctx_5935_, v_env_5936_, v_act_5937_, v_constantsPerTask_5938_, v_n_5939_, v___x_5940_, v___x_5943_, v___x_5941_, v___x_5944_, v___x_5941_);
return v___x_5945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5946_, lean_object* v_00_u03b1_5947_, lean_object* v_inst_5948_, lean_object* v_inst_5949_, lean_object* v_cctx_5950_, lean_object* v_env_5951_, lean_object* v_act_5952_, lean_object* v_constantsPerTask_5953_, lean_object* v_n_5954_, lean_object* v_ngen_5955_, lean_object* v_tasks_5956_, lean_object* v_start_5957_, lean_object* v_cnt_5958_, lean_object* v_idx_5959_){
_start:
{
lean_object* v___x_5960_; 
v___x_5960_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5948_, v_inst_5949_, v_cctx_5950_, v_env_5951_, v_act_5952_, v_constantsPerTask_5953_, v_n_5954_, v_ngen_5955_, v_tasks_5956_, v_start_5957_, v_cnt_5958_, v_idx_5959_);
return v___x_5960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5961_, lean_object* v_h__1_5962_){
_start:
{
lean_object* v_fst_5963_; lean_object* v_snd_5964_; lean_object* v___x_5965_; 
v_fst_5963_ = lean_ctor_get(v_x_5961_, 0);
lean_inc(v_fst_5963_);
v_snd_5964_ = lean_ctor_get(v_x_5961_, 1);
lean_inc(v_snd_5964_);
lean_dec_ref(v_x_5961_);
v___x_5965_ = lean_apply_2(v_h__1_5962_, v_fst_5963_, v_snd_5964_);
return v___x_5965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5966_, lean_object* v_x_5967_, lean_object* v_h__1_5968_){
_start:
{
lean_object* v_fst_5969_; lean_object* v_snd_5970_; lean_object* v___x_5971_; 
v_fst_5969_ = lean_ctor_get(v_x_5967_, 0);
lean_inc(v_fst_5969_);
v_snd_5970_ = lean_ctor_get(v_x_5967_, 1);
lean_inc(v_snd_5970_);
lean_dec_ref(v_x_5967_);
v___x_5971_ = lean_apply_2(v_h__1_5968_, v_fst_5969_, v_snd_5970_);
return v___x_5971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5972_, lean_object* v_inst_5973_, lean_object* v_inst_5974_, lean_object* v_inst_5975_, lean_object* v_x_5976_, lean_object* v___y_5977_){
_start:
{
lean_object* v___x_5978_; 
v___x_5978_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5972_, v_inst_5973_, v_inst_5974_, v_inst_5975_, v___y_5977_);
return v___x_5978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5979_, lean_object* v_toPure_5980_, lean_object* v_____r_5981_){
_start:
{
lean_object* v_tree_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; 
v_tree_5982_ = lean_ctor_get(v_r_5979_, 0);
lean_inc_ref(v_tree_5982_);
lean_dec_ref(v_r_5979_);
v___x_5983_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5982_);
v___x_5984_ = lean_apply_2(v_toPure_5980_, lean_box(0), v___x_5983_);
return v___x_5984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5985_, lean_object* v___x_5986_, lean_object* v_toPure_5987_, lean_object* v_toBind_5988_, lean_object* v_inst_5989_, lean_object* v___f_5990_, lean_object* v_tasks_5991_){
_start:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v_r_5997_; lean_object* v_errors_5998_; lean_object* v___f_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; uint8_t v___x_6002_; 
v___x_5992_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_5985_);
v___x_5993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5985_);
lean_ctor_set(v___x_5993_, 1, v___x_5992_);
v___x_5994_ = lean_mk_empty_array_with_capacity(v___x_5985_);
lean_inc_ref(v___x_5994_);
v___x_5995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5993_);
lean_ctor_set(v___x_5995_, 1, v___x_5994_);
v___x_5996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
lean_ctor_set(v___x_5996_, 1, v___x_5994_);
v_r_5997_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5986_, v___x_5996_, v_tasks_5991_);
v_errors_5998_ = lean_ctor_get(v_r_5997_, 1);
lean_inc_ref(v_errors_5998_);
lean_inc(v_toPure_5987_);
v___f_5999_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5999_, 0, v_r_5997_);
lean_closure_set(v___f_5999_, 1, v_toPure_5987_);
v___x_6000_ = lean_array_get_size(v_errors_5998_);
v___x_6001_ = lean_box(0);
v___x_6002_ = lean_nat_dec_lt(v___x_5985_, v___x_6000_);
lean_dec(v___x_5985_);
if (v___x_6002_ == 0)
{
lean_object* v___x_6003_; lean_object* v___x_6004_; 
lean_dec_ref(v_errors_5998_);
lean_dec(v___f_5990_);
lean_dec_ref(v_inst_5989_);
v___x_6003_ = lean_apply_2(v_toPure_5987_, lean_box(0), v___x_6001_);
v___x_6004_ = lean_apply_4(v_toBind_5988_, lean_box(0), lean_box(0), v___x_6003_, v___f_5999_);
return v___x_6004_;
}
else
{
uint8_t v___x_6005_; 
v___x_6005_ = lean_nat_dec_le(v___x_6000_, v___x_6000_);
if (v___x_6005_ == 0)
{
if (v___x_6002_ == 0)
{
lean_object* v___x_6006_; lean_object* v___x_6007_; 
lean_dec_ref(v_errors_5998_);
lean_dec(v___f_5990_);
lean_dec_ref(v_inst_5989_);
v___x_6006_ = lean_apply_2(v_toPure_5987_, lean_box(0), v___x_6001_);
v___x_6007_ = lean_apply_4(v_toBind_5988_, lean_box(0), lean_box(0), v___x_6006_, v___f_5999_);
return v___x_6007_;
}
else
{
size_t v___x_6008_; size_t v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; 
lean_dec(v_toPure_5987_);
v___x_6008_ = ((size_t)0ULL);
v___x_6009_ = lean_usize_of_nat(v___x_6000_);
v___x_6010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5989_, v___f_5990_, v_errors_5998_, v___x_6008_, v___x_6009_, v___x_6001_);
v___x_6011_ = lean_apply_4(v_toBind_5988_, lean_box(0), lean_box(0), v___x_6010_, v___f_5999_);
return v___x_6011_;
}
}
else
{
size_t v___x_6012_; size_t v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; 
lean_dec(v_toPure_5987_);
v___x_6012_ = ((size_t)0ULL);
v___x_6013_ = lean_usize_of_nat(v___x_6000_);
v___x_6014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5989_, v___f_5990_, v_errors_5998_, v___x_6012_, v___x_6013_, v___x_6001_);
v___x_6015_ = lean_apply_4(v_toBind_5988_, lean_box(0), lean_box(0), v___x_6014_, v___f_5999_);
return v___x_6015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_6018_, lean_object* v_inst_6019_, lean_object* v_inst_6020_, lean_object* v_inst_6021_, lean_object* v_inst_6022_, lean_object* v_cctx_6023_, lean_object* v_ngen_6024_, lean_object* v_env_6025_, lean_object* v_act_6026_, lean_object* v_constantsPerTask_6027_){
_start:
{
lean_object* v___x_6028_; lean_object* v_moduleData_6029_; lean_object* v_toApplicative_6030_; lean_object* v_toBind_6031_; lean_object* v_n_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v_toPure_6036_; lean_object* v___f_6037_; lean_object* v___x_6038_; lean_object* v___f_6039_; lean_object* v___x_6040_; 
v___x_6028_ = l_Lean_Environment_header(v_env_6025_);
v_moduleData_6029_ = lean_ctor_get(v___x_6028_, 6);
lean_inc_ref(v_moduleData_6029_);
lean_dec_ref(v___x_6028_);
v_toApplicative_6030_ = lean_ctor_get(v_inst_6018_, 0);
v_toBind_6031_ = lean_ctor_get(v_inst_6018_, 1);
lean_inc_n(v_toBind_6031_, 2);
v_n_6032_ = lean_array_get_size(v_moduleData_6029_);
lean_dec_ref(v_moduleData_6029_);
v___x_6033_ = lean_unsigned_to_nat(0u);
v___x_6034_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_6018_, 2);
v___x_6035_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_6018_, v_inst_6022_, v_cctx_6023_, v_env_6025_, v_act_6026_, v_constantsPerTask_6027_, v_n_6032_, v_ngen_6024_, v___x_6034_, v___x_6033_, v___x_6033_, v___x_6033_);
v_toPure_6036_ = lean_ctor_get(v_toApplicative_6030_, 1);
lean_inc(v_toPure_6036_);
v___f_6037_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_6037_, 0, v_inst_6018_);
lean_closure_set(v___f_6037_, 1, v_inst_6019_);
lean_closure_set(v___f_6037_, 2, v_inst_6020_);
lean_closure_set(v___f_6037_, 3, v_inst_6021_);
v___x_6038_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
v___f_6039_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_6039_, 0, v___x_6033_);
lean_closure_set(v___f_6039_, 1, v___x_6038_);
lean_closure_set(v___f_6039_, 2, v_toPure_6036_);
lean_closure_set(v___f_6039_, 3, v_toBind_6031_);
lean_closure_set(v___f_6039_, 4, v_inst_6018_);
lean_closure_set(v___f_6039_, 5, v___f_6037_);
v___x_6040_ = lean_apply_4(v_toBind_6031_, lean_box(0), lean_box(0), v___x_6035_, v___f_6039_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_6041_, lean_object* v_00_u03b1_6042_, lean_object* v_inst_6043_, lean_object* v_inst_6044_, lean_object* v_inst_6045_, lean_object* v_inst_6046_, lean_object* v_inst_6047_, lean_object* v_cctx_6048_, lean_object* v_ngen_6049_, lean_object* v_env_6050_, lean_object* v_act_6051_, lean_object* v_constantsPerTask_6052_){
_start:
{
lean_object* v___x_6053_; 
v___x_6053_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_6043_, v_inst_6044_, v_inst_6045_, v_inst_6046_, v_inst_6047_, v_cctx_6048_, v_ngen_6049_, v_env_6050_, v_act_6051_, v_constantsPerTask_6052_);
return v___x_6053_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; 
v___x_6054_ = lean_box(0);
v___x_6055_ = lean_unsigned_to_nat(16u);
v___x_6056_ = lean_mk_array(v___x_6055_, v___x_6054_);
return v___x_6056_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; 
v___x_6057_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_6058_ = lean_unsigned_to_nat(0u);
v___x_6059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
lean_ctor_set(v___x_6059_, 1, v___x_6057_);
return v___x_6059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_6060_){
_start:
{
lean_object* v_fileName_6061_; lean_object* v_fileMap_6062_; lean_object* v_options_6063_; lean_object* v_maxRecDepth_6064_; lean_object* v_ref_6065_; lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6080_; 
v_fileName_6061_ = lean_ctor_get(v_ctx_6060_, 0);
v_fileMap_6062_ = lean_ctor_get(v_ctx_6060_, 1);
v_options_6063_ = lean_ctor_get(v_ctx_6060_, 2);
v_maxRecDepth_6064_ = lean_ctor_get(v_ctx_6060_, 4);
v_ref_6065_ = lean_ctor_get(v_ctx_6060_, 5);
v_isSharedCheck_6080_ = !lean_is_exclusive(v_ctx_6060_);
if (v_isSharedCheck_6080_ == 0)
{
lean_object* v_unused_6081_; lean_object* v_unused_6082_; lean_object* v_unused_6083_; lean_object* v_unused_6084_; lean_object* v_unused_6085_; lean_object* v_unused_6086_; lean_object* v_unused_6087_; lean_object* v_unused_6088_; lean_object* v_unused_6089_; 
v_unused_6081_ = lean_ctor_get(v_ctx_6060_, 13);
lean_dec(v_unused_6081_);
v_unused_6082_ = lean_ctor_get(v_ctx_6060_, 12);
lean_dec(v_unused_6082_);
v_unused_6083_ = lean_ctor_get(v_ctx_6060_, 11);
lean_dec(v_unused_6083_);
v_unused_6084_ = lean_ctor_get(v_ctx_6060_, 10);
lean_dec(v_unused_6084_);
v_unused_6085_ = lean_ctor_get(v_ctx_6060_, 9);
lean_dec(v_unused_6085_);
v_unused_6086_ = lean_ctor_get(v_ctx_6060_, 8);
lean_dec(v_unused_6086_);
v_unused_6087_ = lean_ctor_get(v_ctx_6060_, 7);
lean_dec(v_unused_6087_);
v_unused_6088_ = lean_ctor_get(v_ctx_6060_, 6);
lean_dec(v_unused_6088_);
v_unused_6089_ = lean_ctor_get(v_ctx_6060_, 3);
lean_dec(v_unused_6089_);
v___x_6067_ = v_ctx_6060_;
v_isShared_6068_ = v_isSharedCheck_6080_;
goto v_resetjp_6066_;
}
else
{
lean_inc(v_ref_6065_);
lean_inc(v_maxRecDepth_6064_);
lean_inc(v_options_6063_);
lean_inc(v_fileMap_6062_);
lean_inc(v_fileName_6061_);
lean_dec(v_ctx_6060_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6080_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; uint8_t v___x_6073_; lean_object* v___x_6074_; uint8_t v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6078_; 
v___x_6069_ = lean_unsigned_to_nat(0u);
v___x_6070_ = lean_box(0);
v___x_6071_ = lean_box(0);
v___x_6072_ = l_Lean_firstFrontendMacroScope;
v___x_6073_ = l_Lean_getDiag(v_options_6063_);
v___x_6074_ = lean_box(0);
v___x_6075_ = 0;
v___x_6076_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
if (v_isShared_6068_ == 0)
{
lean_ctor_set(v___x_6067_, 13, v___x_6076_);
lean_ctor_set(v___x_6067_, 12, v___x_6074_);
lean_ctor_set(v___x_6067_, 11, v___x_6072_);
lean_ctor_set(v___x_6067_, 10, v___x_6070_);
lean_ctor_set(v___x_6067_, 9, v___x_6069_);
lean_ctor_set(v___x_6067_, 8, v___x_6069_);
lean_ctor_set(v___x_6067_, 7, v___x_6071_);
lean_ctor_set(v___x_6067_, 6, v___x_6070_);
lean_ctor_set(v___x_6067_, 3, v___x_6069_);
v___x_6078_ = v___x_6067_;
goto v_reusejp_6077_;
}
else
{
lean_object* v_reuseFailAlloc_6079_; 
v_reuseFailAlloc_6079_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_6079_, 0, v_fileName_6061_);
lean_ctor_set(v_reuseFailAlloc_6079_, 1, v_fileMap_6062_);
lean_ctor_set(v_reuseFailAlloc_6079_, 2, v_options_6063_);
lean_ctor_set(v_reuseFailAlloc_6079_, 3, v___x_6069_);
lean_ctor_set(v_reuseFailAlloc_6079_, 4, v_maxRecDepth_6064_);
lean_ctor_set(v_reuseFailAlloc_6079_, 5, v_ref_6065_);
lean_ctor_set(v_reuseFailAlloc_6079_, 6, v___x_6070_);
lean_ctor_set(v_reuseFailAlloc_6079_, 7, v___x_6071_);
lean_ctor_set(v_reuseFailAlloc_6079_, 8, v___x_6069_);
lean_ctor_set(v_reuseFailAlloc_6079_, 9, v___x_6069_);
lean_ctor_set(v_reuseFailAlloc_6079_, 10, v___x_6070_);
lean_ctor_set(v_reuseFailAlloc_6079_, 11, v___x_6072_);
lean_ctor_set(v_reuseFailAlloc_6079_, 12, v___x_6074_);
lean_ctor_set(v_reuseFailAlloc_6079_, 13, v___x_6076_);
v___x_6078_ = v_reuseFailAlloc_6079_;
goto v_reusejp_6077_;
}
v_reusejp_6077_:
{
lean_ctor_set_uint8(v___x_6078_, sizeof(void*)*14, v___x_6073_);
lean_ctor_set_uint8(v___x_6078_, sizeof(void*)*14 + 1, v___x_6075_);
return v___x_6078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_6090_, lean_object* v_opts_6091_, lean_object* v_act_6092_, lean_object* v_decl_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_){
_start:
{
lean_object* v___x_6099_; lean_object* v___x_6100_; 
lean_inc(v___y_6097_);
lean_inc_ref(v___y_6096_);
lean_inc(v___y_6095_);
lean_inc_ref(v___y_6094_);
v___x_6099_ = lean_apply_4(v_act_6092_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_);
v___x_6100_ = l_Lean_profileitIOUnsafe___redArg(v_category_6090_, v_opts_6091_, v___x_6099_, v_decl_6093_);
return v___x_6100_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_6101_, lean_object* v_opts_6102_, lean_object* v_act_6103_, lean_object* v_decl_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_){
_start:
{
lean_object* v_res_6110_; 
v_res_6110_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6101_, v_opts_6102_, v_act_6103_, v_decl_6104_, v___y_6105_, v___y_6106_, v___y_6107_, v___y_6108_);
lean_dec(v___y_6108_);
lean_dec_ref(v___y_6107_);
lean_dec(v___y_6106_);
lean_dec_ref(v___y_6105_);
lean_dec_ref(v_opts_6102_);
lean_dec_ref(v_category_6101_);
return v_res_6110_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_6111_, lean_object* v_category_6112_, lean_object* v_opts_6113_, lean_object* v_act_6114_, lean_object* v_decl_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_){
_start:
{
lean_object* v___x_6121_; 
v___x_6121_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6112_, v_opts_6113_, v_act_6114_, v_decl_6115_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_);
return v___x_6121_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6122_, lean_object* v_category_6123_, lean_object* v_opts_6124_, lean_object* v_act_6125_, lean_object* v_decl_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_){
_start:
{
lean_object* v_res_6132_; 
v_res_6132_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6122_, v_category_6123_, v_opts_6124_, v_act_6125_, v_decl_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_);
lean_dec(v___y_6130_);
lean_dec_ref(v___y_6129_);
lean_dec(v___y_6128_);
lean_dec_ref(v___y_6127_);
lean_dec_ref(v_opts_6124_);
lean_dec_ref(v_category_6123_);
return v_res_6132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6133_, lean_object* v_env_6134_, lean_object* v_act_6135_, lean_object* v_constantsPerTask_6136_, lean_object* v_n_6137_, lean_object* v_ngen_6138_, lean_object* v_tasks_6139_, lean_object* v_start_6140_, lean_object* v_cnt_6141_, lean_object* v_idx_6142_){
_start:
{
lean_object* v___x_6144_; lean_object* v_moduleData_6145_; lean_object* v___x_6146_; uint8_t v___x_6147_; 
v___x_6144_ = l_Lean_Environment_header(v_env_6134_);
v_moduleData_6145_ = lean_ctor_get(v___x_6144_, 6);
lean_inc_ref(v_moduleData_6145_);
lean_dec_ref(v___x_6144_);
v___x_6146_ = lean_array_get_size(v_moduleData_6145_);
v___x_6147_ = lean_nat_dec_lt(v_idx_6142_, v___x_6146_);
if (v___x_6147_ == 0)
{
uint8_t v___x_6148_; 
lean_dec_ref(v_moduleData_6145_);
lean_dec(v_idx_6142_);
lean_dec(v_cnt_6141_);
v___x_6148_ = lean_nat_dec_lt(v_start_6140_, v_n_6137_);
if (v___x_6148_ == 0)
{
lean_object* v___x_6149_; 
lean_dec(v_start_6140_);
lean_dec_ref(v_ngen_6138_);
lean_dec(v_n_6137_);
lean_dec_ref(v_act_6135_);
lean_dec_ref(v_env_6134_);
lean_dec_ref(v_cctx_6133_);
v___x_6149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6149_, 0, v_tasks_6139_);
return v___x_6149_;
}
else
{
lean_object* v_namePrefix_6150_; lean_object* v_idx_6151_; lean_object* v___x_6153_; uint8_t v_isShared_6154_; uint8_t v_isSharedCheck_6165_; 
v_namePrefix_6150_ = lean_ctor_get(v_ngen_6138_, 0);
v_idx_6151_ = lean_ctor_get(v_ngen_6138_, 1);
v_isSharedCheck_6165_ = !lean_is_exclusive(v_ngen_6138_);
if (v_isSharedCheck_6165_ == 0)
{
v___x_6153_ = v_ngen_6138_;
v_isShared_6154_ = v_isSharedCheck_6165_;
goto v_resetjp_6152_;
}
else
{
lean_inc(v_idx_6151_);
lean_inc(v_namePrefix_6150_);
lean_dec(v_ngen_6138_);
v___x_6153_ = lean_box(0);
v_isShared_6154_ = v_isSharedCheck_6165_;
goto v_resetjp_6152_;
}
v_resetjp_6152_:
{
lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6158_; 
v___x_6155_ = l_Lean_Name_num___override(v_namePrefix_6150_, v_idx_6151_);
v___x_6156_ = lean_unsigned_to_nat(1u);
if (v_isShared_6154_ == 0)
{
lean_ctor_set(v___x_6153_, 1, v___x_6156_);
lean_ctor_set(v___x_6153_, 0, v___x_6155_);
v___x_6158_ = v___x_6153_;
goto v_reusejp_6157_;
}
else
{
lean_object* v_reuseFailAlloc_6164_; 
v_reuseFailAlloc_6164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6164_, 0, v___x_6155_);
lean_ctor_set(v_reuseFailAlloc_6164_, 1, v___x_6156_);
v___x_6158_ = v_reuseFailAlloc_6164_;
goto v_reusejp_6157_;
}
v_reusejp_6157_:
{
lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; 
v___x_6159_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6159_, 0, lean_box(0));
lean_closure_set(v___x_6159_, 1, v_cctx_6133_);
lean_closure_set(v___x_6159_, 2, v___x_6158_);
lean_closure_set(v___x_6159_, 3, v_env_6134_);
lean_closure_set(v___x_6159_, 4, v_act_6135_);
lean_closure_set(v___x_6159_, 5, v_start_6140_);
lean_closure_set(v___x_6159_, 6, v_n_6137_);
v___x_6160_ = lean_unsigned_to_nat(0u);
v___x_6161_ = lean_io_as_task(v___x_6159_, v___x_6160_);
v___x_6162_ = lean_array_push(v_tasks_6139_, v___x_6161_);
v___x_6163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6162_);
return v___x_6163_;
}
}
}
}
else
{
lean_object* v_mdata_6166_; lean_object* v_constants_6167_; lean_object* v___x_6168_; lean_object* v_cnt_6169_; uint8_t v___x_6170_; 
v_mdata_6166_ = lean_array_fget(v_moduleData_6145_, v_idx_6142_);
lean_dec_ref(v_moduleData_6145_);
v_constants_6167_ = lean_ctor_get(v_mdata_6166_, 2);
lean_inc_ref(v_constants_6167_);
lean_dec(v_mdata_6166_);
v___x_6168_ = lean_array_get_size(v_constants_6167_);
lean_dec_ref(v_constants_6167_);
v_cnt_6169_ = lean_nat_add(v_cnt_6141_, v___x_6168_);
lean_dec(v_cnt_6141_);
v___x_6170_ = lean_nat_dec_lt(v_constantsPerTask_6136_, v_cnt_6169_);
if (v___x_6170_ == 0)
{
lean_object* v___x_6171_; lean_object* v___x_6172_; 
v___x_6171_ = lean_unsigned_to_nat(1u);
v___x_6172_ = lean_nat_add(v_idx_6142_, v___x_6171_);
lean_dec(v_idx_6142_);
v_cnt_6141_ = v_cnt_6169_;
v_idx_6142_ = v___x_6172_;
goto _start;
}
else
{
lean_object* v_namePrefix_6174_; lean_object* v_idx_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6192_; 
lean_dec(v_cnt_6169_);
v_namePrefix_6174_ = lean_ctor_get(v_ngen_6138_, 0);
v_idx_6175_ = lean_ctor_get(v_ngen_6138_, 1);
v_isSharedCheck_6192_ = !lean_is_exclusive(v_ngen_6138_);
if (v_isSharedCheck_6192_ == 0)
{
v___x_6177_ = v_ngen_6138_;
v_isShared_6178_ = v_isSharedCheck_6192_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_idx_6175_);
lean_inc(v_namePrefix_6174_);
lean_dec(v_ngen_6138_);
v___x_6177_ = lean_box(0);
v_isShared_6178_ = v_isSharedCheck_6192_;
goto v_resetjp_6176_;
}
v_resetjp_6176_:
{
lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6182_; 
lean_inc(v_idx_6175_);
lean_inc(v_namePrefix_6174_);
v___x_6179_ = l_Lean_Name_num___override(v_namePrefix_6174_, v_idx_6175_);
v___x_6180_ = lean_unsigned_to_nat(1u);
if (v_isShared_6178_ == 0)
{
lean_ctor_set(v___x_6177_, 1, v___x_6180_);
lean_ctor_set(v___x_6177_, 0, v___x_6179_);
v___x_6182_ = v___x_6177_;
goto v_reusejp_6181_;
}
else
{
lean_object* v_reuseFailAlloc_6191_; 
v_reuseFailAlloc_6191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6191_, 0, v___x_6179_);
lean_ctor_set(v_reuseFailAlloc_6191_, 1, v___x_6180_);
v___x_6182_ = v_reuseFailAlloc_6191_;
goto v_reusejp_6181_;
}
v_reusejp_6181_:
{
lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; 
v___x_6183_ = lean_nat_add(v_idx_6142_, v___x_6180_);
lean_dec(v_idx_6142_);
lean_inc_n(v___x_6183_, 2);
lean_inc_ref(v_act_6135_);
lean_inc_ref(v_env_6134_);
lean_inc_ref(v_cctx_6133_);
v___x_6184_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6184_, 0, lean_box(0));
lean_closure_set(v___x_6184_, 1, v_cctx_6133_);
lean_closure_set(v___x_6184_, 2, v___x_6182_);
lean_closure_set(v___x_6184_, 3, v_env_6134_);
lean_closure_set(v___x_6184_, 4, v_act_6135_);
lean_closure_set(v___x_6184_, 5, v_start_6140_);
lean_closure_set(v___x_6184_, 6, v___x_6183_);
v___x_6185_ = lean_unsigned_to_nat(0u);
v___x_6186_ = lean_io_as_task(v___x_6184_, v___x_6185_);
v___x_6187_ = lean_nat_add(v_idx_6175_, v___x_6180_);
lean_dec(v_idx_6175_);
v___x_6188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6188_, 0, v_namePrefix_6174_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
v___x_6189_ = lean_array_push(v_tasks_6139_, v___x_6186_);
v_ngen_6138_ = v___x_6188_;
v_tasks_6139_ = v___x_6189_;
v_start_6140_ = v___x_6183_;
v_cnt_6141_ = v___x_6185_;
v_idx_6142_ = v___x_6183_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6193_, lean_object* v_env_6194_, lean_object* v_act_6195_, lean_object* v_constantsPerTask_6196_, lean_object* v_n_6197_, lean_object* v_ngen_6198_, lean_object* v_tasks_6199_, lean_object* v_start_6200_, lean_object* v_cnt_6201_, lean_object* v_idx_6202_, lean_object* v___y_6203_){
_start:
{
lean_object* v_res_6204_; 
v_res_6204_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6193_, v_env_6194_, v_act_6195_, v_constantsPerTask_6196_, v_n_6197_, v_ngen_6198_, v_tasks_6199_, v_start_6200_, v_cnt_6201_, v_idx_6202_);
lean_dec(v_constantsPerTask_6196_);
return v_res_6204_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v___y_6213_, uint8_t v_suppressElabErrors_6214_, lean_object* v_x_6215_){
_start:
{
if (lean_obj_tag(v_x_6215_) == 1)
{
lean_object* v_pre_6216_; 
v_pre_6216_ = lean_ctor_get(v_x_6215_, 0);
switch(lean_obj_tag(v_pre_6216_))
{
case 1:
{
lean_object* v_pre_6217_; 
v_pre_6217_ = lean_ctor_get(v_pre_6216_, 0);
switch(lean_obj_tag(v_pre_6217_))
{
case 0:
{
lean_object* v_str_6218_; lean_object* v_str_6219_; lean_object* v___x_6220_; uint8_t v___x_6221_; 
v_str_6218_ = lean_ctor_get(v_x_6215_, 1);
v_str_6219_ = lean_ctor_get(v_pre_6216_, 1);
v___x_6220_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6221_ = lean_string_dec_eq(v_str_6219_, v___x_6220_);
if (v___x_6221_ == 0)
{
lean_object* v___x_6222_; uint8_t v___x_6223_; 
v___x_6222_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6223_ = lean_string_dec_eq(v_str_6219_, v___x_6222_);
if (v___x_6223_ == 0)
{
return v___y_6213_;
}
else
{
lean_object* v___x_6224_; uint8_t v___x_6225_; 
v___x_6224_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6225_ = lean_string_dec_eq(v_str_6218_, v___x_6224_);
if (v___x_6225_ == 0)
{
return v___y_6213_;
}
else
{
return v_suppressElabErrors_6214_;
}
}
}
else
{
lean_object* v___x_6226_; uint8_t v___x_6227_; 
v___x_6226_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6227_ = lean_string_dec_eq(v_str_6218_, v___x_6226_);
if (v___x_6227_ == 0)
{
return v___y_6213_;
}
else
{
return v_suppressElabErrors_6214_;
}
}
}
case 1:
{
lean_object* v_pre_6228_; 
v_pre_6228_ = lean_ctor_get(v_pre_6217_, 0);
if (lean_obj_tag(v_pre_6228_) == 0)
{
lean_object* v_str_6229_; lean_object* v_str_6230_; lean_object* v_str_6231_; lean_object* v___x_6232_; uint8_t v___x_6233_; 
v_str_6229_ = lean_ctor_get(v_x_6215_, 1);
v_str_6230_ = lean_ctor_get(v_pre_6216_, 1);
v_str_6231_ = lean_ctor_get(v_pre_6217_, 1);
v___x_6232_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6233_ = lean_string_dec_eq(v_str_6231_, v___x_6232_);
if (v___x_6233_ == 0)
{
return v___y_6213_;
}
else
{
lean_object* v___x_6234_; uint8_t v___x_6235_; 
v___x_6234_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6235_ = lean_string_dec_eq(v_str_6230_, v___x_6234_);
if (v___x_6235_ == 0)
{
return v___y_6213_;
}
else
{
lean_object* v___x_6236_; uint8_t v___x_6237_; 
v___x_6236_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6237_ = lean_string_dec_eq(v_str_6229_, v___x_6236_);
if (v___x_6237_ == 0)
{
return v___y_6213_;
}
else
{
return v_suppressElabErrors_6214_;
}
}
}
}
else
{
return v___y_6213_;
}
}
default: 
{
return v___y_6213_;
}
}
}
case 0:
{
lean_object* v_str_6238_; lean_object* v___x_6239_; uint8_t v___x_6240_; 
v_str_6238_ = lean_ctor_get(v_x_6215_, 1);
v___x_6239_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6240_ = lean_string_dec_eq(v_str_6238_, v___x_6239_);
if (v___x_6240_ == 0)
{
return v___y_6213_;
}
else
{
return v_suppressElabErrors_6214_;
}
}
default: 
{
return v___y_6213_;
}
}
}
else
{
return v___y_6213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v___y_6241_, lean_object* v_suppressElabErrors_6242_, lean_object* v_x_6243_){
_start:
{
uint8_t v___y_8412__boxed_6244_; uint8_t v_suppressElabErrors_boxed_6245_; uint8_t v_res_6246_; lean_object* v_r_6247_; 
v___y_8412__boxed_6244_ = lean_unbox(v___y_6241_);
v_suppressElabErrors_boxed_6245_ = lean_unbox(v_suppressElabErrors_6242_);
v_res_6246_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v___y_8412__boxed_6244_, v_suppressElabErrors_boxed_6245_, v_x_6243_);
lean_dec(v_x_6243_);
v_r_6247_ = lean_box(v_res_6246_);
return v_r_6247_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6249_, lean_object* v_msgData_6250_, uint8_t v_severity_6251_, uint8_t v_isSilent_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_){
_start:
{
lean_object* v___y_6259_; lean_object* v___y_6260_; uint8_t v___y_6261_; lean_object* v___y_6262_; uint8_t v___y_6263_; lean_object* v___y_6264_; lean_object* v___y_6265_; lean_object* v___y_6266_; lean_object* v___y_6267_; lean_object* v___y_6295_; lean_object* v___y_6296_; lean_object* v___y_6297_; uint8_t v___y_6298_; lean_object* v___y_6299_; uint8_t v___y_6300_; uint8_t v___y_6301_; lean_object* v___y_6302_; lean_object* v___y_6320_; lean_object* v___y_6321_; lean_object* v___y_6322_; uint8_t v___y_6323_; uint8_t v___y_6324_; uint8_t v___y_6325_; lean_object* v___y_6326_; lean_object* v___y_6327_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; uint8_t v___y_6334_; lean_object* v___y_6335_; uint8_t v___y_6336_; uint8_t v___y_6337_; uint8_t v___x_6342_; lean_object* v___y_6344_; lean_object* v___y_6345_; lean_object* v___y_6346_; lean_object* v___y_6347_; uint8_t v___y_6348_; uint8_t v___y_6349_; uint8_t v___y_6350_; uint8_t v___y_6352_; uint8_t v___x_6367_; 
v___x_6342_ = 2;
v___x_6367_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6251_, v___x_6342_);
if (v___x_6367_ == 0)
{
v___y_6352_ = v___x_6367_;
goto v___jp_6351_;
}
else
{
uint8_t v___x_6368_; 
lean_inc_ref(v_msgData_6250_);
v___x_6368_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6250_);
v___y_6352_ = v___x_6368_;
goto v___jp_6351_;
}
v___jp_6258_:
{
lean_object* v___x_6268_; lean_object* v_currNamespace_6269_; lean_object* v_openDecls_6270_; lean_object* v_env_6271_; lean_object* v_nextMacroScope_6272_; lean_object* v_ngen_6273_; lean_object* v_auxDeclNGen_6274_; lean_object* v_traceState_6275_; lean_object* v_cache_6276_; lean_object* v_messages_6277_; lean_object* v_infoState_6278_; lean_object* v_snapshotTasks_6279_; lean_object* v___x_6281_; uint8_t v_isShared_6282_; uint8_t v_isSharedCheck_6293_; 
v___x_6268_ = lean_st_ref_take(v___y_6267_);
v_currNamespace_6269_ = lean_ctor_get(v___y_6266_, 6);
v_openDecls_6270_ = lean_ctor_get(v___y_6266_, 7);
v_env_6271_ = lean_ctor_get(v___x_6268_, 0);
v_nextMacroScope_6272_ = lean_ctor_get(v___x_6268_, 1);
v_ngen_6273_ = lean_ctor_get(v___x_6268_, 2);
v_auxDeclNGen_6274_ = lean_ctor_get(v___x_6268_, 3);
v_traceState_6275_ = lean_ctor_get(v___x_6268_, 4);
v_cache_6276_ = lean_ctor_get(v___x_6268_, 5);
v_messages_6277_ = lean_ctor_get(v___x_6268_, 6);
v_infoState_6278_ = lean_ctor_get(v___x_6268_, 7);
v_snapshotTasks_6279_ = lean_ctor_get(v___x_6268_, 8);
v_isSharedCheck_6293_ = !lean_is_exclusive(v___x_6268_);
if (v_isSharedCheck_6293_ == 0)
{
v___x_6281_ = v___x_6268_;
v_isShared_6282_ = v_isSharedCheck_6293_;
goto v_resetjp_6280_;
}
else
{
lean_inc(v_snapshotTasks_6279_);
lean_inc(v_infoState_6278_);
lean_inc(v_messages_6277_);
lean_inc(v_cache_6276_);
lean_inc(v_traceState_6275_);
lean_inc(v_auxDeclNGen_6274_);
lean_inc(v_ngen_6273_);
lean_inc(v_nextMacroScope_6272_);
lean_inc(v_env_6271_);
lean_dec(v___x_6268_);
v___x_6281_ = lean_box(0);
v_isShared_6282_ = v_isSharedCheck_6293_;
goto v_resetjp_6280_;
}
v_resetjp_6280_:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6288_; 
lean_inc(v_openDecls_6270_);
lean_inc(v_currNamespace_6269_);
v___x_6283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6283_, 0, v_currNamespace_6269_);
lean_ctor_set(v___x_6283_, 1, v_openDecls_6270_);
v___x_6284_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6284_, 0, v___x_6283_);
lean_ctor_set(v___x_6284_, 1, v___y_6264_);
lean_inc_ref(v___y_6262_);
lean_inc_ref(v___y_6259_);
v___x_6285_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6285_, 0, v___y_6259_);
lean_ctor_set(v___x_6285_, 1, v___y_6260_);
lean_ctor_set(v___x_6285_, 2, v___y_6265_);
lean_ctor_set(v___x_6285_, 3, v___y_6262_);
lean_ctor_set(v___x_6285_, 4, v___x_6284_);
lean_ctor_set_uint8(v___x_6285_, sizeof(void*)*5, v___y_6261_);
lean_ctor_set_uint8(v___x_6285_, sizeof(void*)*5 + 1, v___y_6263_);
lean_ctor_set_uint8(v___x_6285_, sizeof(void*)*5 + 2, v_isSilent_6252_);
v___x_6286_ = l_Lean_MessageLog_add(v___x_6285_, v_messages_6277_);
if (v_isShared_6282_ == 0)
{
lean_ctor_set(v___x_6281_, 6, v___x_6286_);
v___x_6288_ = v___x_6281_;
goto v_reusejp_6287_;
}
else
{
lean_object* v_reuseFailAlloc_6292_; 
v_reuseFailAlloc_6292_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6292_, 0, v_env_6271_);
lean_ctor_set(v_reuseFailAlloc_6292_, 1, v_nextMacroScope_6272_);
lean_ctor_set(v_reuseFailAlloc_6292_, 2, v_ngen_6273_);
lean_ctor_set(v_reuseFailAlloc_6292_, 3, v_auxDeclNGen_6274_);
lean_ctor_set(v_reuseFailAlloc_6292_, 4, v_traceState_6275_);
lean_ctor_set(v_reuseFailAlloc_6292_, 5, v_cache_6276_);
lean_ctor_set(v_reuseFailAlloc_6292_, 6, v___x_6286_);
lean_ctor_set(v_reuseFailAlloc_6292_, 7, v_infoState_6278_);
lean_ctor_set(v_reuseFailAlloc_6292_, 8, v_snapshotTasks_6279_);
v___x_6288_ = v_reuseFailAlloc_6292_;
goto v_reusejp_6287_;
}
v_reusejp_6287_:
{
lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; 
v___x_6289_ = lean_st_ref_set(v___y_6267_, v___x_6288_);
v___x_6290_ = lean_box(0);
v___x_6291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6291_, 0, v___x_6290_);
return v___x_6291_;
}
}
}
v___jp_6294_:
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v_a_6305_; lean_object* v___x_6307_; uint8_t v_isShared_6308_; uint8_t v_isSharedCheck_6318_; 
v___x_6303_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6250_);
v___x_6304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6303_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_);
v_a_6305_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6318_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6318_ == 0)
{
v___x_6307_ = v___x_6304_;
v_isShared_6308_ = v_isSharedCheck_6318_;
goto v_resetjp_6306_;
}
else
{
lean_inc(v_a_6305_);
lean_dec(v___x_6304_);
v___x_6307_ = lean_box(0);
v_isShared_6308_ = v_isSharedCheck_6318_;
goto v_resetjp_6306_;
}
v_resetjp_6306_:
{
lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; 
lean_inc_ref_n(v___y_6299_, 2);
v___x_6309_ = l_Lean_FileMap_toPosition(v___y_6299_, v___y_6297_);
lean_dec(v___y_6297_);
v___x_6310_ = l_Lean_FileMap_toPosition(v___y_6299_, v___y_6302_);
lean_dec(v___y_6302_);
v___x_6311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6311_, 0, v___x_6310_);
v___x_6312_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6300_ == 0)
{
lean_del_object(v___x_6307_);
lean_dec_ref(v___y_6295_);
v___y_6259_ = v___y_6296_;
v___y_6260_ = v___x_6309_;
v___y_6261_ = v___y_6298_;
v___y_6262_ = v___x_6312_;
v___y_6263_ = v___y_6301_;
v___y_6264_ = v_a_6305_;
v___y_6265_ = v___x_6311_;
v___y_6266_ = v___y_6255_;
v___y_6267_ = v___y_6256_;
goto v___jp_6258_;
}
else
{
uint8_t v___x_6313_; 
lean_inc(v_a_6305_);
v___x_6313_ = l_Lean_MessageData_hasTag(v___y_6295_, v_a_6305_);
if (v___x_6313_ == 0)
{
lean_object* v___x_6314_; lean_object* v___x_6316_; 
lean_dec_ref(v___x_6311_);
lean_dec_ref(v___x_6309_);
lean_dec(v_a_6305_);
v___x_6314_ = lean_box(0);
if (v_isShared_6308_ == 0)
{
lean_ctor_set(v___x_6307_, 0, v___x_6314_);
v___x_6316_ = v___x_6307_;
goto v_reusejp_6315_;
}
else
{
lean_object* v_reuseFailAlloc_6317_; 
v_reuseFailAlloc_6317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6317_, 0, v___x_6314_);
v___x_6316_ = v_reuseFailAlloc_6317_;
goto v_reusejp_6315_;
}
v_reusejp_6315_:
{
return v___x_6316_;
}
}
else
{
lean_del_object(v___x_6307_);
v___y_6259_ = v___y_6296_;
v___y_6260_ = v___x_6309_;
v___y_6261_ = v___y_6298_;
v___y_6262_ = v___x_6312_;
v___y_6263_ = v___y_6301_;
v___y_6264_ = v_a_6305_;
v___y_6265_ = v___x_6311_;
v___y_6266_ = v___y_6255_;
v___y_6267_ = v___y_6256_;
goto v___jp_6258_;
}
}
}
}
v___jp_6319_:
{
lean_object* v___x_6328_; 
v___x_6328_ = l_Lean_Syntax_getTailPos_x3f(v___y_6326_, v___y_6323_);
lean_dec(v___y_6326_);
if (lean_obj_tag(v___x_6328_) == 0)
{
lean_inc(v___y_6327_);
v___y_6295_ = v___y_6320_;
v___y_6296_ = v___y_6321_;
v___y_6297_ = v___y_6327_;
v___y_6298_ = v___y_6323_;
v___y_6299_ = v___y_6322_;
v___y_6300_ = v___y_6324_;
v___y_6301_ = v___y_6325_;
v___y_6302_ = v___y_6327_;
goto v___jp_6294_;
}
else
{
lean_object* v_val_6329_; 
v_val_6329_ = lean_ctor_get(v___x_6328_, 0);
lean_inc(v_val_6329_);
lean_dec_ref(v___x_6328_);
v___y_6295_ = v___y_6320_;
v___y_6296_ = v___y_6321_;
v___y_6297_ = v___y_6327_;
v___y_6298_ = v___y_6323_;
v___y_6299_ = v___y_6322_;
v___y_6300_ = v___y_6324_;
v___y_6301_ = v___y_6325_;
v___y_6302_ = v_val_6329_;
goto v___jp_6294_;
}
}
v___jp_6330_:
{
lean_object* v_ref_6338_; lean_object* v___x_6339_; 
v_ref_6338_ = l_Lean_replaceRef(v_ref_6249_, v___y_6333_);
v___x_6339_ = l_Lean_Syntax_getPos_x3f(v_ref_6338_, v___y_6334_);
if (lean_obj_tag(v___x_6339_) == 0)
{
lean_object* v___x_6340_; 
v___x_6340_ = lean_unsigned_to_nat(0u);
v___y_6320_ = v___y_6331_;
v___y_6321_ = v___y_6332_;
v___y_6322_ = v___y_6335_;
v___y_6323_ = v___y_6334_;
v___y_6324_ = v___y_6336_;
v___y_6325_ = v___y_6337_;
v___y_6326_ = v_ref_6338_;
v___y_6327_ = v___x_6340_;
goto v___jp_6319_;
}
else
{
lean_object* v_val_6341_; 
v_val_6341_ = lean_ctor_get(v___x_6339_, 0);
lean_inc(v_val_6341_);
lean_dec_ref(v___x_6339_);
v___y_6320_ = v___y_6331_;
v___y_6321_ = v___y_6332_;
v___y_6322_ = v___y_6335_;
v___y_6323_ = v___y_6334_;
v___y_6324_ = v___y_6336_;
v___y_6325_ = v___y_6337_;
v___y_6326_ = v_ref_6338_;
v___y_6327_ = v_val_6341_;
goto v___jp_6319_;
}
}
v___jp_6343_:
{
if (v___y_6350_ == 0)
{
v___y_6331_ = v___y_6344_;
v___y_6332_ = v___y_6345_;
v___y_6333_ = v___y_6346_;
v___y_6334_ = v___y_6349_;
v___y_6335_ = v___y_6347_;
v___y_6336_ = v___y_6348_;
v___y_6337_ = v_severity_6251_;
goto v___jp_6330_;
}
else
{
v___y_6331_ = v___y_6344_;
v___y_6332_ = v___y_6345_;
v___y_6333_ = v___y_6346_;
v___y_6334_ = v___y_6349_;
v___y_6335_ = v___y_6347_;
v___y_6336_ = v___y_6348_;
v___y_6337_ = v___x_6342_;
goto v___jp_6330_;
}
}
v___jp_6351_:
{
if (v___y_6352_ == 0)
{
lean_object* v_fileName_6353_; lean_object* v_fileMap_6354_; lean_object* v_options_6355_; lean_object* v_ref_6356_; uint8_t v_suppressElabErrors_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___f_6360_; uint8_t v___x_6361_; uint8_t v___x_6362_; 
v_fileName_6353_ = lean_ctor_get(v___y_6255_, 0);
v_fileMap_6354_ = lean_ctor_get(v___y_6255_, 1);
v_options_6355_ = lean_ctor_get(v___y_6255_, 2);
v_ref_6356_ = lean_ctor_get(v___y_6255_, 5);
v_suppressElabErrors_6357_ = lean_ctor_get_uint8(v___y_6255_, sizeof(void*)*14 + 1);
v___x_6358_ = lean_box(v___y_6352_);
v___x_6359_ = lean_box(v_suppressElabErrors_6357_);
v___f_6360_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6360_, 0, v___x_6358_);
lean_closure_set(v___f_6360_, 1, v___x_6359_);
v___x_6361_ = 1;
v___x_6362_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6251_, v___x_6361_);
if (v___x_6362_ == 0)
{
v___y_6344_ = v___f_6360_;
v___y_6345_ = v_fileName_6353_;
v___y_6346_ = v_ref_6356_;
v___y_6347_ = v_fileMap_6354_;
v___y_6348_ = v_suppressElabErrors_6357_;
v___y_6349_ = v___y_6352_;
v___y_6350_ = v___x_6362_;
goto v___jp_6343_;
}
else
{
lean_object* v___x_6363_; uint8_t v___x_6364_; 
v___x_6363_ = l_Lean_warningAsError;
v___x_6364_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6355_, v___x_6363_);
v___y_6344_ = v___f_6360_;
v___y_6345_ = v_fileName_6353_;
v___y_6346_ = v_ref_6356_;
v___y_6347_ = v_fileMap_6354_;
v___y_6348_ = v_suppressElabErrors_6357_;
v___y_6349_ = v___y_6352_;
v___y_6350_ = v___x_6364_;
goto v___jp_6343_;
}
}
else
{
lean_object* v___x_6365_; lean_object* v___x_6366_; 
lean_dec_ref(v_msgData_6250_);
v___x_6365_ = lean_box(0);
v___x_6366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6366_, 0, v___x_6365_);
return v___x_6366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6369_, lean_object* v_msgData_6370_, lean_object* v_severity_6371_, lean_object* v_isSilent_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_){
_start:
{
uint8_t v_severity_boxed_6378_; uint8_t v_isSilent_boxed_6379_; lean_object* v_res_6380_; 
v_severity_boxed_6378_ = lean_unbox(v_severity_6371_);
v_isSilent_boxed_6379_ = lean_unbox(v_isSilent_6372_);
v_res_6380_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6369_, v_msgData_6370_, v_severity_boxed_6378_, v_isSilent_boxed_6379_, v___y_6373_, v___y_6374_, v___y_6375_, v___y_6376_);
lean_dec(v___y_6376_);
lean_dec_ref(v___y_6375_);
lean_dec(v___y_6374_);
lean_dec_ref(v___y_6373_);
lean_dec(v_ref_6369_);
return v_res_6380_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6381_, uint8_t v_severity_6382_, uint8_t v_isSilent_6383_, lean_object* v___y_6384_, lean_object* v___y_6385_, lean_object* v___y_6386_, lean_object* v___y_6387_){
_start:
{
lean_object* v_ref_6389_; lean_object* v___x_6390_; 
v_ref_6389_ = lean_ctor_get(v___y_6386_, 5);
v___x_6390_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6389_, v_msgData_6381_, v_severity_6382_, v_isSilent_6383_, v___y_6384_, v___y_6385_, v___y_6386_, v___y_6387_);
return v___x_6390_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6391_, lean_object* v_severity_6392_, lean_object* v_isSilent_6393_, lean_object* v___y_6394_, lean_object* v___y_6395_, lean_object* v___y_6396_, lean_object* v___y_6397_, lean_object* v___y_6398_){
_start:
{
uint8_t v_severity_boxed_6399_; uint8_t v_isSilent_boxed_6400_; lean_object* v_res_6401_; 
v_severity_boxed_6399_ = lean_unbox(v_severity_6392_);
v_isSilent_boxed_6400_ = lean_unbox(v_isSilent_6393_);
v_res_6401_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6391_, v_severity_boxed_6399_, v_isSilent_boxed_6400_, v___y_6394_, v___y_6395_, v___y_6396_, v___y_6397_);
lean_dec(v___y_6397_);
lean_dec_ref(v___y_6396_);
lean_dec(v___y_6395_);
lean_dec_ref(v___y_6394_);
return v_res_6401_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6402_, lean_object* v___y_6403_, lean_object* v___y_6404_, lean_object* v___y_6405_, lean_object* v___y_6406_){
_start:
{
uint8_t v___x_6408_; uint8_t v___x_6409_; lean_object* v___x_6410_; 
v___x_6408_ = 2;
v___x_6409_ = 0;
v___x_6410_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6402_, v___x_6408_, v___x_6409_, v___y_6403_, v___y_6404_, v___y_6405_, v___y_6406_);
return v___x_6410_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_){
_start:
{
lean_object* v_res_6417_; 
v_res_6417_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6411_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_);
lean_dec(v___y_6415_);
lean_dec_ref(v___y_6414_);
lean_dec(v___y_6413_);
lean_dec_ref(v___y_6412_);
return v_res_6417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6418_, lean_object* v___y_6419_, lean_object* v___y_6420_, lean_object* v___y_6421_, lean_object* v___y_6422_){
_start:
{
lean_object* v_module_6424_; lean_object* v_const_6425_; lean_object* v_exception_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; lean_object* v___x_6430_; lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; 
v_module_6424_ = lean_ctor_get(v_f_6418_, 0);
lean_inc(v_module_6424_);
v_const_6425_ = lean_ctor_get(v_f_6418_, 1);
lean_inc(v_const_6425_);
v_exception_6426_ = lean_ctor_get(v_f_6418_, 2);
lean_inc_ref(v_exception_6426_);
lean_dec_ref(v_f_6418_);
v___x_6427_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6428_ = l_Lean_MessageData_ofName(v_const_6425_);
v___x_6429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6429_, 0, v___x_6427_);
lean_ctor_set(v___x_6429_, 1, v___x_6428_);
v___x_6430_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6431_, 0, v___x_6429_);
lean_ctor_set(v___x_6431_, 1, v___x_6430_);
v___x_6432_ = l_Lean_MessageData_ofName(v_module_6424_);
v___x_6433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6433_, 0, v___x_6431_);
lean_ctor_set(v___x_6433_, 1, v___x_6432_);
v___x_6434_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6435_, 0, v___x_6433_);
lean_ctor_set(v___x_6435_, 1, v___x_6434_);
v___x_6436_ = l_Lean_Exception_toMessageData(v_exception_6426_);
v___x_6437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6437_, 0, v___x_6435_);
lean_ctor_set(v___x_6437_, 1, v___x_6436_);
v___x_6438_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6437_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_);
return v___x_6438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6439_, lean_object* v___y_6440_, lean_object* v___y_6441_, lean_object* v___y_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_){
_start:
{
lean_object* v_res_6445_; 
v_res_6445_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_);
lean_dec(v___y_6443_);
lean_dec_ref(v___y_6442_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
return v_res_6445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6446_, size_t v_i_6447_, size_t v_stop_6448_, lean_object* v_b_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_){
_start:
{
uint8_t v___x_6455_; 
v___x_6455_ = lean_usize_dec_eq(v_i_6447_, v_stop_6448_);
if (v___x_6455_ == 0)
{
lean_object* v___x_6456_; lean_object* v___x_6457_; 
v___x_6456_ = lean_array_uget_borrowed(v_as_6446_, v_i_6447_);
lean_inc(v___x_6456_);
v___x_6457_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6456_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_);
if (lean_obj_tag(v___x_6457_) == 0)
{
lean_object* v_a_6458_; size_t v___x_6459_; size_t v___x_6460_; 
v_a_6458_ = lean_ctor_get(v___x_6457_, 0);
lean_inc(v_a_6458_);
lean_dec_ref(v___x_6457_);
v___x_6459_ = ((size_t)1ULL);
v___x_6460_ = lean_usize_add(v_i_6447_, v___x_6459_);
v_i_6447_ = v___x_6460_;
v_b_6449_ = v_a_6458_;
goto _start;
}
else
{
return v___x_6457_;
}
}
else
{
lean_object* v___x_6462_; 
v___x_6462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6462_, 0, v_b_6449_);
return v___x_6462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6463_, lean_object* v_i_6464_, lean_object* v_stop_6465_, lean_object* v_b_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_, lean_object* v___y_6471_){
_start:
{
size_t v_i_boxed_6472_; size_t v_stop_boxed_6473_; lean_object* v_res_6474_; 
v_i_boxed_6472_ = lean_unbox_usize(v_i_6464_);
lean_dec(v_i_6464_);
v_stop_boxed_6473_ = lean_unbox_usize(v_stop_6465_);
lean_dec(v_stop_6465_);
v_res_6474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6463_, v_i_boxed_6472_, v_stop_boxed_6473_, v_b_6466_, v___y_6467_, v___y_6468_, v___y_6469_, v___y_6470_);
lean_dec(v___y_6470_);
lean_dec_ref(v___y_6469_);
lean_dec(v___y_6468_);
lean_dec_ref(v___y_6467_);
lean_dec_ref(v_as_6463_);
return v_res_6474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6475_, size_t v_i_6476_, size_t v_stop_6477_, lean_object* v_b_6478_){
_start:
{
uint8_t v___x_6479_; 
v___x_6479_ = lean_usize_dec_eq(v_i_6476_, v_stop_6477_);
if (v___x_6479_ == 0)
{
lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; size_t v___x_6483_; size_t v___x_6484_; 
v___x_6480_ = lean_array_uget_borrowed(v_as_6475_, v_i_6476_);
lean_inc(v___x_6480_);
v___x_6481_ = lean_task_get_own(v___x_6480_);
v___x_6482_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6478_, v___x_6481_);
v___x_6483_ = ((size_t)1ULL);
v___x_6484_ = lean_usize_add(v_i_6476_, v___x_6483_);
v_i_6476_ = v___x_6484_;
v_b_6478_ = v___x_6482_;
goto _start;
}
else
{
return v_b_6478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6486_, lean_object* v_i_6487_, lean_object* v_stop_6488_, lean_object* v_b_6489_){
_start:
{
size_t v_i_boxed_6490_; size_t v_stop_boxed_6491_; lean_object* v_res_6492_; 
v_i_boxed_6490_ = lean_unbox_usize(v_i_6487_);
lean_dec(v_i_6487_);
v_stop_boxed_6491_ = lean_unbox_usize(v_stop_6488_);
lean_dec(v_stop_6488_);
v_res_6492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6486_, v_i_boxed_6490_, v_stop_boxed_6491_, v_b_6489_);
lean_dec_ref(v_as_6486_);
return v_res_6492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6493_, lean_object* v_tasks_6494_){
_start:
{
lean_object* v___x_6495_; lean_object* v___x_6496_; uint8_t v___x_6497_; 
v___x_6495_ = lean_unsigned_to_nat(0u);
v___x_6496_ = lean_array_get_size(v_tasks_6494_);
v___x_6497_ = lean_nat_dec_lt(v___x_6495_, v___x_6496_);
if (v___x_6497_ == 0)
{
return v_z_6493_;
}
else
{
uint8_t v___x_6498_; 
v___x_6498_ = lean_nat_dec_le(v___x_6496_, v___x_6496_);
if (v___x_6498_ == 0)
{
if (v___x_6497_ == 0)
{
return v_z_6493_;
}
else
{
size_t v___x_6499_; size_t v___x_6500_; lean_object* v___x_6501_; 
v___x_6499_ = ((size_t)0ULL);
v___x_6500_ = lean_usize_of_nat(v___x_6496_);
v___x_6501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6494_, v___x_6499_, v___x_6500_, v_z_6493_);
return v___x_6501_;
}
}
else
{
size_t v___x_6502_; size_t v___x_6503_; lean_object* v___x_6504_; 
v___x_6502_ = ((size_t)0ULL);
v___x_6503_ = lean_usize_of_nat(v___x_6496_);
v___x_6504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6494_, v___x_6502_, v___x_6503_, v_z_6493_);
return v___x_6504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6505_, lean_object* v_tasks_6506_){
_start:
{
lean_object* v_res_6507_; 
v_res_6507_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6505_, v_tasks_6506_);
lean_dec_ref(v_tasks_6506_);
return v_res_6507_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; 
v___x_6508_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6509_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6510_, 0, v___x_6509_);
lean_ctor_set(v___x_6510_, 1, v___x_6508_);
return v___x_6510_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; 
v___x_6511_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6512_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6513_, 0, v___x_6512_);
lean_ctor_set(v___x_6513_, 1, v___x_6511_);
return v___x_6513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6514_, lean_object* v_ngen_6515_, lean_object* v_env_6516_, lean_object* v_act_6517_, lean_object* v_constantsPerTask_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_){
_start:
{
lean_object* v___x_6524_; lean_object* v_moduleData_6525_; lean_object* v_n_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v_a_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6572_; 
v___x_6524_ = l_Lean_Environment_header(v_env_6516_);
v_moduleData_6525_ = lean_ctor_get(v___x_6524_, 6);
lean_inc_ref(v_moduleData_6525_);
lean_dec_ref(v___x_6524_);
v_n_6526_ = lean_array_get_size(v_moduleData_6525_);
lean_dec_ref(v_moduleData_6525_);
v___x_6527_ = lean_unsigned_to_nat(0u);
v___x_6528_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6529_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6514_, v_env_6516_, v_act_6517_, v_constantsPerTask_6518_, v_n_6526_, v_ngen_6515_, v___x_6528_, v___x_6527_, v___x_6527_, v___x_6527_);
v_a_6530_ = lean_ctor_get(v___x_6529_, 0);
v_isSharedCheck_6572_ = !lean_is_exclusive(v___x_6529_);
if (v_isSharedCheck_6572_ == 0)
{
v___x_6532_ = v___x_6529_;
v_isShared_6533_ = v_isSharedCheck_6572_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_a_6530_);
lean_dec(v___x_6529_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6572_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v___x_6534_; lean_object* v_r_6535_; lean_object* v_tree_6542_; lean_object* v_errors_6543_; lean_object* v___x_6544_; uint8_t v___x_6545_; 
v___x_6534_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6535_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6534_, v_a_6530_);
lean_dec(v_a_6530_);
v_tree_6542_ = lean_ctor_get(v_r_6535_, 0);
lean_inc_ref(v_tree_6542_);
v_errors_6543_ = lean_ctor_get(v_r_6535_, 1);
lean_inc_ref(v_errors_6543_);
v___x_6544_ = lean_array_get_size(v_errors_6543_);
v___x_6545_ = lean_nat_dec_lt(v___x_6527_, v___x_6544_);
if (v___x_6545_ == 0)
{
lean_object* v___x_6546_; lean_object* v___x_6547_; 
lean_dec_ref(v_errors_6543_);
lean_dec_ref(v_r_6535_);
lean_del_object(v___x_6532_);
v___x_6546_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6542_);
v___x_6547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6547_, 0, v___x_6546_);
return v___x_6547_;
}
else
{
lean_object* v___x_6548_; uint8_t v___x_6549_; 
lean_dec_ref(v_tree_6542_);
v___x_6548_ = lean_box(0);
v___x_6549_ = lean_nat_dec_le(v___x_6544_, v___x_6544_);
if (v___x_6549_ == 0)
{
if (v___x_6545_ == 0)
{
lean_dec_ref(v_errors_6543_);
goto v___jp_6536_;
}
else
{
size_t v___x_6550_; size_t v___x_6551_; lean_object* v___x_6552_; 
v___x_6550_ = ((size_t)0ULL);
v___x_6551_ = lean_usize_of_nat(v___x_6544_);
v___x_6552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6543_, v___x_6550_, v___x_6551_, v___x_6548_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_);
lean_dec_ref(v_errors_6543_);
if (lean_obj_tag(v___x_6552_) == 0)
{
lean_dec_ref(v___x_6552_);
goto v___jp_6536_;
}
else
{
lean_object* v_a_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6560_; 
lean_dec_ref(v_r_6535_);
lean_del_object(v___x_6532_);
v_a_6553_ = lean_ctor_get(v___x_6552_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v___x_6552_);
if (v_isSharedCheck_6560_ == 0)
{
v___x_6555_ = v___x_6552_;
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_a_6553_);
lean_dec(v___x_6552_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v___x_6558_; 
if (v_isShared_6556_ == 0)
{
v___x_6558_ = v___x_6555_;
goto v_reusejp_6557_;
}
else
{
lean_object* v_reuseFailAlloc_6559_; 
v_reuseFailAlloc_6559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6553_);
v___x_6558_ = v_reuseFailAlloc_6559_;
goto v_reusejp_6557_;
}
v_reusejp_6557_:
{
return v___x_6558_;
}
}
}
}
}
else
{
size_t v___x_6561_; size_t v___x_6562_; lean_object* v___x_6563_; 
v___x_6561_ = ((size_t)0ULL);
v___x_6562_ = lean_usize_of_nat(v___x_6544_);
v___x_6563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6543_, v___x_6561_, v___x_6562_, v___x_6548_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_);
lean_dec_ref(v_errors_6543_);
if (lean_obj_tag(v___x_6563_) == 0)
{
lean_dec_ref(v___x_6563_);
goto v___jp_6536_;
}
else
{
lean_object* v_a_6564_; lean_object* v___x_6566_; uint8_t v_isShared_6567_; uint8_t v_isSharedCheck_6571_; 
lean_dec_ref(v_r_6535_);
lean_del_object(v___x_6532_);
v_a_6564_ = lean_ctor_get(v___x_6563_, 0);
v_isSharedCheck_6571_ = !lean_is_exclusive(v___x_6563_);
if (v_isSharedCheck_6571_ == 0)
{
v___x_6566_ = v___x_6563_;
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
else
{
lean_inc(v_a_6564_);
lean_dec(v___x_6563_);
v___x_6566_ = lean_box(0);
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
v_resetjp_6565_:
{
lean_object* v___x_6569_; 
if (v_isShared_6567_ == 0)
{
v___x_6569_ = v___x_6566_;
goto v_reusejp_6568_;
}
else
{
lean_object* v_reuseFailAlloc_6570_; 
v_reuseFailAlloc_6570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6570_, 0, v_a_6564_);
v___x_6569_ = v_reuseFailAlloc_6570_;
goto v_reusejp_6568_;
}
v_reusejp_6568_:
{
return v___x_6569_;
}
}
}
}
}
v___jp_6536_:
{
lean_object* v_tree_6537_; lean_object* v___x_6538_; lean_object* v___x_6540_; 
v_tree_6537_ = lean_ctor_get(v_r_6535_, 0);
lean_inc_ref(v_tree_6537_);
lean_dec_ref(v_r_6535_);
v___x_6538_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6537_);
if (v_isShared_6533_ == 0)
{
lean_ctor_set(v___x_6532_, 0, v___x_6538_);
v___x_6540_ = v___x_6532_;
goto v_reusejp_6539_;
}
else
{
lean_object* v_reuseFailAlloc_6541_; 
v_reuseFailAlloc_6541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6541_, 0, v___x_6538_);
v___x_6540_ = v_reuseFailAlloc_6541_;
goto v_reusejp_6539_;
}
v_reusejp_6539_:
{
return v___x_6540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6573_, lean_object* v_ngen_6574_, lean_object* v_env_6575_, lean_object* v_act_6576_, lean_object* v_constantsPerTask_6577_, lean_object* v___y_6578_, lean_object* v___y_6579_, lean_object* v___y_6580_, lean_object* v___y_6581_, lean_object* v___y_6582_){
_start:
{
lean_object* v_res_6583_; 
v_res_6583_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6573_, v_ngen_6574_, v_env_6575_, v_act_6576_, v_constantsPerTask_6577_, v___y_6578_, v___y_6579_, v___y_6580_, v___y_6581_);
lean_dec(v___y_6581_);
lean_dec_ref(v___y_6580_);
lean_dec(v___y_6579_);
lean_dec_ref(v___y_6578_);
lean_dec(v_constantsPerTask_6577_);
return v_res_6583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6584_, lean_object* v___x_6585_, lean_object* v_addEntry_6586_, lean_object* v_constantsPerTask_6587_, lean_object* v_droppedEntriesRef_6588_, lean_object* v_droppedKeys_6589_, lean_object* v___y_6590_, lean_object* v___y_6591_, lean_object* v___y_6592_, lean_object* v___y_6593_){
_start:
{
lean_object* v___x_6595_; lean_object* v_env_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; 
v___x_6595_ = lean_st_ref_get(v___y_6593_);
v_env_6596_ = lean_ctor_get(v___x_6595_, 0);
lean_inc_ref(v_env_6596_);
lean_dec(v___x_6595_);
lean_inc_ref(v_a_6584_);
v___x_6597_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6584_);
v___x_6598_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6597_, v___x_6585_, v_env_6596_, v_addEntry_6586_, v_constantsPerTask_6587_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_);
if (lean_obj_tag(v___x_6598_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6588_) == 1)
{
lean_object* v_a_6599_; lean_object* v_val_6600_; lean_object* v___x_6602_; uint8_t v_isShared_6603_; uint8_t v_isSharedCheck_6633_; 
v_a_6599_ = lean_ctor_get(v___x_6598_, 0);
lean_inc(v_a_6599_);
lean_dec_ref(v___x_6598_);
v_val_6600_ = lean_ctor_get(v_droppedEntriesRef_6588_, 0);
v_isSharedCheck_6633_ = !lean_is_exclusive(v_droppedEntriesRef_6588_);
if (v_isSharedCheck_6633_ == 0)
{
v___x_6602_ = v_droppedEntriesRef_6588_;
v_isShared_6603_ = v_isSharedCheck_6633_;
goto v_resetjp_6601_;
}
else
{
lean_inc(v_val_6600_);
lean_dec(v_droppedEntriesRef_6588_);
v___x_6602_ = lean_box(0);
v_isShared_6603_ = v_isSharedCheck_6633_;
goto v_resetjp_6601_;
}
v_resetjp_6601_:
{
lean_object* v___x_6604_; 
v___x_6604_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6599_, v_droppedKeys_6589_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_);
if (lean_obj_tag(v___x_6604_) == 0)
{
lean_object* v_a_6605_; lean_object* v___x_6607_; uint8_t v_isShared_6608_; uint8_t v_isSharedCheck_6624_; 
v_a_6605_ = lean_ctor_get(v___x_6604_, 0);
v_isSharedCheck_6624_ = !lean_is_exclusive(v___x_6604_);
if (v_isSharedCheck_6624_ == 0)
{
v___x_6607_ = v___x_6604_;
v_isShared_6608_ = v_isSharedCheck_6624_;
goto v_resetjp_6606_;
}
else
{
lean_inc(v_a_6605_);
lean_dec(v___x_6604_);
v___x_6607_ = lean_box(0);
v_isShared_6608_ = v_isSharedCheck_6624_;
goto v_resetjp_6606_;
}
v_resetjp_6606_:
{
lean_object* v_fst_6609_; lean_object* v_snd_6610_; lean_object* v___x_6611_; lean_object* v___y_6613_; 
v_fst_6609_ = lean_ctor_get(v_a_6605_, 0);
lean_inc(v_fst_6609_);
v_snd_6610_ = lean_ctor_get(v_a_6605_, 1);
lean_inc(v_snd_6610_);
lean_dec(v_a_6605_);
v___x_6611_ = lean_st_ref_get(v_val_6600_);
if (lean_obj_tag(v___x_6611_) == 0)
{
lean_object* v___x_6622_; 
v___x_6622_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6613_ = v___x_6622_;
goto v___jp_6612_;
}
else
{
lean_object* v_val_6623_; 
v_val_6623_ = lean_ctor_get(v___x_6611_, 0);
lean_inc(v_val_6623_);
lean_dec_ref(v___x_6611_);
v___y_6613_ = v_val_6623_;
goto v___jp_6612_;
}
v___jp_6612_:
{
lean_object* v___x_6614_; lean_object* v___x_6616_; 
v___x_6614_ = l_Array_append___redArg(v___y_6613_, v_fst_6609_);
lean_dec(v_fst_6609_);
if (v_isShared_6603_ == 0)
{
lean_ctor_set(v___x_6602_, 0, v___x_6614_);
v___x_6616_ = v___x_6602_;
goto v_reusejp_6615_;
}
else
{
lean_object* v_reuseFailAlloc_6621_; 
v_reuseFailAlloc_6621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6621_, 0, v___x_6614_);
v___x_6616_ = v_reuseFailAlloc_6621_;
goto v_reusejp_6615_;
}
v_reusejp_6615_:
{
lean_object* v___x_6617_; lean_object* v___x_6619_; 
v___x_6617_ = lean_st_ref_set(v_val_6600_, v___x_6616_);
lean_dec(v_val_6600_);
if (v_isShared_6608_ == 0)
{
lean_ctor_set(v___x_6607_, 0, v_snd_6610_);
v___x_6619_ = v___x_6607_;
goto v_reusejp_6618_;
}
else
{
lean_object* v_reuseFailAlloc_6620_; 
v_reuseFailAlloc_6620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6620_, 0, v_snd_6610_);
v___x_6619_ = v_reuseFailAlloc_6620_;
goto v_reusejp_6618_;
}
v_reusejp_6618_:
{
return v___x_6619_;
}
}
}
}
}
else
{
lean_object* v_a_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6632_; 
lean_del_object(v___x_6602_);
lean_dec(v_val_6600_);
v_a_6625_ = lean_ctor_get(v___x_6604_, 0);
v_isSharedCheck_6632_ = !lean_is_exclusive(v___x_6604_);
if (v_isSharedCheck_6632_ == 0)
{
v___x_6627_ = v___x_6604_;
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_a_6625_);
lean_dec(v___x_6604_);
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
}
else
{
lean_object* v_a_6634_; lean_object* v___x_6635_; 
lean_dec(v_droppedEntriesRef_6588_);
v_a_6634_ = lean_ctor_get(v___x_6598_, 0);
lean_inc(v_a_6634_);
lean_dec_ref(v___x_6598_);
v___x_6635_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6634_, v_droppedKeys_6589_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_);
return v___x_6635_;
}
}
else
{
lean_dec(v_droppedKeys_6589_);
lean_dec(v_droppedEntriesRef_6588_);
return v___x_6598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6636_, lean_object* v___x_6637_, lean_object* v_addEntry_6638_, lean_object* v_constantsPerTask_6639_, lean_object* v_droppedEntriesRef_6640_, lean_object* v_droppedKeys_6641_, lean_object* v___y_6642_, lean_object* v___y_6643_, lean_object* v___y_6644_, lean_object* v___y_6645_, lean_object* v___y_6646_){
_start:
{
lean_object* v_res_6647_; 
v_res_6647_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6636_, v___x_6637_, v_addEntry_6638_, v_constantsPerTask_6639_, v_droppedEntriesRef_6640_, v_droppedKeys_6641_, v___y_6642_, v___y_6643_, v___y_6644_, v___y_6645_);
lean_dec(v___y_6645_);
lean_dec_ref(v___y_6644_);
lean_dec(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec(v_constantsPerTask_6639_);
lean_dec_ref(v_a_6636_);
return v_res_6647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ext_6649_, lean_object* v_addEntry_6650_, lean_object* v_droppedKeys_6651_, lean_object* v_constantsPerTask_6652_, lean_object* v_droppedEntriesRef_6653_, lean_object* v_ty_6654_, lean_object* v_a_6655_, lean_object* v_a_6656_, lean_object* v_a_6657_, lean_object* v_a_6658_){
_start:
{
lean_object* v___x_6660_; lean_object* v_ngen_6661_; lean_object* v_namePrefix_6662_; lean_object* v_idx_6663_; lean_object* v___x_6665_; uint8_t v_isShared_6666_; uint8_t v_isSharedCheck_6737_; 
v___x_6660_ = lean_st_ref_get(v_a_6658_);
v_ngen_6661_ = lean_ctor_get(v___x_6660_, 2);
lean_inc_ref(v_ngen_6661_);
lean_dec(v___x_6660_);
v_namePrefix_6662_ = lean_ctor_get(v_ngen_6661_, 0);
v_idx_6663_ = lean_ctor_get(v_ngen_6661_, 1);
v_isSharedCheck_6737_ = !lean_is_exclusive(v_ngen_6661_);
if (v_isSharedCheck_6737_ == 0)
{
v___x_6665_ = v_ngen_6661_;
v_isShared_6666_ = v_isSharedCheck_6737_;
goto v_resetjp_6664_;
}
else
{
lean_inc(v_idx_6663_);
lean_inc(v_namePrefix_6662_);
lean_dec(v_ngen_6661_);
v___x_6665_ = lean_box(0);
v_isShared_6666_ = v_isSharedCheck_6737_;
goto v_resetjp_6664_;
}
v_resetjp_6664_:
{
lean_object* v___x_6667_; lean_object* v_env_6668_; lean_object* v_nextMacroScope_6669_; lean_object* v_auxDeclNGen_6670_; lean_object* v_traceState_6671_; lean_object* v_cache_6672_; lean_object* v_messages_6673_; lean_object* v_infoState_6674_; lean_object* v_snapshotTasks_6675_; lean_object* v___x_6677_; uint8_t v_isShared_6678_; uint8_t v_isSharedCheck_6735_; 
v___x_6667_ = lean_st_ref_take(v_a_6658_);
v_env_6668_ = lean_ctor_get(v___x_6667_, 0);
v_nextMacroScope_6669_ = lean_ctor_get(v___x_6667_, 1);
v_auxDeclNGen_6670_ = lean_ctor_get(v___x_6667_, 3);
v_traceState_6671_ = lean_ctor_get(v___x_6667_, 4);
v_cache_6672_ = lean_ctor_get(v___x_6667_, 5);
v_messages_6673_ = lean_ctor_get(v___x_6667_, 6);
v_infoState_6674_ = lean_ctor_get(v___x_6667_, 7);
v_snapshotTasks_6675_ = lean_ctor_get(v___x_6667_, 8);
v_isSharedCheck_6735_ = !lean_is_exclusive(v___x_6667_);
if (v_isSharedCheck_6735_ == 0)
{
lean_object* v_unused_6736_; 
v_unused_6736_ = lean_ctor_get(v___x_6667_, 2);
lean_dec(v_unused_6736_);
v___x_6677_ = v___x_6667_;
v_isShared_6678_ = v_isSharedCheck_6735_;
goto v_resetjp_6676_;
}
else
{
lean_inc(v_snapshotTasks_6675_);
lean_inc(v_infoState_6674_);
lean_inc(v_messages_6673_);
lean_inc(v_cache_6672_);
lean_inc(v_traceState_6671_);
lean_inc(v_auxDeclNGen_6670_);
lean_inc(v_nextMacroScope_6669_);
lean_inc(v_env_6668_);
lean_dec(v___x_6667_);
v___x_6677_ = lean_box(0);
v_isShared_6678_ = v_isSharedCheck_6735_;
goto v_resetjp_6676_;
}
v_resetjp_6676_:
{
lean_object* v___x_6679_; lean_object* v___x_6680_; lean_object* v___x_6681_; lean_object* v___x_6683_; 
lean_inc(v_idx_6663_);
lean_inc(v_namePrefix_6662_);
v___x_6679_ = l_Lean_Name_num___override(v_namePrefix_6662_, v_idx_6663_);
v___x_6680_ = lean_unsigned_to_nat(1u);
v___x_6681_ = lean_nat_add(v_idx_6663_, v___x_6680_);
lean_dec(v_idx_6663_);
if (v_isShared_6666_ == 0)
{
lean_ctor_set(v___x_6665_, 1, v___x_6681_);
v___x_6683_ = v___x_6665_;
goto v_reusejp_6682_;
}
else
{
lean_object* v_reuseFailAlloc_6734_; 
v_reuseFailAlloc_6734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6734_, 0, v_namePrefix_6662_);
lean_ctor_set(v_reuseFailAlloc_6734_, 1, v___x_6681_);
v___x_6683_ = v_reuseFailAlloc_6734_;
goto v_reusejp_6682_;
}
v_reusejp_6682_:
{
lean_object* v___x_6685_; 
if (v_isShared_6678_ == 0)
{
lean_ctor_set(v___x_6677_, 2, v___x_6683_);
v___x_6685_ = v___x_6677_;
goto v_reusejp_6684_;
}
else
{
lean_object* v_reuseFailAlloc_6733_; 
v_reuseFailAlloc_6733_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6733_, 0, v_env_6668_);
lean_ctor_set(v_reuseFailAlloc_6733_, 1, v_nextMacroScope_6669_);
lean_ctor_set(v_reuseFailAlloc_6733_, 2, v___x_6683_);
lean_ctor_set(v_reuseFailAlloc_6733_, 3, v_auxDeclNGen_6670_);
lean_ctor_set(v_reuseFailAlloc_6733_, 4, v_traceState_6671_);
lean_ctor_set(v_reuseFailAlloc_6733_, 5, v_cache_6672_);
lean_ctor_set(v_reuseFailAlloc_6733_, 6, v_messages_6673_);
lean_ctor_set(v_reuseFailAlloc_6733_, 7, v_infoState_6674_);
lean_ctor_set(v_reuseFailAlloc_6733_, 8, v_snapshotTasks_6675_);
v___x_6685_ = v_reuseFailAlloc_6733_;
goto v_reusejp_6684_;
}
v_reusejp_6684_:
{
lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v_env_6690_; lean_object* v_asyncMode_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; lean_object* v_a_6695_; lean_object* v___x_6717_; 
v___x_6686_ = lean_st_ref_set(v_a_6658_, v___x_6685_);
v___x_6687_ = lean_box(0);
v___x_6688_ = lean_st_mk_ref(v___x_6687_);
v___x_6689_ = lean_st_ref_get(v_a_6658_);
v_env_6690_ = lean_ctor_get(v___x_6689_, 0);
lean_inc_ref(v_env_6690_);
lean_dec(v___x_6689_);
v_asyncMode_6691_ = lean_ctor_get(v_ext_6649_, 2);
v___x_6692_ = lean_box(0);
v___x_6693_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_6688_, v_ext_6649_, v_env_6690_, v_asyncMode_6691_, v___x_6692_);
lean_dec(v___x_6688_);
v___x_6717_ = lean_st_ref_get(v___x_6693_);
if (lean_obj_tag(v___x_6717_) == 0)
{
lean_object* v_options_6718_; lean_object* v___x_6719_; lean_object* v___f_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; 
v_options_6718_ = lean_ctor_get(v_a_6657_, 2);
v___x_6719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6719_, 0, v___x_6679_);
lean_ctor_set(v___x_6719_, 1, v___x_6680_);
lean_inc_ref(v_a_6657_);
v___f_6720_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6720_, 0, v_a_6657_);
lean_closure_set(v___f_6720_, 1, v___x_6719_);
lean_closure_set(v___f_6720_, 2, v_addEntry_6650_);
lean_closure_set(v___f_6720_, 3, v_constantsPerTask_6652_);
lean_closure_set(v___f_6720_, 4, v_droppedEntriesRef_6653_);
lean_closure_set(v___f_6720_, 5, v_droppedKeys_6651_);
v___x_6721_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6722_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6721_, v_options_6718_, v___f_6720_, v___x_6692_, v_a_6655_, v_a_6656_, v_a_6657_, v_a_6658_);
if (lean_obj_tag(v___x_6722_) == 0)
{
lean_object* v_a_6723_; 
v_a_6723_ = lean_ctor_get(v___x_6722_, 0);
lean_inc(v_a_6723_);
lean_dec_ref(v___x_6722_);
v_a_6695_ = v_a_6723_;
goto v___jp_6694_;
}
else
{
lean_object* v_a_6724_; lean_object* v___x_6726_; uint8_t v_isShared_6727_; uint8_t v_isSharedCheck_6731_; 
lean_dec(v___x_6693_);
lean_dec_ref(v_ty_6654_);
v_a_6724_ = lean_ctor_get(v___x_6722_, 0);
v_isSharedCheck_6731_ = !lean_is_exclusive(v___x_6722_);
if (v_isSharedCheck_6731_ == 0)
{
v___x_6726_ = v___x_6722_;
v_isShared_6727_ = v_isSharedCheck_6731_;
goto v_resetjp_6725_;
}
else
{
lean_inc(v_a_6724_);
lean_dec(v___x_6722_);
v___x_6726_ = lean_box(0);
v_isShared_6727_ = v_isSharedCheck_6731_;
goto v_resetjp_6725_;
}
v_resetjp_6725_:
{
lean_object* v___x_6729_; 
if (v_isShared_6727_ == 0)
{
v___x_6729_ = v___x_6726_;
goto v_reusejp_6728_;
}
else
{
lean_object* v_reuseFailAlloc_6730_; 
v_reuseFailAlloc_6730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6730_, 0, v_a_6724_);
v___x_6729_ = v_reuseFailAlloc_6730_;
goto v_reusejp_6728_;
}
v_reusejp_6728_:
{
return v___x_6729_;
}
}
}
}
else
{
lean_object* v_val_6732_; 
lean_dec(v___x_6679_);
lean_dec(v_droppedEntriesRef_6653_);
lean_dec(v_constantsPerTask_6652_);
lean_dec(v_droppedKeys_6651_);
lean_dec_ref(v_addEntry_6650_);
v_val_6732_ = lean_ctor_get(v___x_6717_, 0);
lean_inc(v_val_6732_);
lean_dec_ref(v___x_6717_);
v_a_6695_ = v_val_6732_;
goto v___jp_6694_;
}
v___jp_6694_:
{
lean_object* v___x_6696_; 
v___x_6696_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6695_, v_ty_6654_, v_a_6655_, v_a_6656_, v_a_6657_, v_a_6658_);
if (lean_obj_tag(v___x_6696_) == 0)
{
lean_object* v_a_6697_; lean_object* v___x_6699_; uint8_t v_isShared_6700_; uint8_t v_isSharedCheck_6708_; 
v_a_6697_ = lean_ctor_get(v___x_6696_, 0);
v_isSharedCheck_6708_ = !lean_is_exclusive(v___x_6696_);
if (v_isSharedCheck_6708_ == 0)
{
v___x_6699_ = v___x_6696_;
v_isShared_6700_ = v_isSharedCheck_6708_;
goto v_resetjp_6698_;
}
else
{
lean_inc(v_a_6697_);
lean_dec(v___x_6696_);
v___x_6699_ = lean_box(0);
v_isShared_6700_ = v_isSharedCheck_6708_;
goto v_resetjp_6698_;
}
v_resetjp_6698_:
{
lean_object* v_fst_6701_; lean_object* v_snd_6702_; lean_object* v___x_6703_; lean_object* v___x_6704_; lean_object* v___x_6706_; 
v_fst_6701_ = lean_ctor_get(v_a_6697_, 0);
lean_inc(v_fst_6701_);
v_snd_6702_ = lean_ctor_get(v_a_6697_, 1);
lean_inc(v_snd_6702_);
lean_dec(v_a_6697_);
v___x_6703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6703_, 0, v_snd_6702_);
v___x_6704_ = lean_st_ref_set(v___x_6693_, v___x_6703_);
lean_dec(v___x_6693_);
if (v_isShared_6700_ == 0)
{
lean_ctor_set(v___x_6699_, 0, v_fst_6701_);
v___x_6706_ = v___x_6699_;
goto v_reusejp_6705_;
}
else
{
lean_object* v_reuseFailAlloc_6707_; 
v_reuseFailAlloc_6707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6707_, 0, v_fst_6701_);
v___x_6706_ = v_reuseFailAlloc_6707_;
goto v_reusejp_6705_;
}
v_reusejp_6705_:
{
return v___x_6706_;
}
}
}
else
{
lean_object* v_a_6709_; lean_object* v___x_6711_; uint8_t v_isShared_6712_; uint8_t v_isSharedCheck_6716_; 
lean_dec(v___x_6693_);
v_a_6709_ = lean_ctor_get(v___x_6696_, 0);
v_isSharedCheck_6716_ = !lean_is_exclusive(v___x_6696_);
if (v_isSharedCheck_6716_ == 0)
{
v___x_6711_ = v___x_6696_;
v_isShared_6712_ = v_isSharedCheck_6716_;
goto v_resetjp_6710_;
}
else
{
lean_inc(v_a_6709_);
lean_dec(v___x_6696_);
v___x_6711_ = lean_box(0);
v_isShared_6712_ = v_isSharedCheck_6716_;
goto v_resetjp_6710_;
}
v_resetjp_6710_:
{
lean_object* v___x_6714_; 
if (v_isShared_6712_ == 0)
{
v___x_6714_ = v___x_6711_;
goto v_reusejp_6713_;
}
else
{
lean_object* v_reuseFailAlloc_6715_; 
v_reuseFailAlloc_6715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6715_, 0, v_a_6709_);
v___x_6714_ = v_reuseFailAlloc_6715_;
goto v_reusejp_6713_;
}
v_reusejp_6713_:
{
return v___x_6714_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ext_6738_, lean_object* v_addEntry_6739_, lean_object* v_droppedKeys_6740_, lean_object* v_constantsPerTask_6741_, lean_object* v_droppedEntriesRef_6742_, lean_object* v_ty_6743_, lean_object* v_a_6744_, lean_object* v_a_6745_, lean_object* v_a_6746_, lean_object* v_a_6747_, lean_object* v_a_6748_){
_start:
{
lean_object* v_res_6749_; 
v_res_6749_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ext_6738_, v_addEntry_6739_, v_droppedKeys_6740_, v_constantsPerTask_6741_, v_droppedEntriesRef_6742_, v_ty_6743_, v_a_6744_, v_a_6745_, v_a_6746_, v_a_6747_);
lean_dec(v_a_6747_);
lean_dec_ref(v_a_6746_);
lean_dec(v_a_6745_);
lean_dec_ref(v_a_6744_);
lean_dec_ref(v_ext_6738_);
return v_res_6749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6750_, lean_object* v_ext_6751_, lean_object* v_addEntry_6752_, lean_object* v_droppedKeys_6753_, lean_object* v_constantsPerTask_6754_, lean_object* v_droppedEntriesRef_6755_, lean_object* v_ty_6756_, lean_object* v_a_6757_, lean_object* v_a_6758_, lean_object* v_a_6759_, lean_object* v_a_6760_){
_start:
{
lean_object* v___x_6762_; 
v___x_6762_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ext_6751_, v_addEntry_6752_, v_droppedKeys_6753_, v_constantsPerTask_6754_, v_droppedEntriesRef_6755_, v_ty_6756_, v_a_6757_, v_a_6758_, v_a_6759_, v_a_6760_);
return v___x_6762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6763_, lean_object* v_ext_6764_, lean_object* v_addEntry_6765_, lean_object* v_droppedKeys_6766_, lean_object* v_constantsPerTask_6767_, lean_object* v_droppedEntriesRef_6768_, lean_object* v_ty_6769_, lean_object* v_a_6770_, lean_object* v_a_6771_, lean_object* v_a_6772_, lean_object* v_a_6773_, lean_object* v_a_6774_){
_start:
{
lean_object* v_res_6775_; 
v_res_6775_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6763_, v_ext_6764_, v_addEntry_6765_, v_droppedKeys_6766_, v_constantsPerTask_6767_, v_droppedEntriesRef_6768_, v_ty_6769_, v_a_6770_, v_a_6771_, v_a_6772_, v_a_6773_);
lean_dec(v_a_6773_);
lean_dec_ref(v_a_6772_);
lean_dec(v_a_6771_);
lean_dec_ref(v_a_6770_);
lean_dec_ref(v_ext_6764_);
return v_res_6775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6776_, lean_object* v_cctx_6777_, lean_object* v_ngen_6778_, lean_object* v_env_6779_, lean_object* v_act_6780_, lean_object* v_constantsPerTask_6781_, lean_object* v___y_6782_, lean_object* v___y_6783_, lean_object* v___y_6784_, lean_object* v___y_6785_){
_start:
{
lean_object* v___x_6787_; 
v___x_6787_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6777_, v_ngen_6778_, v_env_6779_, v_act_6780_, v_constantsPerTask_6781_, v___y_6782_, v___y_6783_, v___y_6784_, v___y_6785_);
return v___x_6787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6788_, lean_object* v_cctx_6789_, lean_object* v_ngen_6790_, lean_object* v_env_6791_, lean_object* v_act_6792_, lean_object* v_constantsPerTask_6793_, lean_object* v___y_6794_, lean_object* v___y_6795_, lean_object* v___y_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_){
_start:
{
lean_object* v_res_6799_; 
v_res_6799_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6788_, v_cctx_6789_, v_ngen_6790_, v_env_6791_, v_act_6792_, v_constantsPerTask_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_);
lean_dec(v___y_6797_);
lean_dec_ref(v___y_6796_);
lean_dec(v___y_6795_);
lean_dec_ref(v___y_6794_);
lean_dec(v_constantsPerTask_6793_);
return v_res_6799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6800_, lean_object* v_cctx_6801_, lean_object* v_env_6802_, lean_object* v_act_6803_, lean_object* v_constantsPerTask_6804_, lean_object* v_n_6805_, lean_object* v_ngen_6806_, lean_object* v_tasks_6807_, lean_object* v_start_6808_, lean_object* v_cnt_6809_, lean_object* v_idx_6810_, lean_object* v___y_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_){
_start:
{
lean_object* v___x_6816_; 
v___x_6816_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6801_, v_env_6802_, v_act_6803_, v_constantsPerTask_6804_, v_n_6805_, v_ngen_6806_, v_tasks_6807_, v_start_6808_, v_cnt_6809_, v_idx_6810_);
return v___x_6816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6817_, lean_object* v_cctx_6818_, lean_object* v_env_6819_, lean_object* v_act_6820_, lean_object* v_constantsPerTask_6821_, lean_object* v_n_6822_, lean_object* v_ngen_6823_, lean_object* v_tasks_6824_, lean_object* v_start_6825_, lean_object* v_cnt_6826_, lean_object* v_idx_6827_, lean_object* v___y_6828_, lean_object* v___y_6829_, lean_object* v___y_6830_, lean_object* v___y_6831_, lean_object* v___y_6832_){
_start:
{
lean_object* v_res_6833_; 
v_res_6833_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6817_, v_cctx_6818_, v_env_6819_, v_act_6820_, v_constantsPerTask_6821_, v_n_6822_, v_ngen_6823_, v_tasks_6824_, v_start_6825_, v_cnt_6826_, v_idx_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_);
lean_dec(v___y_6831_);
lean_dec_ref(v___y_6830_);
lean_dec(v___y_6829_);
lean_dec_ref(v___y_6828_);
lean_dec(v_constantsPerTask_6821_);
return v_res_6833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6834_, lean_object* v_z_6835_, lean_object* v_tasks_6836_){
_start:
{
lean_object* v___x_6837_; 
v___x_6837_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6835_, v_tasks_6836_);
return v___x_6837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6838_, lean_object* v_z_6839_, lean_object* v_tasks_6840_){
_start:
{
lean_object* v_res_6841_; 
v_res_6841_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6838_, v_z_6839_, v_tasks_6840_);
lean_dec_ref(v_tasks_6840_);
return v_res_6841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6842_, lean_object* v_as_6843_, size_t v_i_6844_, size_t v_stop_6845_, lean_object* v_b_6846_){
_start:
{
lean_object* v___x_6847_; 
v___x_6847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6843_, v_i_6844_, v_stop_6845_, v_b_6846_);
return v___x_6847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6848_, lean_object* v_as_6849_, lean_object* v_i_6850_, lean_object* v_stop_6851_, lean_object* v_b_6852_){
_start:
{
size_t v_i_boxed_6853_; size_t v_stop_boxed_6854_; lean_object* v_res_6855_; 
v_i_boxed_6853_ = lean_unbox_usize(v_i_6850_);
lean_dec(v_i_6850_);
v_stop_boxed_6854_ = lean_unbox_usize(v_stop_6851_);
lean_dec(v_stop_6851_);
v_res_6855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6848_, v_as_6849_, v_i_boxed_6853_, v_stop_boxed_6854_, v_b_6852_);
lean_dec_ref(v_as_6849_);
return v_res_6855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6856_){
_start:
{
lean_object* v___x_6858_; lean_object* v_ngen_6859_; lean_object* v_namePrefix_6860_; lean_object* v_idx_6861_; lean_object* v___x_6863_; uint8_t v_isShared_6864_; uint8_t v_isSharedCheck_6891_; 
v___x_6858_ = lean_st_ref_get(v___y_6856_);
v_ngen_6859_ = lean_ctor_get(v___x_6858_, 2);
lean_inc_ref(v_ngen_6859_);
lean_dec(v___x_6858_);
v_namePrefix_6860_ = lean_ctor_get(v_ngen_6859_, 0);
v_idx_6861_ = lean_ctor_get(v_ngen_6859_, 1);
v_isSharedCheck_6891_ = !lean_is_exclusive(v_ngen_6859_);
if (v_isSharedCheck_6891_ == 0)
{
v___x_6863_ = v_ngen_6859_;
v_isShared_6864_ = v_isSharedCheck_6891_;
goto v_resetjp_6862_;
}
else
{
lean_inc(v_idx_6861_);
lean_inc(v_namePrefix_6860_);
lean_dec(v_ngen_6859_);
v___x_6863_ = lean_box(0);
v_isShared_6864_ = v_isSharedCheck_6891_;
goto v_resetjp_6862_;
}
v_resetjp_6862_:
{
lean_object* v___x_6865_; lean_object* v_env_6866_; lean_object* v_nextMacroScope_6867_; lean_object* v_auxDeclNGen_6868_; lean_object* v_traceState_6869_; lean_object* v_cache_6870_; lean_object* v_messages_6871_; lean_object* v_infoState_6872_; lean_object* v_snapshotTasks_6873_; lean_object* v___x_6875_; uint8_t v_isShared_6876_; uint8_t v_isSharedCheck_6889_; 
v___x_6865_ = lean_st_ref_take(v___y_6856_);
v_env_6866_ = lean_ctor_get(v___x_6865_, 0);
v_nextMacroScope_6867_ = lean_ctor_get(v___x_6865_, 1);
v_auxDeclNGen_6868_ = lean_ctor_get(v___x_6865_, 3);
v_traceState_6869_ = lean_ctor_get(v___x_6865_, 4);
v_cache_6870_ = lean_ctor_get(v___x_6865_, 5);
v_messages_6871_ = lean_ctor_get(v___x_6865_, 6);
v_infoState_6872_ = lean_ctor_get(v___x_6865_, 7);
v_snapshotTasks_6873_ = lean_ctor_get(v___x_6865_, 8);
v_isSharedCheck_6889_ = !lean_is_exclusive(v___x_6865_);
if (v_isSharedCheck_6889_ == 0)
{
lean_object* v_unused_6890_; 
v_unused_6890_ = lean_ctor_get(v___x_6865_, 2);
lean_dec(v_unused_6890_);
v___x_6875_ = v___x_6865_;
v_isShared_6876_ = v_isSharedCheck_6889_;
goto v_resetjp_6874_;
}
else
{
lean_inc(v_snapshotTasks_6873_);
lean_inc(v_infoState_6872_);
lean_inc(v_messages_6871_);
lean_inc(v_cache_6870_);
lean_inc(v_traceState_6869_);
lean_inc(v_auxDeclNGen_6868_);
lean_inc(v_nextMacroScope_6867_);
lean_inc(v_env_6866_);
lean_dec(v___x_6865_);
v___x_6875_ = lean_box(0);
v_isShared_6876_ = v_isSharedCheck_6889_;
goto v_resetjp_6874_;
}
v_resetjp_6874_:
{
lean_object* v___x_6877_; lean_object* v___x_6878_; lean_object* v___x_6879_; lean_object* v___x_6881_; 
lean_inc(v_idx_6861_);
lean_inc(v_namePrefix_6860_);
v___x_6877_ = l_Lean_Name_num___override(v_namePrefix_6860_, v_idx_6861_);
v___x_6878_ = lean_unsigned_to_nat(1u);
v___x_6879_ = lean_nat_add(v_idx_6861_, v___x_6878_);
lean_dec(v_idx_6861_);
if (v_isShared_6864_ == 0)
{
lean_ctor_set(v___x_6863_, 1, v___x_6879_);
v___x_6881_ = v___x_6863_;
goto v_reusejp_6880_;
}
else
{
lean_object* v_reuseFailAlloc_6888_; 
v_reuseFailAlloc_6888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6888_, 0, v_namePrefix_6860_);
lean_ctor_set(v_reuseFailAlloc_6888_, 1, v___x_6879_);
v___x_6881_ = v_reuseFailAlloc_6888_;
goto v_reusejp_6880_;
}
v_reusejp_6880_:
{
lean_object* v___x_6883_; 
if (v_isShared_6876_ == 0)
{
lean_ctor_set(v___x_6875_, 2, v___x_6881_);
v___x_6883_ = v___x_6875_;
goto v_reusejp_6882_;
}
else
{
lean_object* v_reuseFailAlloc_6887_; 
v_reuseFailAlloc_6887_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6887_, 0, v_env_6866_);
lean_ctor_set(v_reuseFailAlloc_6887_, 1, v_nextMacroScope_6867_);
lean_ctor_set(v_reuseFailAlloc_6887_, 2, v___x_6881_);
lean_ctor_set(v_reuseFailAlloc_6887_, 3, v_auxDeclNGen_6868_);
lean_ctor_set(v_reuseFailAlloc_6887_, 4, v_traceState_6869_);
lean_ctor_set(v_reuseFailAlloc_6887_, 5, v_cache_6870_);
lean_ctor_set(v_reuseFailAlloc_6887_, 6, v_messages_6871_);
lean_ctor_set(v_reuseFailAlloc_6887_, 7, v_infoState_6872_);
lean_ctor_set(v_reuseFailAlloc_6887_, 8, v_snapshotTasks_6873_);
v___x_6883_ = v_reuseFailAlloc_6887_;
goto v_reusejp_6882_;
}
v_reusejp_6882_:
{
lean_object* v___x_6884_; lean_object* v___x_6885_; lean_object* v___x_6886_; 
v___x_6884_ = lean_st_ref_set(v___y_6856_, v___x_6883_);
v___x_6885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6885_, 0, v___x_6877_);
lean_ctor_set(v___x_6885_, 1, v___x_6878_);
v___x_6886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6886_, 0, v___x_6885_);
return v___x_6886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6892_, lean_object* v___y_6893_){
_start:
{
lean_object* v_res_6894_; 
v_res_6894_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6892_);
lean_dec(v___y_6892_);
return v_res_6894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6895_, lean_object* v___y_6896_){
_start:
{
lean_object* v___x_6898_; 
v___x_6898_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6896_);
return v___x_6898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6899_, lean_object* v___y_6900_, lean_object* v___y_6901_){
_start:
{
lean_object* v_res_6902_; 
v_res_6902_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6899_, v___y_6900_);
lean_dec(v___y_6900_);
lean_dec_ref(v___y_6899_);
return v_res_6902_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6903_; lean_object* v___x_6904_; lean_object* v___x_6905_; 
v___x_6903_ = lean_unsigned_to_nat(32u);
v___x_6904_ = lean_mk_empty_array_with_capacity(v___x_6903_);
v___x_6905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6905_, 0, v___x_6904_);
return v___x_6905_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6906_; lean_object* v___x_6907_; lean_object* v___x_6908_; lean_object* v___x_6909_; lean_object* v___x_6910_; lean_object* v___x_6911_; 
v___x_6906_ = ((size_t)5ULL);
v___x_6907_ = lean_unsigned_to_nat(0u);
v___x_6908_ = lean_unsigned_to_nat(32u);
v___x_6909_ = lean_mk_empty_array_with_capacity(v___x_6908_);
v___x_6910_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6911_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6911_, 0, v___x_6910_);
lean_ctor_set(v___x_6911_, 1, v___x_6909_);
lean_ctor_set(v___x_6911_, 2, v___x_6907_);
lean_ctor_set(v___x_6911_, 3, v___x_6907_);
lean_ctor_set_usize(v___x_6911_, 4, v___x_6906_);
return v___x_6911_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6912_; lean_object* v___x_6913_; lean_object* v___x_6914_; lean_object* v___x_6915_; 
v___x_6912_ = lean_box(1);
v___x_6913_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6914_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6915_, 0, v___x_6914_);
lean_ctor_set(v___x_6915_, 1, v___x_6913_);
lean_ctor_set(v___x_6915_, 2, v___x_6912_);
return v___x_6915_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_){
_start:
{
lean_object* v___x_6920_; lean_object* v_env_6921_; lean_object* v_options_6922_; lean_object* v___x_6923_; lean_object* v___x_6924_; lean_object* v___x_6925_; lean_object* v___x_6926_; lean_object* v___x_6927_; 
v___x_6920_ = lean_st_ref_get(v___y_6918_);
v_env_6921_ = lean_ctor_get(v___x_6920_, 0);
lean_inc_ref(v_env_6921_);
lean_dec(v___x_6920_);
v_options_6922_ = lean_ctor_get(v___y_6917_, 2);
v___x_6923_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_6924_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6922_);
v___x_6925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6925_, 0, v_env_6921_);
lean_ctor_set(v___x_6925_, 1, v___x_6923_);
lean_ctor_set(v___x_6925_, 2, v___x_6924_);
lean_ctor_set(v___x_6925_, 3, v_options_6922_);
v___x_6926_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6926_, 0, v___x_6925_);
lean_ctor_set(v___x_6926_, 1, v_msgData_6916_);
v___x_6927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6927_, 0, v___x_6926_);
return v___x_6927_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6928_, lean_object* v___y_6929_, lean_object* v___y_6930_, lean_object* v___y_6931_){
_start:
{
lean_object* v_res_6932_; 
v_res_6932_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6928_, v___y_6929_, v___y_6930_);
lean_dec(v___y_6930_);
lean_dec_ref(v___y_6929_);
return v_res_6932_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6933_, lean_object* v_msgData_6934_, uint8_t v_severity_6935_, uint8_t v_isSilent_6936_, lean_object* v___y_6937_, lean_object* v___y_6938_){
_start:
{
uint8_t v___y_6941_; lean_object* v___y_6942_; lean_object* v___y_6943_; lean_object* v___y_6944_; uint8_t v___y_6945_; lean_object* v___y_6946_; lean_object* v___y_6947_; lean_object* v___y_6948_; lean_object* v___y_6949_; lean_object* v___y_6977_; uint8_t v___y_6978_; uint8_t v___y_6979_; uint8_t v___y_6980_; lean_object* v___y_6981_; lean_object* v___y_6982_; lean_object* v___y_6983_; lean_object* v___y_6984_; lean_object* v___y_7002_; uint8_t v___y_7003_; uint8_t v___y_7004_; lean_object* v___y_7005_; uint8_t v___y_7006_; lean_object* v___y_7007_; lean_object* v___y_7008_; lean_object* v___y_7009_; lean_object* v___y_7013_; uint8_t v___y_7014_; uint8_t v___y_7015_; lean_object* v___y_7016_; lean_object* v___y_7017_; lean_object* v___y_7018_; uint8_t v___y_7019_; uint8_t v___x_7024_; uint8_t v___y_7026_; lean_object* v___y_7027_; lean_object* v___y_7028_; lean_object* v___y_7029_; lean_object* v___y_7030_; uint8_t v___y_7031_; uint8_t v___y_7032_; uint8_t v___y_7034_; uint8_t v___x_7049_; 
v___x_7024_ = 2;
v___x_7049_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6935_, v___x_7024_);
if (v___x_7049_ == 0)
{
v___y_7034_ = v___x_7049_;
goto v___jp_7033_;
}
else
{
uint8_t v___x_7050_; 
lean_inc_ref(v_msgData_6934_);
v___x_7050_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6934_);
v___y_7034_ = v___x_7050_;
goto v___jp_7033_;
}
v___jp_6940_:
{
lean_object* v___x_6950_; lean_object* v_currNamespace_6951_; lean_object* v_openDecls_6952_; lean_object* v_env_6953_; lean_object* v_nextMacroScope_6954_; lean_object* v_ngen_6955_; lean_object* v_auxDeclNGen_6956_; lean_object* v_traceState_6957_; lean_object* v_cache_6958_; lean_object* v_messages_6959_; lean_object* v_infoState_6960_; lean_object* v_snapshotTasks_6961_; lean_object* v___x_6963_; uint8_t v_isShared_6964_; uint8_t v_isSharedCheck_6975_; 
v___x_6950_ = lean_st_ref_take(v___y_6949_);
v_currNamespace_6951_ = lean_ctor_get(v___y_6948_, 6);
v_openDecls_6952_ = lean_ctor_get(v___y_6948_, 7);
v_env_6953_ = lean_ctor_get(v___x_6950_, 0);
v_nextMacroScope_6954_ = lean_ctor_get(v___x_6950_, 1);
v_ngen_6955_ = lean_ctor_get(v___x_6950_, 2);
v_auxDeclNGen_6956_ = lean_ctor_get(v___x_6950_, 3);
v_traceState_6957_ = lean_ctor_get(v___x_6950_, 4);
v_cache_6958_ = lean_ctor_get(v___x_6950_, 5);
v_messages_6959_ = lean_ctor_get(v___x_6950_, 6);
v_infoState_6960_ = lean_ctor_get(v___x_6950_, 7);
v_snapshotTasks_6961_ = lean_ctor_get(v___x_6950_, 8);
v_isSharedCheck_6975_ = !lean_is_exclusive(v___x_6950_);
if (v_isSharedCheck_6975_ == 0)
{
v___x_6963_ = v___x_6950_;
v_isShared_6964_ = v_isSharedCheck_6975_;
goto v_resetjp_6962_;
}
else
{
lean_inc(v_snapshotTasks_6961_);
lean_inc(v_infoState_6960_);
lean_inc(v_messages_6959_);
lean_inc(v_cache_6958_);
lean_inc(v_traceState_6957_);
lean_inc(v_auxDeclNGen_6956_);
lean_inc(v_ngen_6955_);
lean_inc(v_nextMacroScope_6954_);
lean_inc(v_env_6953_);
lean_dec(v___x_6950_);
v___x_6963_ = lean_box(0);
v_isShared_6964_ = v_isSharedCheck_6975_;
goto v_resetjp_6962_;
}
v_resetjp_6962_:
{
lean_object* v___x_6965_; lean_object* v___x_6966_; lean_object* v___x_6967_; lean_object* v___x_6968_; lean_object* v___x_6970_; 
lean_inc(v_openDecls_6952_);
lean_inc(v_currNamespace_6951_);
v___x_6965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6965_, 0, v_currNamespace_6951_);
lean_ctor_set(v___x_6965_, 1, v_openDecls_6952_);
v___x_6966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6966_, 0, v___x_6965_);
lean_ctor_set(v___x_6966_, 1, v___y_6944_);
lean_inc_ref(v___y_6943_);
lean_inc_ref(v___y_6946_);
v___x_6967_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6967_, 0, v___y_6946_);
lean_ctor_set(v___x_6967_, 1, v___y_6947_);
lean_ctor_set(v___x_6967_, 2, v___y_6942_);
lean_ctor_set(v___x_6967_, 3, v___y_6943_);
lean_ctor_set(v___x_6967_, 4, v___x_6966_);
lean_ctor_set_uint8(v___x_6967_, sizeof(void*)*5, v___y_6941_);
lean_ctor_set_uint8(v___x_6967_, sizeof(void*)*5 + 1, v___y_6945_);
lean_ctor_set_uint8(v___x_6967_, sizeof(void*)*5 + 2, v_isSilent_6936_);
v___x_6968_ = l_Lean_MessageLog_add(v___x_6967_, v_messages_6959_);
if (v_isShared_6964_ == 0)
{
lean_ctor_set(v___x_6963_, 6, v___x_6968_);
v___x_6970_ = v___x_6963_;
goto v_reusejp_6969_;
}
else
{
lean_object* v_reuseFailAlloc_6974_; 
v_reuseFailAlloc_6974_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6974_, 0, v_env_6953_);
lean_ctor_set(v_reuseFailAlloc_6974_, 1, v_nextMacroScope_6954_);
lean_ctor_set(v_reuseFailAlloc_6974_, 2, v_ngen_6955_);
lean_ctor_set(v_reuseFailAlloc_6974_, 3, v_auxDeclNGen_6956_);
lean_ctor_set(v_reuseFailAlloc_6974_, 4, v_traceState_6957_);
lean_ctor_set(v_reuseFailAlloc_6974_, 5, v_cache_6958_);
lean_ctor_set(v_reuseFailAlloc_6974_, 6, v___x_6968_);
lean_ctor_set(v_reuseFailAlloc_6974_, 7, v_infoState_6960_);
lean_ctor_set(v_reuseFailAlloc_6974_, 8, v_snapshotTasks_6961_);
v___x_6970_ = v_reuseFailAlloc_6974_;
goto v_reusejp_6969_;
}
v_reusejp_6969_:
{
lean_object* v___x_6971_; lean_object* v___x_6972_; lean_object* v___x_6973_; 
v___x_6971_ = lean_st_ref_set(v___y_6949_, v___x_6970_);
v___x_6972_ = lean_box(0);
v___x_6973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6973_, 0, v___x_6972_);
return v___x_6973_;
}
}
}
v___jp_6976_:
{
lean_object* v___x_6985_; lean_object* v___x_6986_; lean_object* v_a_6987_; lean_object* v___x_6989_; uint8_t v_isShared_6990_; uint8_t v_isSharedCheck_7000_; 
v___x_6985_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6934_);
v___x_6986_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6985_, v___y_6937_, v___y_6938_);
v_a_6987_ = lean_ctor_get(v___x_6986_, 0);
v_isSharedCheck_7000_ = !lean_is_exclusive(v___x_6986_);
if (v_isSharedCheck_7000_ == 0)
{
v___x_6989_ = v___x_6986_;
v_isShared_6990_ = v_isSharedCheck_7000_;
goto v_resetjp_6988_;
}
else
{
lean_inc(v_a_6987_);
lean_dec(v___x_6986_);
v___x_6989_ = lean_box(0);
v_isShared_6990_ = v_isSharedCheck_7000_;
goto v_resetjp_6988_;
}
v_resetjp_6988_:
{
lean_object* v___x_6991_; lean_object* v___x_6992_; lean_object* v___x_6993_; lean_object* v___x_6994_; 
lean_inc_ref_n(v___y_6981_, 2);
v___x_6991_ = l_Lean_FileMap_toPosition(v___y_6981_, v___y_6983_);
lean_dec(v___y_6983_);
v___x_6992_ = l_Lean_FileMap_toPosition(v___y_6981_, v___y_6984_);
lean_dec(v___y_6984_);
v___x_6993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6993_, 0, v___x_6992_);
v___x_6994_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6978_ == 0)
{
lean_del_object(v___x_6989_);
lean_dec_ref(v___y_6977_);
v___y_6941_ = v___y_6979_;
v___y_6942_ = v___x_6993_;
v___y_6943_ = v___x_6994_;
v___y_6944_ = v_a_6987_;
v___y_6945_ = v___y_6980_;
v___y_6946_ = v___y_6982_;
v___y_6947_ = v___x_6991_;
v___y_6948_ = v___y_6937_;
v___y_6949_ = v___y_6938_;
goto v___jp_6940_;
}
else
{
uint8_t v___x_6995_; 
lean_inc(v_a_6987_);
v___x_6995_ = l_Lean_MessageData_hasTag(v___y_6977_, v_a_6987_);
if (v___x_6995_ == 0)
{
lean_object* v___x_6996_; lean_object* v___x_6998_; 
lean_dec_ref(v___x_6993_);
lean_dec_ref(v___x_6991_);
lean_dec(v_a_6987_);
v___x_6996_ = lean_box(0);
if (v_isShared_6990_ == 0)
{
lean_ctor_set(v___x_6989_, 0, v___x_6996_);
v___x_6998_ = v___x_6989_;
goto v_reusejp_6997_;
}
else
{
lean_object* v_reuseFailAlloc_6999_; 
v_reuseFailAlloc_6999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6999_, 0, v___x_6996_);
v___x_6998_ = v_reuseFailAlloc_6999_;
goto v_reusejp_6997_;
}
v_reusejp_6997_:
{
return v___x_6998_;
}
}
else
{
lean_del_object(v___x_6989_);
v___y_6941_ = v___y_6979_;
v___y_6942_ = v___x_6993_;
v___y_6943_ = v___x_6994_;
v___y_6944_ = v_a_6987_;
v___y_6945_ = v___y_6980_;
v___y_6946_ = v___y_6982_;
v___y_6947_ = v___x_6991_;
v___y_6948_ = v___y_6937_;
v___y_6949_ = v___y_6938_;
goto v___jp_6940_;
}
}
}
}
v___jp_7001_:
{
lean_object* v___x_7010_; 
v___x_7010_ = l_Lean_Syntax_getTailPos_x3f(v___y_7008_, v___y_7003_);
lean_dec(v___y_7008_);
if (lean_obj_tag(v___x_7010_) == 0)
{
lean_inc(v___y_7009_);
v___y_6977_ = v___y_7002_;
v___y_6978_ = v___y_7004_;
v___y_6979_ = v___y_7003_;
v___y_6980_ = v___y_7006_;
v___y_6981_ = v___y_7005_;
v___y_6982_ = v___y_7007_;
v___y_6983_ = v___y_7009_;
v___y_6984_ = v___y_7009_;
goto v___jp_6976_;
}
else
{
lean_object* v_val_7011_; 
v_val_7011_ = lean_ctor_get(v___x_7010_, 0);
lean_inc(v_val_7011_);
lean_dec_ref(v___x_7010_);
v___y_6977_ = v___y_7002_;
v___y_6978_ = v___y_7004_;
v___y_6979_ = v___y_7003_;
v___y_6980_ = v___y_7006_;
v___y_6981_ = v___y_7005_;
v___y_6982_ = v___y_7007_;
v___y_6983_ = v___y_7009_;
v___y_6984_ = v_val_7011_;
goto v___jp_6976_;
}
}
v___jp_7012_:
{
lean_object* v_ref_7020_; lean_object* v___x_7021_; 
v_ref_7020_ = l_Lean_replaceRef(v_ref_6933_, v___y_7018_);
v___x_7021_ = l_Lean_Syntax_getPos_x3f(v_ref_7020_, v___y_7015_);
if (lean_obj_tag(v___x_7021_) == 0)
{
lean_object* v___x_7022_; 
v___x_7022_ = lean_unsigned_to_nat(0u);
v___y_7002_ = v___y_7013_;
v___y_7003_ = v___y_7015_;
v___y_7004_ = v___y_7014_;
v___y_7005_ = v___y_7016_;
v___y_7006_ = v___y_7019_;
v___y_7007_ = v___y_7017_;
v___y_7008_ = v_ref_7020_;
v___y_7009_ = v___x_7022_;
goto v___jp_7001_;
}
else
{
lean_object* v_val_7023_; 
v_val_7023_ = lean_ctor_get(v___x_7021_, 0);
lean_inc(v_val_7023_);
lean_dec_ref(v___x_7021_);
v___y_7002_ = v___y_7013_;
v___y_7003_ = v___y_7015_;
v___y_7004_ = v___y_7014_;
v___y_7005_ = v___y_7016_;
v___y_7006_ = v___y_7019_;
v___y_7007_ = v___y_7017_;
v___y_7008_ = v_ref_7020_;
v___y_7009_ = v_val_7023_;
goto v___jp_7001_;
}
}
v___jp_7025_:
{
if (v___y_7032_ == 0)
{
v___y_7013_ = v___y_7030_;
v___y_7014_ = v___y_7026_;
v___y_7015_ = v___y_7031_;
v___y_7016_ = v___y_7027_;
v___y_7017_ = v___y_7029_;
v___y_7018_ = v___y_7028_;
v___y_7019_ = v_severity_6935_;
goto v___jp_7012_;
}
else
{
v___y_7013_ = v___y_7030_;
v___y_7014_ = v___y_7026_;
v___y_7015_ = v___y_7031_;
v___y_7016_ = v___y_7027_;
v___y_7017_ = v___y_7029_;
v___y_7018_ = v___y_7028_;
v___y_7019_ = v___x_7024_;
goto v___jp_7012_;
}
}
v___jp_7033_:
{
if (v___y_7034_ == 0)
{
lean_object* v_fileName_7035_; lean_object* v_fileMap_7036_; lean_object* v_options_7037_; lean_object* v_ref_7038_; uint8_t v_suppressElabErrors_7039_; lean_object* v___x_7040_; lean_object* v___x_7041_; lean_object* v___f_7042_; uint8_t v___x_7043_; uint8_t v___x_7044_; 
v_fileName_7035_ = lean_ctor_get(v___y_6937_, 0);
v_fileMap_7036_ = lean_ctor_get(v___y_6937_, 1);
v_options_7037_ = lean_ctor_get(v___y_6937_, 2);
v_ref_7038_ = lean_ctor_get(v___y_6937_, 5);
v_suppressElabErrors_7039_ = lean_ctor_get_uint8(v___y_6937_, sizeof(void*)*14 + 1);
v___x_7040_ = lean_box(v___y_7034_);
v___x_7041_ = lean_box(v_suppressElabErrors_7039_);
v___f_7042_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_7042_, 0, v___x_7040_);
lean_closure_set(v___f_7042_, 1, v___x_7041_);
v___x_7043_ = 1;
v___x_7044_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6935_, v___x_7043_);
if (v___x_7044_ == 0)
{
v___y_7026_ = v_suppressElabErrors_7039_;
v___y_7027_ = v_fileMap_7036_;
v___y_7028_ = v_ref_7038_;
v___y_7029_ = v_fileName_7035_;
v___y_7030_ = v___f_7042_;
v___y_7031_ = v___y_7034_;
v___y_7032_ = v___x_7044_;
goto v___jp_7025_;
}
else
{
lean_object* v___x_7045_; uint8_t v___x_7046_; 
v___x_7045_ = l_Lean_warningAsError;
v___x_7046_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_7037_, v___x_7045_);
v___y_7026_ = v_suppressElabErrors_7039_;
v___y_7027_ = v_fileMap_7036_;
v___y_7028_ = v_ref_7038_;
v___y_7029_ = v_fileName_7035_;
v___y_7030_ = v___f_7042_;
v___y_7031_ = v___y_7034_;
v___y_7032_ = v___x_7046_;
goto v___jp_7025_;
}
}
else
{
lean_object* v___x_7047_; lean_object* v___x_7048_; 
lean_dec_ref(v_msgData_6934_);
v___x_7047_ = lean_box(0);
v___x_7048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7048_, 0, v___x_7047_);
return v___x_7048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_7051_, lean_object* v_msgData_7052_, lean_object* v_severity_7053_, lean_object* v_isSilent_7054_, lean_object* v___y_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_){
_start:
{
uint8_t v_severity_boxed_7058_; uint8_t v_isSilent_boxed_7059_; lean_object* v_res_7060_; 
v_severity_boxed_7058_ = lean_unbox(v_severity_7053_);
v_isSilent_boxed_7059_ = lean_unbox(v_isSilent_7054_);
v_res_7060_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_7051_, v_msgData_7052_, v_severity_boxed_7058_, v_isSilent_boxed_7059_, v___y_7055_, v___y_7056_);
lean_dec(v___y_7056_);
lean_dec_ref(v___y_7055_);
lean_dec(v_ref_7051_);
return v_res_7060_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_7061_, uint8_t v_severity_7062_, uint8_t v_isSilent_7063_, lean_object* v___y_7064_, lean_object* v___y_7065_){
_start:
{
lean_object* v_ref_7067_; lean_object* v___x_7068_; 
v_ref_7067_ = lean_ctor_get(v___y_7064_, 5);
v___x_7068_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_7067_, v_msgData_7061_, v_severity_7062_, v_isSilent_7063_, v___y_7064_, v___y_7065_);
return v___x_7068_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_7069_, lean_object* v_severity_7070_, lean_object* v_isSilent_7071_, lean_object* v___y_7072_, lean_object* v___y_7073_, lean_object* v___y_7074_){
_start:
{
uint8_t v_severity_boxed_7075_; uint8_t v_isSilent_boxed_7076_; lean_object* v_res_7077_; 
v_severity_boxed_7075_ = lean_unbox(v_severity_7070_);
v_isSilent_boxed_7076_ = lean_unbox(v_isSilent_7071_);
v_res_7077_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_7069_, v_severity_boxed_7075_, v_isSilent_boxed_7076_, v___y_7072_, v___y_7073_);
lean_dec(v___y_7073_);
lean_dec_ref(v___y_7072_);
return v_res_7077_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_7078_, lean_object* v___y_7079_, lean_object* v___y_7080_){
_start:
{
uint8_t v___x_7082_; uint8_t v___x_7083_; lean_object* v___x_7084_; 
v___x_7082_ = 2;
v___x_7083_ = 0;
v___x_7084_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_7078_, v___x_7082_, v___x_7083_, v___y_7079_, v___y_7080_);
return v___x_7084_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_7085_, lean_object* v___y_7086_, lean_object* v___y_7087_, lean_object* v___y_7088_){
_start:
{
lean_object* v_res_7089_; 
v_res_7089_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_7085_, v___y_7086_, v___y_7087_);
lean_dec(v___y_7087_);
lean_dec_ref(v___y_7086_);
return v_res_7089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_7090_, lean_object* v___y_7091_, lean_object* v___y_7092_){
_start:
{
lean_object* v_module_7094_; lean_object* v_const_7095_; lean_object* v_exception_7096_; lean_object* v___x_7097_; lean_object* v___x_7098_; lean_object* v___x_7099_; lean_object* v___x_7100_; lean_object* v___x_7101_; lean_object* v___x_7102_; lean_object* v___x_7103_; lean_object* v___x_7104_; lean_object* v___x_7105_; lean_object* v___x_7106_; lean_object* v___x_7107_; lean_object* v___x_7108_; 
v_module_7094_ = lean_ctor_get(v_f_7090_, 0);
lean_inc(v_module_7094_);
v_const_7095_ = lean_ctor_get(v_f_7090_, 1);
lean_inc(v_const_7095_);
v_exception_7096_ = lean_ctor_get(v_f_7090_, 2);
lean_inc_ref(v_exception_7096_);
lean_dec_ref(v_f_7090_);
v___x_7097_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_7098_ = l_Lean_MessageData_ofName(v_const_7095_);
v___x_7099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7099_, 0, v___x_7097_);
lean_ctor_set(v___x_7099_, 1, v___x_7098_);
v___x_7100_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_7101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7101_, 0, v___x_7099_);
lean_ctor_set(v___x_7101_, 1, v___x_7100_);
v___x_7102_ = l_Lean_MessageData_ofName(v_module_7094_);
v___x_7103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7103_, 0, v___x_7101_);
lean_ctor_set(v___x_7103_, 1, v___x_7102_);
v___x_7104_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_7105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7105_, 0, v___x_7103_);
lean_ctor_set(v___x_7105_, 1, v___x_7104_);
v___x_7106_ = l_Lean_Exception_toMessageData(v_exception_7096_);
v___x_7107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7107_, 0, v___x_7105_);
lean_ctor_set(v___x_7107_, 1, v___x_7106_);
v___x_7108_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_7107_, v___y_7091_, v___y_7092_);
return v___x_7108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_7109_, lean_object* v___y_7110_, lean_object* v___y_7111_, lean_object* v___y_7112_){
_start:
{
lean_object* v_res_7113_; 
v_res_7113_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_7109_, v___y_7110_, v___y_7111_);
lean_dec(v___y_7111_);
lean_dec_ref(v___y_7110_);
return v_res_7113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_7114_, size_t v_i_7115_, size_t v_stop_7116_, lean_object* v_b_7117_, lean_object* v___y_7118_, lean_object* v___y_7119_){
_start:
{
uint8_t v___x_7121_; 
v___x_7121_ = lean_usize_dec_eq(v_i_7115_, v_stop_7116_);
if (v___x_7121_ == 0)
{
lean_object* v___x_7122_; lean_object* v___x_7123_; 
v___x_7122_ = lean_array_uget_borrowed(v_as_7114_, v_i_7115_);
lean_inc(v___x_7122_);
v___x_7123_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_7122_, v___y_7118_, v___y_7119_);
if (lean_obj_tag(v___x_7123_) == 0)
{
lean_object* v_a_7124_; size_t v___x_7125_; size_t v___x_7126_; 
v_a_7124_ = lean_ctor_get(v___x_7123_, 0);
lean_inc(v_a_7124_);
lean_dec_ref(v___x_7123_);
v___x_7125_ = ((size_t)1ULL);
v___x_7126_ = lean_usize_add(v_i_7115_, v___x_7125_);
v_i_7115_ = v___x_7126_;
v_b_7117_ = v_a_7124_;
goto _start;
}
else
{
return v___x_7123_;
}
}
else
{
lean_object* v___x_7128_; 
v___x_7128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7128_, 0, v_b_7117_);
return v___x_7128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_7129_, lean_object* v_i_7130_, lean_object* v_stop_7131_, lean_object* v_b_7132_, lean_object* v___y_7133_, lean_object* v___y_7134_, lean_object* v___y_7135_){
_start:
{
size_t v_i_boxed_7136_; size_t v_stop_boxed_7137_; lean_object* v_res_7138_; 
v_i_boxed_7136_ = lean_unbox_usize(v_i_7130_);
lean_dec(v_i_7130_);
v_stop_boxed_7137_ = lean_unbox_usize(v_stop_7131_);
lean_dec(v_stop_7131_);
v_res_7138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_7129_, v_i_boxed_7136_, v_stop_boxed_7137_, v_b_7132_, v___y_7133_, v___y_7134_);
lean_dec(v___y_7134_);
lean_dec_ref(v___y_7133_);
lean_dec_ref(v_as_7129_);
return v_res_7138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7139_, lean_object* v_a_7140_, lean_object* v_a_7141_){
_start:
{
lean_object* v___x_7143_; lean_object* v___x_7144_; lean_object* v_a_7145_; lean_object* v___x_7147_; uint8_t v_isShared_7148_; uint8_t v_isSharedCheck_7179_; 
v___x_7143_ = lean_st_ref_get(v_a_7141_);
v___x_7144_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7141_);
v_a_7145_ = lean_ctor_get(v___x_7144_, 0);
v_isSharedCheck_7179_ = !lean_is_exclusive(v___x_7144_);
if (v_isSharedCheck_7179_ == 0)
{
v___x_7147_ = v___x_7144_;
v_isShared_7148_ = v_isSharedCheck_7179_;
goto v_resetjp_7146_;
}
else
{
lean_inc(v_a_7145_);
lean_dec(v___x_7144_);
v___x_7147_ = lean_box(0);
v_isShared_7148_ = v_isSharedCheck_7179_;
goto v_resetjp_7146_;
}
v_resetjp_7146_:
{
lean_object* v___x_7149_; lean_object* v_env_7150_; lean_object* v___x_7151_; lean_object* v___y_7158_; lean_object* v___x_7167_; lean_object* v___x_7168_; lean_object* v___x_7169_; uint8_t v___x_7170_; 
v___x_7149_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v_env_7150_ = lean_ctor_get(v___x_7143_, 0);
lean_inc_ref(v_env_7150_);
lean_dec(v___x_7143_);
lean_inc(v___x_7149_);
lean_inc_ref(v_a_7140_);
v___x_7151_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7140_, v_a_7145_, v_env_7150_, v___x_7149_, v_entriesForConst_7139_);
v___x_7167_ = lean_st_ref_get(v___x_7149_);
lean_dec(v___x_7149_);
v___x_7168_ = lean_unsigned_to_nat(0u);
v___x_7169_ = lean_array_get_size(v___x_7167_);
v___x_7170_ = lean_nat_dec_lt(v___x_7168_, v___x_7169_);
if (v___x_7170_ == 0)
{
lean_dec(v___x_7167_);
goto v___jp_7152_;
}
else
{
lean_object* v___x_7171_; uint8_t v___x_7172_; 
v___x_7171_ = lean_box(0);
v___x_7172_ = lean_nat_dec_le(v___x_7169_, v___x_7169_);
if (v___x_7172_ == 0)
{
if (v___x_7170_ == 0)
{
lean_dec(v___x_7167_);
goto v___jp_7152_;
}
else
{
size_t v___x_7173_; size_t v___x_7174_; lean_object* v___x_7175_; 
v___x_7173_ = ((size_t)0ULL);
v___x_7174_ = lean_usize_of_nat(v___x_7169_);
v___x_7175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7167_, v___x_7173_, v___x_7174_, v___x_7171_, v_a_7140_, v_a_7141_);
lean_dec(v___x_7167_);
v___y_7158_ = v___x_7175_;
goto v___jp_7157_;
}
}
else
{
size_t v___x_7176_; size_t v___x_7177_; lean_object* v___x_7178_; 
v___x_7176_ = ((size_t)0ULL);
v___x_7177_ = lean_usize_of_nat(v___x_7169_);
v___x_7178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7167_, v___x_7176_, v___x_7177_, v___x_7171_, v_a_7140_, v_a_7141_);
lean_dec(v___x_7167_);
v___y_7158_ = v___x_7178_;
goto v___jp_7157_;
}
}
v___jp_7152_:
{
lean_object* v___x_7153_; lean_object* v___x_7155_; 
v___x_7153_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7151_);
if (v_isShared_7148_ == 0)
{
lean_ctor_set(v___x_7147_, 0, v___x_7153_);
v___x_7155_ = v___x_7147_;
goto v_reusejp_7154_;
}
else
{
lean_object* v_reuseFailAlloc_7156_; 
v_reuseFailAlloc_7156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7156_, 0, v___x_7153_);
v___x_7155_ = v_reuseFailAlloc_7156_;
goto v_reusejp_7154_;
}
v_reusejp_7154_:
{
return v___x_7155_;
}
}
v___jp_7157_:
{
if (lean_obj_tag(v___y_7158_) == 0)
{
lean_dec_ref(v___y_7158_);
goto v___jp_7152_;
}
else
{
lean_object* v_a_7159_; lean_object* v___x_7161_; uint8_t v_isShared_7162_; uint8_t v_isSharedCheck_7166_; 
lean_dec_ref(v___x_7151_);
lean_del_object(v___x_7147_);
v_a_7159_ = lean_ctor_get(v___y_7158_, 0);
v_isSharedCheck_7166_ = !lean_is_exclusive(v___y_7158_);
if (v_isSharedCheck_7166_ == 0)
{
v___x_7161_ = v___y_7158_;
v_isShared_7162_ = v_isSharedCheck_7166_;
goto v_resetjp_7160_;
}
else
{
lean_inc(v_a_7159_);
lean_dec(v___y_7158_);
v___x_7161_ = lean_box(0);
v_isShared_7162_ = v_isSharedCheck_7166_;
goto v_resetjp_7160_;
}
v_resetjp_7160_:
{
lean_object* v___x_7164_; 
if (v_isShared_7162_ == 0)
{
v___x_7164_ = v___x_7161_;
goto v_reusejp_7163_;
}
else
{
lean_object* v_reuseFailAlloc_7165_; 
v_reuseFailAlloc_7165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7165_, 0, v_a_7159_);
v___x_7164_ = v_reuseFailAlloc_7165_;
goto v_reusejp_7163_;
}
v_reusejp_7163_:
{
return v___x_7164_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7180_, lean_object* v_a_7181_, lean_object* v_a_7182_, lean_object* v_a_7183_){
_start:
{
lean_object* v_res_7184_; 
v_res_7184_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7180_, v_a_7181_, v_a_7182_);
lean_dec(v_a_7182_);
lean_dec_ref(v_a_7181_);
return v_res_7184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7185_, lean_object* v_entriesForConst_7186_, lean_object* v_a_7187_, lean_object* v_a_7188_){
_start:
{
lean_object* v___x_7190_; 
v___x_7190_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7186_, v_a_7187_, v_a_7188_);
return v___x_7190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7191_, lean_object* v_entriesForConst_7192_, lean_object* v_a_7193_, lean_object* v_a_7194_, lean_object* v_a_7195_){
_start:
{
lean_object* v_res_7196_; 
v_res_7196_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7191_, v_entriesForConst_7192_, v_a_7193_, v_a_7194_);
lean_dec(v_a_7194_);
lean_dec_ref(v_a_7193_);
return v_res_7196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7197_, lean_object* v_droppedEntriesRef_7198_, lean_object* v_droppedKeys_7199_, lean_object* v___y_7200_, lean_object* v___y_7201_, lean_object* v___y_7202_, lean_object* v___y_7203_){
_start:
{
lean_object* v_t_7206_; lean_object* v___x_7209_; 
v___x_7209_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7197_, v___y_7202_, v___y_7203_);
if (lean_obj_tag(v___x_7209_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7198_) == 1)
{
lean_object* v_a_7210_; lean_object* v_val_7211_; lean_object* v___x_7213_; uint8_t v_isShared_7214_; uint8_t v_isSharedCheck_7237_; 
v_a_7210_ = lean_ctor_get(v___x_7209_, 0);
lean_inc(v_a_7210_);
lean_dec_ref(v___x_7209_);
v_val_7211_ = lean_ctor_get(v_droppedEntriesRef_7198_, 0);
v_isSharedCheck_7237_ = !lean_is_exclusive(v_droppedEntriesRef_7198_);
if (v_isSharedCheck_7237_ == 0)
{
v___x_7213_ = v_droppedEntriesRef_7198_;
v_isShared_7214_ = v_isSharedCheck_7237_;
goto v_resetjp_7212_;
}
else
{
lean_inc(v_val_7211_);
lean_dec(v_droppedEntriesRef_7198_);
v___x_7213_ = lean_box(0);
v_isShared_7214_ = v_isSharedCheck_7237_;
goto v_resetjp_7212_;
}
v_resetjp_7212_:
{
lean_object* v___x_7215_; 
v___x_7215_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7210_, v_droppedKeys_7199_, v___y_7200_, v___y_7201_, v___y_7202_, v___y_7203_);
if (lean_obj_tag(v___x_7215_) == 0)
{
lean_object* v_a_7216_; lean_object* v_fst_7217_; lean_object* v_snd_7218_; lean_object* v___x_7219_; lean_object* v___y_7221_; 
v_a_7216_ = lean_ctor_get(v___x_7215_, 0);
lean_inc(v_a_7216_);
lean_dec_ref(v___x_7215_);
v_fst_7217_ = lean_ctor_get(v_a_7216_, 0);
lean_inc(v_fst_7217_);
v_snd_7218_ = lean_ctor_get(v_a_7216_, 1);
lean_inc(v_snd_7218_);
lean_dec(v_a_7216_);
v___x_7219_ = lean_st_ref_get(v_val_7211_);
if (lean_obj_tag(v___x_7219_) == 0)
{
lean_object* v___x_7227_; 
v___x_7227_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_7221_ = v___x_7227_;
goto v___jp_7220_;
}
else
{
lean_object* v_val_7228_; 
v_val_7228_ = lean_ctor_get(v___x_7219_, 0);
lean_inc(v_val_7228_);
lean_dec_ref(v___x_7219_);
v___y_7221_ = v_val_7228_;
goto v___jp_7220_;
}
v___jp_7220_:
{
lean_object* v___x_7222_; lean_object* v___x_7224_; 
v___x_7222_ = l_Array_append___redArg(v___y_7221_, v_fst_7217_);
lean_dec(v_fst_7217_);
if (v_isShared_7214_ == 0)
{
lean_ctor_set(v___x_7213_, 0, v___x_7222_);
v___x_7224_ = v___x_7213_;
goto v_reusejp_7223_;
}
else
{
lean_object* v_reuseFailAlloc_7226_; 
v_reuseFailAlloc_7226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7226_, 0, v___x_7222_);
v___x_7224_ = v_reuseFailAlloc_7226_;
goto v_reusejp_7223_;
}
v_reusejp_7223_:
{
lean_object* v___x_7225_; 
v___x_7225_ = lean_st_ref_set(v_val_7211_, v___x_7224_);
lean_dec(v_val_7211_);
v_t_7206_ = v_snd_7218_;
goto v___jp_7205_;
}
}
}
else
{
lean_object* v_a_7229_; lean_object* v___x_7231_; uint8_t v_isShared_7232_; uint8_t v_isSharedCheck_7236_; 
lean_del_object(v___x_7213_);
lean_dec(v_val_7211_);
v_a_7229_ = lean_ctor_get(v___x_7215_, 0);
v_isSharedCheck_7236_ = !lean_is_exclusive(v___x_7215_);
if (v_isSharedCheck_7236_ == 0)
{
v___x_7231_ = v___x_7215_;
v_isShared_7232_ = v_isSharedCheck_7236_;
goto v_resetjp_7230_;
}
else
{
lean_inc(v_a_7229_);
lean_dec(v___x_7215_);
v___x_7231_ = lean_box(0);
v_isShared_7232_ = v_isSharedCheck_7236_;
goto v_resetjp_7230_;
}
v_resetjp_7230_:
{
lean_object* v___x_7234_; 
if (v_isShared_7232_ == 0)
{
v___x_7234_ = v___x_7231_;
goto v_reusejp_7233_;
}
else
{
lean_object* v_reuseFailAlloc_7235_; 
v_reuseFailAlloc_7235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7235_, 0, v_a_7229_);
v___x_7234_ = v_reuseFailAlloc_7235_;
goto v_reusejp_7233_;
}
v_reusejp_7233_:
{
return v___x_7234_;
}
}
}
}
}
else
{
lean_object* v_a_7238_; lean_object* v___x_7239_; 
lean_dec(v_droppedEntriesRef_7198_);
v_a_7238_ = lean_ctor_get(v___x_7209_, 0);
lean_inc(v_a_7238_);
lean_dec_ref(v___x_7209_);
v___x_7239_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7238_, v_droppedKeys_7199_, v___y_7200_, v___y_7201_, v___y_7202_, v___y_7203_);
if (lean_obj_tag(v___x_7239_) == 0)
{
lean_object* v_a_7240_; 
v_a_7240_ = lean_ctor_get(v___x_7239_, 0);
lean_inc(v_a_7240_);
lean_dec_ref(v___x_7239_);
v_t_7206_ = v_a_7240_;
goto v___jp_7205_;
}
else
{
lean_object* v_a_7241_; lean_object* v___x_7243_; uint8_t v_isShared_7244_; uint8_t v_isSharedCheck_7248_; 
v_a_7241_ = lean_ctor_get(v___x_7239_, 0);
v_isSharedCheck_7248_ = !lean_is_exclusive(v___x_7239_);
if (v_isSharedCheck_7248_ == 0)
{
v___x_7243_ = v___x_7239_;
v_isShared_7244_ = v_isSharedCheck_7248_;
goto v_resetjp_7242_;
}
else
{
lean_inc(v_a_7241_);
lean_dec(v___x_7239_);
v___x_7243_ = lean_box(0);
v_isShared_7244_ = v_isSharedCheck_7248_;
goto v_resetjp_7242_;
}
v_resetjp_7242_:
{
lean_object* v___x_7246_; 
if (v_isShared_7244_ == 0)
{
v___x_7246_ = v___x_7243_;
goto v_reusejp_7245_;
}
else
{
lean_object* v_reuseFailAlloc_7247_; 
v_reuseFailAlloc_7247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7247_, 0, v_a_7241_);
v___x_7246_ = v_reuseFailAlloc_7247_;
goto v_reusejp_7245_;
}
v_reusejp_7245_:
{
return v___x_7246_;
}
}
}
}
}
else
{
lean_object* v_a_7249_; lean_object* v___x_7251_; uint8_t v_isShared_7252_; uint8_t v_isSharedCheck_7256_; 
lean_dec(v_droppedKeys_7199_);
lean_dec(v_droppedEntriesRef_7198_);
v_a_7249_ = lean_ctor_get(v___x_7209_, 0);
v_isSharedCheck_7256_ = !lean_is_exclusive(v___x_7209_);
if (v_isSharedCheck_7256_ == 0)
{
v___x_7251_ = v___x_7209_;
v_isShared_7252_ = v_isSharedCheck_7256_;
goto v_resetjp_7250_;
}
else
{
lean_inc(v_a_7249_);
lean_dec(v___x_7209_);
v___x_7251_ = lean_box(0);
v_isShared_7252_ = v_isSharedCheck_7256_;
goto v_resetjp_7250_;
}
v_resetjp_7250_:
{
lean_object* v___x_7254_; 
if (v_isShared_7252_ == 0)
{
v___x_7254_ = v___x_7251_;
goto v_reusejp_7253_;
}
else
{
lean_object* v_reuseFailAlloc_7255_; 
v_reuseFailAlloc_7255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7255_, 0, v_a_7249_);
v___x_7254_ = v_reuseFailAlloc_7255_;
goto v_reusejp_7253_;
}
v_reusejp_7253_:
{
return v___x_7254_;
}
}
}
v___jp_7205_:
{
lean_object* v___x_7207_; lean_object* v___x_7208_; 
v___x_7207_ = lean_st_mk_ref(v_t_7206_);
v___x_7208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7208_, 0, v___x_7207_);
return v___x_7208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7257_, lean_object* v_droppedEntriesRef_7258_, lean_object* v_droppedKeys_7259_, lean_object* v___y_7260_, lean_object* v___y_7261_, lean_object* v___y_7262_, lean_object* v___y_7263_, lean_object* v___y_7264_){
_start:
{
lean_object* v_res_7265_; 
v_res_7265_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7257_, v_droppedEntriesRef_7258_, v_droppedKeys_7259_, v___y_7260_, v___y_7261_, v___y_7262_, v___y_7263_);
lean_dec(v___y_7263_);
lean_dec_ref(v___y_7262_);
lean_dec(v___y_7261_);
lean_dec_ref(v___y_7260_);
return v_res_7265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7267_, lean_object* v_droppedKeys_7268_, lean_object* v_droppedEntriesRef_7269_, lean_object* v_a_7270_, lean_object* v_a_7271_, lean_object* v_a_7272_, lean_object* v_a_7273_){
_start:
{
lean_object* v_options_7275_; lean_object* v___f_7276_; lean_object* v___x_7277_; lean_object* v___x_7278_; lean_object* v___x_7279_; 
v_options_7275_ = lean_ctor_get(v_a_7272_, 2);
v___f_7276_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7276_, 0, v_entriesForConst_7267_);
lean_closure_set(v___f_7276_, 1, v_droppedEntriesRef_7269_);
lean_closure_set(v___f_7276_, 2, v_droppedKeys_7268_);
v___x_7277_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7278_ = lean_box(0);
v___x_7279_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7277_, v_options_7275_, v___f_7276_, v___x_7278_, v_a_7270_, v_a_7271_, v_a_7272_, v_a_7273_);
return v___x_7279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7280_, lean_object* v_droppedKeys_7281_, lean_object* v_droppedEntriesRef_7282_, lean_object* v_a_7283_, lean_object* v_a_7284_, lean_object* v_a_7285_, lean_object* v_a_7286_, lean_object* v_a_7287_){
_start:
{
lean_object* v_res_7288_; 
v_res_7288_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7280_, v_droppedKeys_7281_, v_droppedEntriesRef_7282_, v_a_7283_, v_a_7284_, v_a_7285_, v_a_7286_);
lean_dec(v_a_7286_);
lean_dec_ref(v_a_7285_);
lean_dec(v_a_7284_);
lean_dec_ref(v_a_7283_);
return v_res_7288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7289_, lean_object* v_entriesForConst_7290_, lean_object* v_droppedKeys_7291_, lean_object* v_droppedEntriesRef_7292_, lean_object* v_a_7293_, lean_object* v_a_7294_, lean_object* v_a_7295_, lean_object* v_a_7296_){
_start:
{
lean_object* v___x_7298_; 
v___x_7298_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7290_, v_droppedKeys_7291_, v_droppedEntriesRef_7292_, v_a_7293_, v_a_7294_, v_a_7295_, v_a_7296_);
return v___x_7298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7299_, lean_object* v_entriesForConst_7300_, lean_object* v_droppedKeys_7301_, lean_object* v_droppedEntriesRef_7302_, lean_object* v_a_7303_, lean_object* v_a_7304_, lean_object* v_a_7305_, lean_object* v_a_7306_, lean_object* v_a_7307_){
_start:
{
lean_object* v_res_7308_; 
v_res_7308_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7299_, v_entriesForConst_7300_, v_droppedKeys_7301_, v_droppedEntriesRef_7302_, v_a_7303_, v_a_7304_, v_a_7305_, v_a_7306_);
lean_dec(v_a_7306_);
lean_dec_ref(v_a_7305_);
lean_dec(v_a_7304_);
lean_dec_ref(v_a_7303_);
return v_res_7308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7309_, lean_object* v_ty_7310_, lean_object* v___y_7311_, lean_object* v___y_7312_, lean_object* v___y_7313_, lean_object* v___y_7314_){
_start:
{
lean_object* v___x_7316_; lean_object* v___x_7317_; 
v___x_7316_ = lean_st_ref_get(v_moduleRef_7309_);
v___x_7317_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7316_, v_ty_7310_, v___y_7311_, v___y_7312_, v___y_7313_, v___y_7314_);
if (lean_obj_tag(v___x_7317_) == 0)
{
lean_object* v_a_7318_; lean_object* v___x_7320_; uint8_t v_isShared_7321_; uint8_t v_isSharedCheck_7328_; 
v_a_7318_ = lean_ctor_get(v___x_7317_, 0);
v_isSharedCheck_7328_ = !lean_is_exclusive(v___x_7317_);
if (v_isSharedCheck_7328_ == 0)
{
v___x_7320_ = v___x_7317_;
v_isShared_7321_ = v_isSharedCheck_7328_;
goto v_resetjp_7319_;
}
else
{
lean_inc(v_a_7318_);
lean_dec(v___x_7317_);
v___x_7320_ = lean_box(0);
v_isShared_7321_ = v_isSharedCheck_7328_;
goto v_resetjp_7319_;
}
v_resetjp_7319_:
{
lean_object* v_fst_7322_; lean_object* v_snd_7323_; lean_object* v___x_7324_; lean_object* v___x_7326_; 
v_fst_7322_ = lean_ctor_get(v_a_7318_, 0);
lean_inc(v_fst_7322_);
v_snd_7323_ = lean_ctor_get(v_a_7318_, 1);
lean_inc(v_snd_7323_);
lean_dec(v_a_7318_);
v___x_7324_ = lean_st_ref_set(v_moduleRef_7309_, v_snd_7323_);
if (v_isShared_7321_ == 0)
{
lean_ctor_set(v___x_7320_, 0, v_fst_7322_);
v___x_7326_ = v___x_7320_;
goto v_reusejp_7325_;
}
else
{
lean_object* v_reuseFailAlloc_7327_; 
v_reuseFailAlloc_7327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7327_, 0, v_fst_7322_);
v___x_7326_ = v_reuseFailAlloc_7327_;
goto v_reusejp_7325_;
}
v_reusejp_7325_:
{
return v___x_7326_;
}
}
}
else
{
lean_object* v_a_7329_; lean_object* v___x_7331_; uint8_t v_isShared_7332_; uint8_t v_isSharedCheck_7336_; 
v_a_7329_ = lean_ctor_get(v___x_7317_, 0);
v_isSharedCheck_7336_ = !lean_is_exclusive(v___x_7317_);
if (v_isSharedCheck_7336_ == 0)
{
v___x_7331_ = v___x_7317_;
v_isShared_7332_ = v_isSharedCheck_7336_;
goto v_resetjp_7330_;
}
else
{
lean_inc(v_a_7329_);
lean_dec(v___x_7317_);
v___x_7331_ = lean_box(0);
v_isShared_7332_ = v_isSharedCheck_7336_;
goto v_resetjp_7330_;
}
v_resetjp_7330_:
{
lean_object* v___x_7334_; 
if (v_isShared_7332_ == 0)
{
v___x_7334_ = v___x_7331_;
goto v_reusejp_7333_;
}
else
{
lean_object* v_reuseFailAlloc_7335_; 
v_reuseFailAlloc_7335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7335_, 0, v_a_7329_);
v___x_7334_ = v_reuseFailAlloc_7335_;
goto v_reusejp_7333_;
}
v_reusejp_7333_:
{
return v___x_7334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7337_, lean_object* v_ty_7338_, lean_object* v___y_7339_, lean_object* v___y_7340_, lean_object* v___y_7341_, lean_object* v___y_7342_, lean_object* v___y_7343_){
_start:
{
lean_object* v_res_7344_; 
v_res_7344_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7337_, v_ty_7338_, v___y_7339_, v___y_7340_, v___y_7341_, v___y_7342_);
lean_dec(v___y_7342_);
lean_dec_ref(v___y_7341_);
lean_dec(v___y_7340_);
lean_dec_ref(v___y_7339_);
lean_dec(v_moduleRef_7337_);
return v_res_7344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7346_, lean_object* v_ty_7347_, lean_object* v_a_7348_, lean_object* v_a_7349_, lean_object* v_a_7350_, lean_object* v_a_7351_){
_start:
{
lean_object* v_options_7353_; lean_object* v___f_7354_; lean_object* v___x_7355_; lean_object* v___x_7356_; lean_object* v___x_7357_; 
v_options_7353_ = lean_ctor_get(v_a_7350_, 2);
v___f_7354_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7354_, 0, v_moduleRef_7346_);
lean_closure_set(v___f_7354_, 1, v_ty_7347_);
v___x_7355_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7356_ = lean_box(0);
v___x_7357_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7355_, v_options_7353_, v___f_7354_, v___x_7356_, v_a_7348_, v_a_7349_, v_a_7350_, v_a_7351_);
return v___x_7357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7358_, lean_object* v_ty_7359_, lean_object* v_a_7360_, lean_object* v_a_7361_, lean_object* v_a_7362_, lean_object* v_a_7363_, lean_object* v_a_7364_){
_start:
{
lean_object* v_res_7365_; 
v_res_7365_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7358_, v_ty_7359_, v_a_7360_, v_a_7361_, v_a_7362_, v_a_7363_);
lean_dec(v_a_7363_);
lean_dec_ref(v_a_7362_);
lean_dec(v_a_7361_);
lean_dec_ref(v_a_7360_);
return v_res_7365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7366_, lean_object* v_moduleRef_7367_, lean_object* v_ty_7368_, lean_object* v_a_7369_, lean_object* v_a_7370_, lean_object* v_a_7371_, lean_object* v_a_7372_){
_start:
{
lean_object* v___x_7374_; 
v___x_7374_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7367_, v_ty_7368_, v_a_7369_, v_a_7370_, v_a_7371_, v_a_7372_);
return v___x_7374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7375_, lean_object* v_moduleRef_7376_, lean_object* v_ty_7377_, lean_object* v_a_7378_, lean_object* v_a_7379_, lean_object* v_a_7380_, lean_object* v_a_7381_, lean_object* v_a_7382_){
_start:
{
lean_object* v_res_7383_; 
v_res_7383_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7375_, v_moduleRef_7376_, v_ty_7377_, v_a_7378_, v_a_7379_, v_a_7380_, v_a_7381_);
lean_dec(v_a_7381_);
lean_dec_ref(v_a_7380_);
lean_dec(v_a_7379_);
lean_dec_ref(v_a_7378_);
return v_res_7383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7384_, lean_object* v_j_7385_, size_t v_sz_7386_, size_t v_i_7387_, lean_object* v_bs_7388_){
_start:
{
uint8_t v___x_7389_; 
v___x_7389_ = lean_usize_dec_lt(v_i_7387_, v_sz_7386_);
if (v___x_7389_ == 0)
{
lean_dec(v_j_7385_);
lean_dec(v_adjustResult_7384_);
return v_bs_7388_;
}
else
{
lean_object* v_v_7390_; lean_object* v___x_7391_; lean_object* v_bs_x27_7392_; lean_object* v___x_7393_; size_t v___x_7394_; size_t v___x_7395_; lean_object* v___x_7396_; 
v_v_7390_ = lean_array_uget(v_bs_7388_, v_i_7387_);
v___x_7391_ = lean_unsigned_to_nat(0u);
v_bs_x27_7392_ = lean_array_uset(v_bs_7388_, v_i_7387_, v___x_7391_);
lean_inc(v_adjustResult_7384_);
lean_inc(v_j_7385_);
v___x_7393_ = lean_apply_2(v_adjustResult_7384_, v_j_7385_, v_v_7390_);
v___x_7394_ = ((size_t)1ULL);
v___x_7395_ = lean_usize_add(v_i_7387_, v___x_7394_);
v___x_7396_ = lean_array_uset(v_bs_x27_7392_, v_i_7387_, v___x_7393_);
v_i_7387_ = v___x_7395_;
v_bs_7388_ = v___x_7396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7398_, lean_object* v_j_7399_, lean_object* v_sz_7400_, lean_object* v_i_7401_, lean_object* v_bs_7402_){
_start:
{
size_t v_sz_boxed_7403_; size_t v_i_boxed_7404_; lean_object* v_res_7405_; 
v_sz_boxed_7403_ = lean_unbox_usize(v_sz_7400_);
lean_dec(v_sz_7400_);
v_i_boxed_7404_ = lean_unbox_usize(v_i_7401_);
lean_dec(v_i_7401_);
v_res_7405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7398_, v_j_7399_, v_sz_boxed_7403_, v_i_boxed_7404_, v_bs_7402_);
return v_res_7405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7406_, lean_object* v_j_7407_, lean_object* v_as_7408_, size_t v_i_7409_, size_t v_stop_7410_, lean_object* v_b_7411_){
_start:
{
uint8_t v___x_7412_; 
v___x_7412_ = lean_usize_dec_eq(v_i_7409_, v_stop_7410_);
if (v___x_7412_ == 0)
{
lean_object* v___x_7413_; size_t v_sz_7414_; size_t v___x_7415_; lean_object* v___x_7416_; lean_object* v___x_7417_; size_t v___x_7418_; size_t v___x_7419_; 
v___x_7413_ = lean_array_uget_borrowed(v_as_7408_, v_i_7409_);
v_sz_7414_ = lean_array_size(v___x_7413_);
v___x_7415_ = ((size_t)0ULL);
lean_inc(v___x_7413_);
lean_inc(v_j_7407_);
lean_inc(v_adjustResult_7406_);
v___x_7416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7406_, v_j_7407_, v_sz_7414_, v___x_7415_, v___x_7413_);
v___x_7417_ = l_Array_append___redArg(v_b_7411_, v___x_7416_);
lean_dec_ref(v___x_7416_);
v___x_7418_ = ((size_t)1ULL);
v___x_7419_ = lean_usize_add(v_i_7409_, v___x_7418_);
v_i_7409_ = v___x_7419_;
v_b_7411_ = v___x_7417_;
goto _start;
}
else
{
lean_dec(v_j_7407_);
lean_dec(v_adjustResult_7406_);
return v_b_7411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7421_, lean_object* v_j_7422_, lean_object* v_as_7423_, lean_object* v_i_7424_, lean_object* v_stop_7425_, lean_object* v_b_7426_){
_start:
{
size_t v_i_boxed_7427_; size_t v_stop_boxed_7428_; lean_object* v_res_7429_; 
v_i_boxed_7427_ = lean_unbox_usize(v_i_7424_);
lean_dec(v_i_7424_);
v_stop_boxed_7428_ = lean_unbox_usize(v_stop_7425_);
lean_dec(v_stop_7425_);
v_res_7429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7421_, v_j_7422_, v_as_7423_, v_i_boxed_7427_, v_stop_boxed_7428_, v_b_7426_);
lean_dec_ref(v_as_7423_);
return v_res_7429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7430_, lean_object* v_aa_7431_, lean_object* v_adjustResult_7432_, lean_object* v_n_7433_, lean_object* v_j_7434_, lean_object* v_a_7435_){
_start:
{
lean_object* v_zero_7436_; uint8_t v_isZero_7437_; 
v_zero_7436_ = lean_unsigned_to_nat(0u);
v_isZero_7437_ = lean_nat_dec_eq(v_j_7434_, v_zero_7436_);
if (v_isZero_7437_ == 1)
{
lean_dec(v_j_7434_);
lean_dec(v_adjustResult_7432_);
return v_a_7435_;
}
else
{
lean_object* v_one_7438_; lean_object* v_n_7439_; lean_object* v___x_7440_; lean_object* v___x_7441_; lean_object* v_j_7442_; lean_object* v_b_7443_; lean_object* v___x_7444_; uint8_t v___x_7445_; 
v_one_7438_ = lean_unsigned_to_nat(1u);
v_n_7439_ = lean_nat_sub(v_j_7434_, v_one_7438_);
v___x_7440_ = lean_nat_sub(v_n_7433_, v_j_7434_);
lean_dec(v_j_7434_);
v___x_7441_ = lean_nat_sub(v_n_7430_, v_one_7438_);
v_j_7442_ = lean_nat_sub(v___x_7441_, v___x_7440_);
lean_dec(v___x_7440_);
lean_dec(v___x_7441_);
v_b_7443_ = lean_array_fget_borrowed(v_aa_7431_, v_j_7442_);
v___x_7444_ = lean_array_get_size(v_b_7443_);
v___x_7445_ = lean_nat_dec_lt(v_zero_7436_, v___x_7444_);
if (v___x_7445_ == 0)
{
lean_dec(v_j_7442_);
v_j_7434_ = v_n_7439_;
goto _start;
}
else
{
uint8_t v___x_7447_; 
v___x_7447_ = lean_nat_dec_le(v___x_7444_, v___x_7444_);
if (v___x_7447_ == 0)
{
if (v___x_7445_ == 0)
{
lean_dec(v_j_7442_);
v_j_7434_ = v_n_7439_;
goto _start;
}
else
{
size_t v___x_7449_; size_t v___x_7450_; lean_object* v___x_7451_; 
v___x_7449_ = ((size_t)0ULL);
v___x_7450_ = lean_usize_of_nat(v___x_7444_);
lean_inc(v_adjustResult_7432_);
v___x_7451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7432_, v_j_7442_, v_b_7443_, v___x_7449_, v___x_7450_, v_a_7435_);
v_j_7434_ = v_n_7439_;
v_a_7435_ = v___x_7451_;
goto _start;
}
}
else
{
size_t v___x_7453_; size_t v___x_7454_; lean_object* v___x_7455_; 
v___x_7453_ = ((size_t)0ULL);
v___x_7454_ = lean_usize_of_nat(v___x_7444_);
lean_inc(v_adjustResult_7432_);
v___x_7455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7432_, v_j_7442_, v_b_7443_, v___x_7453_, v___x_7454_, v_a_7435_);
v_j_7434_ = v_n_7439_;
v_a_7435_ = v___x_7455_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7457_, lean_object* v_aa_7458_, lean_object* v_adjustResult_7459_, lean_object* v_n_7460_, lean_object* v_j_7461_, lean_object* v_a_7462_){
_start:
{
lean_object* v_res_7463_; 
v_res_7463_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7457_, v_aa_7458_, v_adjustResult_7459_, v_n_7460_, v_j_7461_, v_a_7462_);
lean_dec(v_n_7460_);
lean_dec_ref(v_aa_7458_);
lean_dec(v_n_7457_);
return v_res_7463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7464_, lean_object* v_adjustResult_7465_, lean_object* v_aa_7466_, lean_object* v_n_7467_, lean_object* v_j_7468_, lean_object* v_a_7469_){
_start:
{
lean_object* v_zero_7470_; uint8_t v_isZero_7471_; 
v_zero_7470_ = lean_unsigned_to_nat(0u);
v_isZero_7471_ = lean_nat_dec_eq(v_j_7468_, v_zero_7470_);
if (v_isZero_7471_ == 1)
{
lean_dec(v_adjustResult_7465_);
return v_a_7469_;
}
else
{
lean_object* v_one_7472_; lean_object* v_n_7473_; lean_object* v___x_7474_; lean_object* v___x_7475_; lean_object* v_j_7476_; lean_object* v_b_7477_; lean_object* v___x_7478_; uint8_t v___x_7479_; 
v_one_7472_ = lean_unsigned_to_nat(1u);
v_n_7473_ = lean_nat_sub(v_j_7468_, v_one_7472_);
v___x_7474_ = lean_nat_sub(v_n_7467_, v_j_7468_);
v___x_7475_ = lean_nat_sub(v_n_7464_, v_one_7472_);
v_j_7476_ = lean_nat_sub(v___x_7475_, v___x_7474_);
lean_dec(v___x_7474_);
lean_dec(v___x_7475_);
v_b_7477_ = lean_array_fget_borrowed(v_aa_7466_, v_j_7476_);
v___x_7478_ = lean_array_get_size(v_b_7477_);
v___x_7479_ = lean_nat_dec_lt(v_zero_7470_, v___x_7478_);
if (v___x_7479_ == 0)
{
lean_object* v___x_7480_; 
lean_dec(v_j_7476_);
v___x_7480_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7464_, v_aa_7466_, v_adjustResult_7465_, v_n_7467_, v_n_7473_, v_a_7469_);
return v___x_7480_;
}
else
{
uint8_t v___x_7481_; 
v___x_7481_ = lean_nat_dec_le(v___x_7478_, v___x_7478_);
if (v___x_7481_ == 0)
{
if (v___x_7479_ == 0)
{
lean_object* v___x_7482_; 
lean_dec(v_j_7476_);
v___x_7482_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7464_, v_aa_7466_, v_adjustResult_7465_, v_n_7467_, v_n_7473_, v_a_7469_);
return v___x_7482_;
}
else
{
size_t v___x_7483_; size_t v___x_7484_; lean_object* v___x_7485_; lean_object* v___x_7486_; 
v___x_7483_ = ((size_t)0ULL);
v___x_7484_ = lean_usize_of_nat(v___x_7478_);
lean_inc(v_adjustResult_7465_);
v___x_7485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7465_, v_j_7476_, v_b_7477_, v___x_7483_, v___x_7484_, v_a_7469_);
v___x_7486_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7464_, v_aa_7466_, v_adjustResult_7465_, v_n_7467_, v_n_7473_, v___x_7485_);
return v___x_7486_;
}
}
else
{
size_t v___x_7487_; size_t v___x_7488_; lean_object* v___x_7489_; lean_object* v___x_7490_; 
v___x_7487_ = ((size_t)0ULL);
v___x_7488_ = lean_usize_of_nat(v___x_7478_);
lean_inc(v_adjustResult_7465_);
v___x_7489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7465_, v_j_7476_, v_b_7477_, v___x_7487_, v___x_7488_, v_a_7469_);
v___x_7490_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7464_, v_aa_7466_, v_adjustResult_7465_, v_n_7467_, v_n_7473_, v___x_7489_);
return v___x_7490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7491_, lean_object* v_adjustResult_7492_, lean_object* v_aa_7493_, lean_object* v_n_7494_, lean_object* v_j_7495_, lean_object* v_a_7496_){
_start:
{
lean_object* v_res_7497_; 
v_res_7497_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7491_, v_adjustResult_7492_, v_aa_7493_, v_n_7494_, v_j_7495_, v_a_7496_);
lean_dec(v_j_7495_);
lean_dec(v_n_7494_);
lean_dec_ref(v_aa_7493_);
lean_dec(v_n_7491_);
return v_res_7497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7498_, lean_object* v_mr_7499_, lean_object* v_a_7500_){
_start:
{
lean_object* v_n_7501_; lean_object* v___x_7502_; 
v_n_7501_ = lean_array_get_size(v_mr_7499_);
v___x_7502_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7501_, v_adjustResult_7498_, v_mr_7499_, v_n_7501_, v_n_7501_, v_a_7500_);
return v___x_7502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7503_, lean_object* v_mr_7504_, lean_object* v_a_7505_){
_start:
{
lean_object* v_res_7506_; 
v_res_7506_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7503_, v_mr_7504_, v_a_7505_);
lean_dec_ref(v_mr_7504_);
return v_res_7506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7507_, lean_object* v_ext_7508_, lean_object* v_addEntry_7509_, lean_object* v_droppedKeys_7510_, lean_object* v_constantsPerTask_7511_, lean_object* v_droppedEntriesRef_7512_, lean_object* v_adjustResult_7513_, lean_object* v_ty_7514_, lean_object* v_a_7515_, lean_object* v_a_7516_, lean_object* v_a_7517_, lean_object* v_a_7518_){
_start:
{
lean_object* v___x_7520_; 
lean_inc_ref(v_ty_7514_);
v___x_7520_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7507_, v_ty_7514_, v_a_7515_, v_a_7516_, v_a_7517_, v_a_7518_);
if (lean_obj_tag(v___x_7520_) == 0)
{
lean_object* v_a_7521_; lean_object* v___x_7522_; 
v_a_7521_ = lean_ctor_get(v___x_7520_, 0);
lean_inc(v_a_7521_);
lean_dec_ref(v___x_7520_);
v___x_7522_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ext_7508_, v_addEntry_7509_, v_droppedKeys_7510_, v_constantsPerTask_7511_, v_droppedEntriesRef_7512_, v_ty_7514_, v_a_7515_, v_a_7516_, v_a_7517_, v_a_7518_);
if (lean_obj_tag(v___x_7522_) == 0)
{
lean_object* v_a_7523_; lean_object* v___x_7525_; uint8_t v_isShared_7526_; uint8_t v_isSharedCheck_7536_; 
v_a_7523_ = lean_ctor_get(v___x_7522_, 0);
v_isSharedCheck_7536_ = !lean_is_exclusive(v___x_7522_);
if (v_isSharedCheck_7536_ == 0)
{
v___x_7525_ = v___x_7522_;
v_isShared_7526_ = v_isSharedCheck_7536_;
goto v_resetjp_7524_;
}
else
{
lean_inc(v_a_7523_);
lean_dec(v___x_7522_);
v___x_7525_ = lean_box(0);
v_isShared_7526_ = v_isSharedCheck_7536_;
goto v_resetjp_7524_;
}
v_resetjp_7524_:
{
lean_object* v___x_7527_; lean_object* v___x_7528_; lean_object* v___x_7529_; lean_object* v___x_7530_; lean_object* v___x_7531_; lean_object* v___x_7532_; lean_object* v___x_7534_; 
v___x_7527_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7521_);
v___x_7528_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7523_);
v___x_7529_ = lean_nat_add(v___x_7527_, v___x_7528_);
lean_dec(v___x_7528_);
lean_dec(v___x_7527_);
v___x_7530_ = lean_mk_empty_array_with_capacity(v___x_7529_);
lean_dec(v___x_7529_);
lean_inc(v_adjustResult_7513_);
v___x_7531_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7513_, v_a_7521_, v___x_7530_);
lean_dec(v_a_7521_);
v___x_7532_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7513_, v_a_7523_, v___x_7531_);
lean_dec(v_a_7523_);
if (v_isShared_7526_ == 0)
{
lean_ctor_set(v___x_7525_, 0, v___x_7532_);
v___x_7534_ = v___x_7525_;
goto v_reusejp_7533_;
}
else
{
lean_object* v_reuseFailAlloc_7535_; 
v_reuseFailAlloc_7535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7535_, 0, v___x_7532_);
v___x_7534_ = v_reuseFailAlloc_7535_;
goto v_reusejp_7533_;
}
v_reusejp_7533_:
{
return v___x_7534_;
}
}
}
else
{
lean_object* v_a_7537_; lean_object* v___x_7539_; uint8_t v_isShared_7540_; uint8_t v_isSharedCheck_7544_; 
lean_dec(v_a_7521_);
lean_dec(v_adjustResult_7513_);
v_a_7537_ = lean_ctor_get(v___x_7522_, 0);
v_isSharedCheck_7544_ = !lean_is_exclusive(v___x_7522_);
if (v_isSharedCheck_7544_ == 0)
{
v___x_7539_ = v___x_7522_;
v_isShared_7540_ = v_isSharedCheck_7544_;
goto v_resetjp_7538_;
}
else
{
lean_inc(v_a_7537_);
lean_dec(v___x_7522_);
v___x_7539_ = lean_box(0);
v_isShared_7540_ = v_isSharedCheck_7544_;
goto v_resetjp_7538_;
}
v_resetjp_7538_:
{
lean_object* v___x_7542_; 
if (v_isShared_7540_ == 0)
{
v___x_7542_ = v___x_7539_;
goto v_reusejp_7541_;
}
else
{
lean_object* v_reuseFailAlloc_7543_; 
v_reuseFailAlloc_7543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7543_, 0, v_a_7537_);
v___x_7542_ = v_reuseFailAlloc_7543_;
goto v_reusejp_7541_;
}
v_reusejp_7541_:
{
return v___x_7542_;
}
}
}
}
else
{
lean_object* v_a_7545_; lean_object* v___x_7547_; uint8_t v_isShared_7548_; uint8_t v_isSharedCheck_7552_; 
lean_dec_ref(v_ty_7514_);
lean_dec(v_adjustResult_7513_);
lean_dec(v_droppedEntriesRef_7512_);
lean_dec(v_constantsPerTask_7511_);
lean_dec(v_droppedKeys_7510_);
lean_dec_ref(v_addEntry_7509_);
v_a_7545_ = lean_ctor_get(v___x_7520_, 0);
v_isSharedCheck_7552_ = !lean_is_exclusive(v___x_7520_);
if (v_isSharedCheck_7552_ == 0)
{
v___x_7547_ = v___x_7520_;
v_isShared_7548_ = v_isSharedCheck_7552_;
goto v_resetjp_7546_;
}
else
{
lean_inc(v_a_7545_);
lean_dec(v___x_7520_);
v___x_7547_ = lean_box(0);
v_isShared_7548_ = v_isSharedCheck_7552_;
goto v_resetjp_7546_;
}
v_resetjp_7546_:
{
lean_object* v___x_7550_; 
if (v_isShared_7548_ == 0)
{
v___x_7550_ = v___x_7547_;
goto v_reusejp_7549_;
}
else
{
lean_object* v_reuseFailAlloc_7551_; 
v_reuseFailAlloc_7551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7551_, 0, v_a_7545_);
v___x_7550_ = v_reuseFailAlloc_7551_;
goto v_reusejp_7549_;
}
v_reusejp_7549_:
{
return v___x_7550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7553_, lean_object* v_ext_7554_, lean_object* v_addEntry_7555_, lean_object* v_droppedKeys_7556_, lean_object* v_constantsPerTask_7557_, lean_object* v_droppedEntriesRef_7558_, lean_object* v_adjustResult_7559_, lean_object* v_ty_7560_, lean_object* v_a_7561_, lean_object* v_a_7562_, lean_object* v_a_7563_, lean_object* v_a_7564_, lean_object* v_a_7565_){
_start:
{
lean_object* v_res_7566_; 
v_res_7566_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7553_, v_ext_7554_, v_addEntry_7555_, v_droppedKeys_7556_, v_constantsPerTask_7557_, v_droppedEntriesRef_7558_, v_adjustResult_7559_, v_ty_7560_, v_a_7561_, v_a_7562_, v_a_7563_, v_a_7564_);
lean_dec(v_a_7564_);
lean_dec_ref(v_a_7563_);
lean_dec(v_a_7562_);
lean_dec_ref(v_a_7561_);
lean_dec_ref(v_ext_7554_);
return v_res_7566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7567_, lean_object* v_00_u03b2_7568_, lean_object* v_moduleTreeRef_7569_, lean_object* v_ext_7570_, lean_object* v_addEntry_7571_, lean_object* v_droppedKeys_7572_, lean_object* v_constantsPerTask_7573_, lean_object* v_droppedEntriesRef_7574_, lean_object* v_adjustResult_7575_, lean_object* v_ty_7576_, lean_object* v_a_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_, lean_object* v_a_7580_){
_start:
{
lean_object* v___x_7582_; 
v___x_7582_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7569_, v_ext_7570_, v_addEntry_7571_, v_droppedKeys_7572_, v_constantsPerTask_7573_, v_droppedEntriesRef_7574_, v_adjustResult_7575_, v_ty_7576_, v_a_7577_, v_a_7578_, v_a_7579_, v_a_7580_);
return v___x_7582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7583_, lean_object* v_00_u03b2_7584_, lean_object* v_moduleTreeRef_7585_, lean_object* v_ext_7586_, lean_object* v_addEntry_7587_, lean_object* v_droppedKeys_7588_, lean_object* v_constantsPerTask_7589_, lean_object* v_droppedEntriesRef_7590_, lean_object* v_adjustResult_7591_, lean_object* v_ty_7592_, lean_object* v_a_7593_, lean_object* v_a_7594_, lean_object* v_a_7595_, lean_object* v_a_7596_, lean_object* v_a_7597_){
_start:
{
lean_object* v_res_7598_; 
v_res_7598_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7583_, v_00_u03b2_7584_, v_moduleTreeRef_7585_, v_ext_7586_, v_addEntry_7587_, v_droppedKeys_7588_, v_constantsPerTask_7589_, v_droppedEntriesRef_7590_, v_adjustResult_7591_, v_ty_7592_, v_a_7593_, v_a_7594_, v_a_7595_, v_a_7596_);
lean_dec(v_a_7596_);
lean_dec_ref(v_a_7595_);
lean_dec(v_a_7594_);
lean_dec_ref(v_a_7593_);
lean_dec_ref(v_ext_7586_);
return v_res_7598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7599_, lean_object* v_00_u03b2_7600_, lean_object* v_adjustResult_7601_, lean_object* v_mr_7602_, lean_object* v_a_7603_){
_start:
{
lean_object* v___x_7604_; 
v___x_7604_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7601_, v_mr_7602_, v_a_7603_);
return v___x_7604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7605_, lean_object* v_00_u03b2_7606_, lean_object* v_adjustResult_7607_, lean_object* v_mr_7608_, lean_object* v_a_7609_){
_start:
{
lean_object* v_res_7610_; 
v_res_7610_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7605_, v_00_u03b2_7606_, v_adjustResult_7607_, v_mr_7608_, v_a_7609_);
lean_dec_ref(v_mr_7608_);
return v_res_7610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7611_, lean_object* v_00_u03b2_7612_, lean_object* v_adjustResult_7613_, lean_object* v_j_7614_, size_t v_sz_7615_, size_t v_i_7616_, lean_object* v_bs_7617_){
_start:
{
lean_object* v___x_7618_; 
v___x_7618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7613_, v_j_7614_, v_sz_7615_, v_i_7616_, v_bs_7617_);
return v___x_7618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7619_, lean_object* v_00_u03b2_7620_, lean_object* v_adjustResult_7621_, lean_object* v_j_7622_, lean_object* v_sz_7623_, lean_object* v_i_7624_, lean_object* v_bs_7625_){
_start:
{
size_t v_sz_boxed_7626_; size_t v_i_boxed_7627_; lean_object* v_res_7628_; 
v_sz_boxed_7626_ = lean_unbox_usize(v_sz_7623_);
lean_dec(v_sz_7623_);
v_i_boxed_7627_ = lean_unbox_usize(v_i_7624_);
lean_dec(v_i_7624_);
v_res_7628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7619_, v_00_u03b2_7620_, v_adjustResult_7621_, v_j_7622_, v_sz_boxed_7626_, v_i_boxed_7627_, v_bs_7625_);
return v_res_7628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7629_, lean_object* v_00_u03b2_7630_, lean_object* v_adjustResult_7631_, lean_object* v_j_7632_, lean_object* v_as_7633_, size_t v_i_7634_, size_t v_stop_7635_, lean_object* v_b_7636_){
_start:
{
lean_object* v___x_7637_; 
v___x_7637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7631_, v_j_7632_, v_as_7633_, v_i_7634_, v_stop_7635_, v_b_7636_);
return v___x_7637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7638_, lean_object* v_00_u03b2_7639_, lean_object* v_adjustResult_7640_, lean_object* v_j_7641_, lean_object* v_as_7642_, lean_object* v_i_7643_, lean_object* v_stop_7644_, lean_object* v_b_7645_){
_start:
{
size_t v_i_boxed_7646_; size_t v_stop_boxed_7647_; lean_object* v_res_7648_; 
v_i_boxed_7646_ = lean_unbox_usize(v_i_7643_);
lean_dec(v_i_7643_);
v_stop_boxed_7647_ = lean_unbox_usize(v_stop_7644_);
lean_dec(v_stop_7644_);
v_res_7648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7638_, v_00_u03b2_7639_, v_adjustResult_7640_, v_j_7641_, v_as_7642_, v_i_boxed_7646_, v_stop_boxed_7647_, v_b_7645_);
lean_dec_ref(v_as_7642_);
return v_res_7648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7649_, lean_object* v_n_7650_, lean_object* v_00_u03b1_7651_, lean_object* v_adjustResult_7652_, lean_object* v_aa_7653_, lean_object* v_n_7654_, lean_object* v_j_7655_, lean_object* v_a_7656_, lean_object* v_a_7657_){
_start:
{
lean_object* v___x_7658_; 
v___x_7658_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7650_, v_adjustResult_7652_, v_aa_7653_, v_n_7654_, v_j_7655_, v_a_7657_);
return v___x_7658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7659_, lean_object* v_n_7660_, lean_object* v_00_u03b1_7661_, lean_object* v_adjustResult_7662_, lean_object* v_aa_7663_, lean_object* v_n_7664_, lean_object* v_j_7665_, lean_object* v_a_7666_, lean_object* v_a_7667_){
_start:
{
lean_object* v_res_7668_; 
v_res_7668_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7659_, v_n_7660_, v_00_u03b1_7661_, v_adjustResult_7662_, v_aa_7663_, v_n_7664_, v_j_7665_, v_a_7666_, v_a_7667_);
lean_dec(v_j_7665_);
lean_dec(v_n_7664_);
lean_dec_ref(v_aa_7663_);
lean_dec(v_n_7660_);
return v_res_7668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7669_, lean_object* v_n_7670_, lean_object* v_00_u03b1_7671_, lean_object* v_aa_7672_, lean_object* v_adjustResult_7673_, lean_object* v_n_7674_, lean_object* v_j_7675_, lean_object* v_a_7676_, lean_object* v_a_7677_){
_start:
{
lean_object* v___x_7678_; 
v___x_7678_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7670_, v_aa_7672_, v_adjustResult_7673_, v_n_7674_, v_j_7675_, v_a_7677_);
return v___x_7678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7679_, lean_object* v_n_7680_, lean_object* v_00_u03b1_7681_, lean_object* v_aa_7682_, lean_object* v_adjustResult_7683_, lean_object* v_n_7684_, lean_object* v_j_7685_, lean_object* v_a_7686_, lean_object* v_a_7687_){
_start:
{
lean_object* v_res_7688_; 
v_res_7688_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7679_, v_n_7680_, v_00_u03b1_7681_, v_aa_7682_, v_adjustResult_7683_, v_n_7684_, v_j_7685_, v_a_7686_, v_a_7687_);
lean_dec(v_n_7684_);
lean_dec_ref(v_aa_7682_);
lean_dec(v_n_7680_);
return v_res_7688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7689_, lean_object* v_v_7690_){
_start:
{
lean_inc(v_v_7690_);
return v_v_7690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7691_, lean_object* v_v_7692_){
_start:
{
lean_object* v_res_7693_; 
v_res_7693_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7691_, v_v_7692_);
lean_dec(v_v_7692_);
lean_dec(v_x_7691_);
return v_res_7693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ext_7695_, lean_object* v_addEntry_7696_, lean_object* v_droppedKeys_7697_, lean_object* v_constantsPerTask_7698_, lean_object* v_droppedEntriesRef_7699_, lean_object* v_ty_7700_, lean_object* v_a_7701_, lean_object* v_a_7702_, lean_object* v_a_7703_, lean_object* v_a_7704_){
_start:
{
lean_object* v___x_7706_; 
lean_inc(v_droppedEntriesRef_7699_);
lean_inc(v_droppedKeys_7697_);
lean_inc_ref(v_addEntry_7696_);
v___x_7706_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7696_, v_droppedKeys_7697_, v_droppedEntriesRef_7699_, v_a_7701_, v_a_7702_, v_a_7703_, v_a_7704_);
if (lean_obj_tag(v___x_7706_) == 0)
{
lean_object* v_a_7707_; lean_object* v___f_7708_; lean_object* v___x_7709_; 
v_a_7707_ = lean_ctor_get(v___x_7706_, 0);
lean_inc(v_a_7707_);
lean_dec_ref(v___x_7706_);
v___f_7708_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7709_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7707_, v_ext_7695_, v_addEntry_7696_, v_droppedKeys_7697_, v_constantsPerTask_7698_, v_droppedEntriesRef_7699_, v___f_7708_, v_ty_7700_, v_a_7701_, v_a_7702_, v_a_7703_, v_a_7704_);
return v___x_7709_;
}
else
{
lean_object* v_a_7710_; lean_object* v___x_7712_; uint8_t v_isShared_7713_; uint8_t v_isSharedCheck_7717_; 
lean_dec_ref(v_ty_7700_);
lean_dec(v_droppedEntriesRef_7699_);
lean_dec(v_constantsPerTask_7698_);
lean_dec(v_droppedKeys_7697_);
lean_dec_ref(v_addEntry_7696_);
v_a_7710_ = lean_ctor_get(v___x_7706_, 0);
v_isSharedCheck_7717_ = !lean_is_exclusive(v___x_7706_);
if (v_isSharedCheck_7717_ == 0)
{
v___x_7712_ = v___x_7706_;
v_isShared_7713_ = v_isSharedCheck_7717_;
goto v_resetjp_7711_;
}
else
{
lean_inc(v_a_7710_);
lean_dec(v___x_7706_);
v___x_7712_ = lean_box(0);
v_isShared_7713_ = v_isSharedCheck_7717_;
goto v_resetjp_7711_;
}
v_resetjp_7711_:
{
lean_object* v___x_7715_; 
if (v_isShared_7713_ == 0)
{
v___x_7715_ = v___x_7712_;
goto v_reusejp_7714_;
}
else
{
lean_object* v_reuseFailAlloc_7716_; 
v_reuseFailAlloc_7716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7716_, 0, v_a_7710_);
v___x_7715_ = v_reuseFailAlloc_7716_;
goto v_reusejp_7714_;
}
v_reusejp_7714_:
{
return v___x_7715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ext_7718_, lean_object* v_addEntry_7719_, lean_object* v_droppedKeys_7720_, lean_object* v_constantsPerTask_7721_, lean_object* v_droppedEntriesRef_7722_, lean_object* v_ty_7723_, lean_object* v_a_7724_, lean_object* v_a_7725_, lean_object* v_a_7726_, lean_object* v_a_7727_, lean_object* v_a_7728_){
_start:
{
lean_object* v_res_7729_; 
v_res_7729_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ext_7718_, v_addEntry_7719_, v_droppedKeys_7720_, v_constantsPerTask_7721_, v_droppedEntriesRef_7722_, v_ty_7723_, v_a_7724_, v_a_7725_, v_a_7726_, v_a_7727_);
lean_dec(v_a_7727_);
lean_dec_ref(v_a_7726_);
lean_dec(v_a_7725_);
lean_dec_ref(v_a_7724_);
lean_dec_ref(v_ext_7718_);
return v_res_7729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7730_, lean_object* v_ext_7731_, lean_object* v_addEntry_7732_, lean_object* v_droppedKeys_7733_, lean_object* v_constantsPerTask_7734_, lean_object* v_droppedEntriesRef_7735_, lean_object* v_ty_7736_, lean_object* v_a_7737_, lean_object* v_a_7738_, lean_object* v_a_7739_, lean_object* v_a_7740_){
_start:
{
lean_object* v___x_7742_; 
v___x_7742_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ext_7731_, v_addEntry_7732_, v_droppedKeys_7733_, v_constantsPerTask_7734_, v_droppedEntriesRef_7735_, v_ty_7736_, v_a_7737_, v_a_7738_, v_a_7739_, v_a_7740_);
return v___x_7742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7743_, lean_object* v_ext_7744_, lean_object* v_addEntry_7745_, lean_object* v_droppedKeys_7746_, lean_object* v_constantsPerTask_7747_, lean_object* v_droppedEntriesRef_7748_, lean_object* v_ty_7749_, lean_object* v_a_7750_, lean_object* v_a_7751_, lean_object* v_a_7752_, lean_object* v_a_7753_, lean_object* v_a_7754_){
_start:
{
lean_object* v_res_7755_; 
v_res_7755_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7743_, v_ext_7744_, v_addEntry_7745_, v_droppedKeys_7746_, v_constantsPerTask_7747_, v_droppedEntriesRef_7748_, v_ty_7749_, v_a_7750_, v_a_7751_, v_a_7752_, v_a_7753_);
lean_dec(v_a_7753_);
lean_dec_ref(v_a_7752_);
lean_dec(v_a_7751_);
lean_dec_ref(v_a_7750_);
lean_dec_ref(v_ext_7744_);
return v_res_7755_;
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
