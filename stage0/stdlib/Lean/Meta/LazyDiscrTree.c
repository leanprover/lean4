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
lean_object* v___y_777_; lean_object* v_fileName_786_; lean_object* v_fileMap_787_; lean_object* v_options_788_; lean_object* v_currRecDepth_789_; lean_object* v_maxRecDepth_790_; lean_object* v_ref_791_; lean_object* v_currNamespace_792_; lean_object* v_openDecls_793_; lean_object* v_initHeartbeats_794_; lean_object* v_maxHeartbeats_795_; lean_object* v_quotContext_796_; lean_object* v_currMacroScope_797_; uint8_t v_diag_798_; lean_object* v_cancelTk_x3f_799_; uint8_t v_suppressElabErrors_800_; lean_object* v_inheritedTraceOptions_801_; uint8_t v___x_802_; 
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
v___x_802_ = lean_nat_dec_eq(v_currRecDepth_789_, v_maxRecDepth_790_);
if (v___x_802_ == 0)
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
else
{
lean_object* v___x_807_; 
lean_dec_ref(v_x_771_);
lean_inc(v_ref_791_);
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
v___x_1231_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0_spec__5___redArg(v___f_1230_, v_a_1219_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc_n(v_a_1232_, 2);
lean_dec_ref(v___x_1231_);
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
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1760_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1760_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1760_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___y_1603_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; 
if (v_root_1578_ == 0)
{
lean_object* v___x_1748_; 
lean_inc(v_a_1598_);
v___x_1748_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1598_);
if (lean_obj_tag(v___x_1748_) == 1)
{
lean_object* v_val_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1759_; 
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_val_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_val_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 2);
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_val_1749_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
}
else
{
lean_dec(v___x_1748_);
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
lean_object* v_mvarId_1625_; lean_object* v___x_1626_; uint8_t v_isDefEqStuckEx_1627_; 
v_mvarId_1625_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_mvarId_1625_);
lean_dec_ref(v___x_1617_);
v___x_1626_ = l_Lean_Meta_Context_config(v___y_1613_);
v_isDefEqStuckEx_1627_ = lean_ctor_get_uint8(v___x_1626_, 4);
lean_dec_ref(v___x_1626_);
if (v_isDefEqStuckEx_1627_ == 0)
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(v_mvarId_1625_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1642_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1642_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1642_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
uint8_t v___x_1633_; 
v___x_1633_ = lean_unbox(v_a_1629_);
lean_dec(v_a_1629_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1634_);
v___x_1636_ = v___x_1631_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1638_);
v___x_1640_ = v___x_1631_;
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
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1628_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1628_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec(v_mvarId_1625_);
v___x_1651_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__2));
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v___x_1617_);
v___x_1653_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
case 4:
{
lean_object* v_declName_1655_; lean_object* v___x_1656_; uint8_t v_isDefEqStuckEx_1657_; 
v_declName_1655_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_declName_1655_);
lean_dec_ref(v___x_1617_);
v___x_1656_ = l_Lean_Meta_Context_config(v___y_1613_);
v_isDefEqStuckEx_1657_ = lean_ctor_get_uint8(v___x_1656_, 4);
lean_dec_ref(v___x_1656_);
if (v_isDefEqStuckEx_1657_ == 0)
{
v___y_1603_ = v_declName_1655_;
goto v___jp_1602_;
}
else
{
uint8_t v___x_1658_; 
v___x_1658_ = l_Lean_Expr_hasExprMVar(v_a_1598_);
if (v___x_1658_ == 0)
{
v___y_1603_ = v_declName_1655_;
goto v___jp_1602_;
}
else
{
lean_object* v___x_1659_; 
lean_inc(v_declName_1655_);
v___x_1659_ = l_Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0(v_declName_1655_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; uint8_t v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref(v___x_1659_);
v___x_1661_ = lean_unbox(v_a_1660_);
lean_dec(v_a_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v_env_1663_; lean_object* v___x_1664_; 
v___x_1662_ = lean_st_ref_get(v___y_1616_);
v_env_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc_ref(v_env_1663_);
lean_dec(v___x_1662_);
v___x_1664_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_1663_, v_a_1598_);
if (lean_obj_tag(v___x_1664_) == 1)
{
lean_object* v_val_1665_; lean_object* v_numDiscrs_1666_; lean_object* v_nargs_1667_; lean_object* v_dummy_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_val_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_val_1665_);
lean_dec_ref(v___x_1664_);
v_numDiscrs_1666_ = lean_ctor_get(v_val_1665_, 1);
lean_inc(v_numDiscrs_1666_);
v_nargs_1667_ = l_Lean_Expr_getAppNumArgs(v_a_1598_);
v_dummy_1668_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta_spec__0_spec__0___lam__1___closed__0);
lean_inc(v_nargs_1667_);
v___x_1669_ = lean_mk_array(v_nargs_1667_, v_dummy_1668_);
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_nat_sub(v_nargs_1667_, v___x_1670_);
lean_dec(v_nargs_1667_);
lean_inc(v_a_1598_);
v___x_1672_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1598_, v___x_1669_, v___x_1671_);
v___x_1673_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_1665_);
lean_dec(v_val_1665_);
v___x_1674_ = lean_nat_add(v___x_1673_, v_numDiscrs_1666_);
lean_dec(v_numDiscrs_1666_);
v___x_1675_ = l_Array_toSubarray___redArg(v___x_1672_, v___x_1673_, v___x_1674_);
v___x_1676_ = lean_box(0);
v___x_1677_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v___x_1675_, v___x_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_dec_ref(v___x_1677_);
v___y_1603_ = v_declName_1655_;
goto v___jp_1602_;
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_declName_1655_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v___x_1686_; lean_object* v_a_1687_; uint8_t v___x_1688_; 
lean_dec(v___x_1664_);
lean_inc(v_declName_1655_);
v___x_1686_ = l_Lean_isRec___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__2___redArg(v_declName_1655_, v___y_1616_);
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = lean_unbox(v_a_1687_);
lean_dec(v_a_1687_);
if (v___x_1688_ == 0)
{
v___y_1603_ = v_declName_1655_;
goto v___jp_1602_;
}
else
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_dec_ref(v___x_1689_);
v___y_1603_ = v_declName_1655_;
goto v___jp_1602_;
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_declName_1655_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
else
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_dec_ref(v___x_1698_);
v___y_1603_ = v_declName_1655_;
goto v___jp_1602_;
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_declName_1655_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
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
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_declName_1655_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_a_1707_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1659_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1659_);
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
case 7:
{
lean_object* v_binderType_1715_; lean_object* v_body_1716_; uint8_t v___x_1717_; 
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_binderType_1715_ = lean_ctor_get(v___x_1617_, 1);
lean_inc_ref(v_binderType_1715_);
v_body_1716_ = lean_ctor_get(v___x_1617_, 2);
lean_inc_ref(v_body_1716_);
lean_dec_ref(v___x_1617_);
v___x_1717_ = l_Lean_Expr_hasLooseBVars(v_body_1716_);
if (v___x_1717_ == 0)
{
v___y_1585_ = v_binderType_1715_;
v_b_1586_ = v_body_1716_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_1716_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1718_);
v___y_1585_ = v_binderType_1715_;
v_b_1586_ = v_a_1719_;
goto v___jp_1584_;
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec_ref(v_binderType_1715_);
v_a_1720_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1718_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1718_);
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
case 9:
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v_a_1728_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_ref(v_a_1728_);
lean_dec_ref(v___x_1617_);
v___x_1729_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_a_1728_);
v___x_1730_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
case 11:
{
lean_object* v_typeName_1733_; lean_object* v_idx_1734_; lean_object* v_struct_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_del_object(v___x_1600_);
v_typeName_1733_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_typeName_1733_);
v_idx_1734_ = lean_ctor_get(v___x_1617_, 1);
lean_inc(v_idx_1734_);
v_struct_1735_ = lean_ctor_get(v___x_1617_, 2);
lean_inc_ref(v_struct_1735_);
lean_dec_ref(v___x_1617_);
v___x_1736_ = l_Lean_Expr_getAppNumArgs(v_a_1598_);
lean_inc(v___x_1736_);
v___x_1737_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_1737_, 0, v_typeName_1733_);
lean_ctor_set(v___x_1737_, 1, v_idx_1734_);
lean_ctor_set(v___x_1737_, 2, v___x_1736_);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_mk_empty_array_with_capacity(v___x_1738_);
v___x_1740_ = lean_array_push(v___x_1739_, v_struct_1735_);
v___x_1741_ = lean_mk_empty_array_with_capacity(v___x_1736_);
lean_dec(v___x_1736_);
v___x_1742_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_1598_, v___x_1741_);
v___x_1743_ = l_Array_append___redArg(v___x_1740_, v___x_1742_);
lean_dec_ref(v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1737_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
default: 
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v___x_1617_);
lean_del_object(v___x_1600_);
lean_dec(v_a_1598_);
v___x_1746_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__1));
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1597_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1597_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___boxed(lean_object* v_e_1769_, lean_object* v_isMatch_1770_, lean_object* v_root_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
uint8_t v_isMatch_boxed_1777_; uint8_t v_root_boxed_1778_; lean_object* v_res_1779_; 
v_isMatch_boxed_1777_ = lean_unbox(v_isMatch_1770_);
v_root_boxed_1778_ = lean_unbox(v_root_1771_);
v_res_1779_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1769_, v_isMatch_boxed_1777_, v_root_boxed_1778_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(lean_object* v_declName_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___redArg(v_declName_1780_, v___y_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0___boxed(lean_object* v_declName_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__0_spec__0(v_declName_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(lean_object* v_inst_1794_, lean_object* v_R_1795_, lean_object* v_a_1796_, lean_object* v_b_1797_, lean_object* v_c_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___redArg(v_a_1796_, v_b_1797_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1___boxed(lean_object* v_inst_1805_, lean_object* v_R_1806_, lean_object* v_a_1807_, lean_object* v_b_1808_, lean_object* v_c_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs_spec__1(v_inst_1805_, v_R_1806_, v_a_1807_, v_b_1808_, v_c_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(lean_object* v_e_1816_, uint8_t v_root_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
uint8_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = 1;
v___x_1824_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_1816_, v___x_1823_, v_root_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs___boxed(lean_object* v_e_1825_, lean_object* v_root_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
uint8_t v_root_boxed_1832_; lean_object* v_res_1833_; 
v_root_boxed_1832_ = lean_unbox(v_root_1826_);
v_res_1833_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getMatchKeyArgs(v_e_1825_, v_root_boxed_1832_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
return v_res_1833_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = lean_box(0);
v___x_1837_ = lean_unsigned_to_nat(16u);
v___x_1838_ = lean_mk_array(v___x_1837_, v___x_1836_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1839_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1842_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_1845_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1843_);
lean_ctor_set(v___x_1845_, 2, v___x_1842_);
lean_ctor_set(v___x_1845_, 3, v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_object* v_a_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__3);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0(void){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default(lean_box(0));
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedTrie(lean_object* v_a_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1853_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_1856_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___x_1854_);
lean_ctor_set(v___x_1856_, 2, v___x_1853_);
lean_ctor_set(v___x_1856_, 3, v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie(lean_object* v_00_u03b1_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1, &l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__1);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
lean_object* v_values_1861_; lean_object* v_star_1862_; lean_object* v_children_1863_; lean_object* v_pending_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1872_; 
v_values_1861_ = lean_ctor_get(v_x_1859_, 0);
v_star_1862_ = lean_ctor_get(v_x_1859_, 1);
v_children_1863_ = lean_ctor_get(v_x_1859_, 2);
v_pending_1864_ = lean_ctor_get(v_x_1859_, 3);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_x_1859_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1866_ = v_x_1859_;
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_pending_1864_);
lean_inc(v_children_1863_);
lean_inc(v_star_1862_);
lean_inc(v_values_1861_);
lean_dec(v_x_1859_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1868_ = lean_array_push(v_pending_1864_, v_x_1860_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 3, v___x_1868_);
v___x_1870_ = v___x_1866_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_values_1861_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_star_1862_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_children_1863_);
lean_ctor_set(v_reuseFailAlloc_1871_, 3, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Trie_pushPending(lean_object* v_00_u03b1_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_x_1874_, v_x_1875_);
return v___x_1876_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1877_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___x_1878_);
v___x_1880_ = lean_array_push(v___x_1879_, v___x_1877_);
return v___x_1880_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_1882_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v___x_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabited(lean_object* v_00_u03b1_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__1);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(lean_object* v_msgData_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v_env_1893_; lean_object* v___x_1894_; lean_object* v_mctx_1895_; lean_object* v_lctx_1896_; lean_object* v_options_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1892_ = lean_st_ref_get(v___y_1890_);
v_env_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc_ref(v_env_1893_);
lean_dec(v___x_1892_);
v___x_1894_ = lean_st_ref_get(v___y_1888_);
v_mctx_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc_ref(v_mctx_1895_);
lean_dec(v___x_1894_);
v_lctx_1896_ = lean_ctor_get(v___y_1887_, 2);
v_options_1897_ = lean_ctor_get(v___y_1889_, 2);
lean_inc_ref(v_options_1897_);
lean_inc_ref(v_lctx_1896_);
v___x_1898_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1898_, 0, v_env_1893_);
lean_ctor_set(v___x_1898_, 1, v_mctx_1895_);
lean_ctor_set(v___x_1898_, 2, v_lctx_1896_);
lean_ctor_set(v___x_1898_, 3, v_options_1897_);
v___x_1899_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v_msgData_1886_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0___boxed(lean_object* v_msgData_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msgData_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(lean_object* v_msg_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_ref_1914_; lean_object* v___x_1915_; lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1924_; 
v_ref_1914_ = lean_ctor_get(v___y_1911_, 5);
v___x_1915_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v_msg_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1924_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_inc(v_ref_1914_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_ref_1914_);
lean_ctor_set(v___x_1920_, 1, v_a_1916_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 1);
lean_ctor_set(v___x_1918_, 0, v___x_1920_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg___boxed(lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1931_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_pushArgs___closed__0));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs(uint8_t v_root_1935_, lean_object* v_todo_1936_, lean_object* v_e_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_1937_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Meta_DiscrTree_reduceDT(v_e_1937_, v_root_1935_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_2084_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_2084_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_2084_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v_v_1950_; lean_object* v___x_1956_; lean_object* v_k_1958_; lean_object* v_nargs_1959_; lean_object* v_todo_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; 
v___x_1956_ = l_Lean_Expr_getAppFn(v_a_1945_);
switch(lean_obj_tag(v___x_1956_))
{
case 9:
{
lean_object* v_a_2003_; 
lean_dec(v_a_1945_);
v_a_2003_ = lean_ctor_get(v___x_1956_, 0);
lean_inc_ref(v_a_2003_);
lean_dec_ref(v___x_1956_);
v_v_1950_ = v_a_2003_;
goto v___jp_1949_;
}
case 4:
{
lean_object* v_declName_2004_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; 
v_declName_2004_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_declName_2004_);
if (v_root_1935_ == 0)
{
lean_object* v___x_2012_; 
lean_inc(v_a_1945_);
v___x_2012_ = l_Lean_Meta_LazyDiscrTree_MatchClone_toNatLit_x3f(v_a_1945_);
if (lean_obj_tag(v___x_2012_) == 1)
{
lean_object* v_val_2013_; 
lean_dec(v_declName_2004_);
lean_dec_ref(v___x_1956_);
lean_dec(v_a_1945_);
v_val_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_val_2013_);
lean_dec_ref(v___x_2012_);
v_v_1950_ = v_val_2013_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_2014_; 
lean_dec(v___x_2012_);
lean_del_object(v___x_1947_);
v___x_2014_ = l_Lean_Meta_LazyDiscrTree_MatchClone_isNatOffset(v_declName_2004_, v_a_1945_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
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
uint8_t v___x_2019_; 
v___x_2019_ = lean_unbox(v_a_2015_);
lean_dec(v_a_2015_);
if (v___x_2019_ == 0)
{
lean_del_object(v___x_2017_);
v___y_2006_ = v_a_1938_;
v___y_2007_ = v_a_1939_;
v___y_2008_ = v_a_1940_;
v___y_2009_ = v_a_1941_;
goto v___jp_2005_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
lean_dec(v_declName_2004_);
lean_dec_ref(v___x_1956_);
lean_dec(v_a_1945_);
v___x_2020_ = lean_box(3);
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v_todo_1936_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2021_);
v___x_2023_ = v___x_2017_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_declName_2004_);
lean_dec_ref(v___x_1956_);
lean_dec(v_a_1945_);
lean_dec_ref(v_todo_1936_);
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
lean_del_object(v___x_1947_);
v___y_2006_ = v_a_1938_;
v___y_2007_ = v_a_1939_;
v___y_2008_ = v_a_1940_;
v___y_2009_ = v_a_1941_;
goto v___jp_2005_;
}
v___jp_2005_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = l_Lean_Expr_getAppNumArgs(v_a_1945_);
lean_inc(v___x_2010_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v_declName_2004_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v_k_1958_ = v___x_2011_;
v_nargs_1959_ = v___x_2010_;
v_todo_1960_ = v_todo_1936_;
v___y_1961_ = v___y_2006_;
v___y_1962_ = v___y_2007_;
v___y_1963_ = v___y_2008_;
v___y_1964_ = v___y_2009_;
goto v___jp_1957_;
}
}
case 11:
{
lean_object* v_typeName_2034_; lean_object* v_idx_2035_; lean_object* v_struct_2036_; lean_object* v___x_2037_; lean_object* v___y_2039_; lean_object* v_env_2043_; uint8_t v___x_2044_; 
lean_del_object(v___x_1947_);
v_typeName_2034_ = lean_ctor_get(v___x_1956_, 0);
lean_inc_n(v_typeName_2034_, 2);
v_idx_2035_ = lean_ctor_get(v___x_1956_, 1);
lean_inc(v_idx_2035_);
v_struct_2036_ = lean_ctor_get(v___x_1956_, 2);
lean_inc_ref(v_struct_2036_);
v___x_2037_ = lean_st_ref_get(v_a_1941_);
v_env_2043_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_ref(v_env_2043_);
lean_dec(v___x_2037_);
v___x_2044_ = lean_is_class(v_env_2043_, v_typeName_2034_);
if (v___x_2044_ == 0)
{
v___y_2039_ = v_struct_2036_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_2036_);
v___y_2039_ = v___x_2045_;
goto v___jp_2038_;
}
v___jp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = l_Lean_Expr_getAppNumArgs(v_a_1945_);
lean_inc(v___x_2040_);
v___x_2041_ = lean_alloc_ctor(6, 3, 0);
lean_ctor_set(v___x_2041_, 0, v_typeName_2034_);
lean_ctor_set(v___x_2041_, 1, v_idx_2035_);
lean_ctor_set(v___x_2041_, 2, v___x_2040_);
v___x_2042_ = lean_array_push(v_todo_1936_, v___y_2039_);
v_k_1958_ = v___x_2041_;
v_nargs_1959_ = v___x_2040_;
v_todo_1960_ = v___x_2042_;
v___y_1961_ = v_a_1938_;
v___y_1962_ = v_a_1939_;
v___y_1963_ = v_a_1940_;
v___y_1964_ = v_a_1941_;
goto v___jp_1957_;
}
}
case 1:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1947_);
lean_dec(v_a_1945_);
v___x_2046_ = lean_box(3);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v_todo_1936_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
return v___x_2048_;
}
case 2:
{
lean_object* v_mvarId_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
lean_del_object(v___x_1947_);
lean_dec(v_a_1945_);
v_mvarId_2049_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_mvarId_2049_);
lean_dec_ref(v___x_1956_);
v___x_2050_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_tmpMVarId));
v___x_2051_ = l_Lean_instBEqMVarId_beq(v_mvarId_2049_, v___x_2050_);
lean_dec(v_mvarId_2049_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref(v_todo_1936_);
v___x_2052_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1, &l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_pushArgs___closed__1);
v___x_2053_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v___x_2052_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_box(3);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v_todo_1936_);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
case 7:
{
lean_object* v_binderType_2057_; lean_object* v_body_2058_; lean_object* v_b_2060_; uint8_t v___x_2070_; 
lean_del_object(v___x_1947_);
lean_dec(v_a_1945_);
v_binderType_2057_ = lean_ctor_get(v___x_1956_, 1);
lean_inc_ref(v_binderType_2057_);
v_body_2058_ = lean_ctor_get(v___x_1956_, 2);
lean_inc_ref(v_body_2058_);
lean_dec_ref(v___x_1956_);
v___x_2070_ = l_Lean_Expr_hasLooseBVars(v_body_2058_);
if (v___x_2070_ == 0)
{
v_b_2060_ = v_body_2058_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Meta_LazyDiscrTree_MatchClone_elimLooseBVarsByBeta(v_body_2058_, v_a_1940_, v_a_1941_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
v_b_2060_ = v_a_2072_;
goto v___jp_2059_;
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v_binderType_2057_);
lean_dec_ref(v_todo_1936_);
v_a_2073_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2071_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2071_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
v___jp_2059_:
{
uint8_t v___x_2061_; 
v___x_2061_ = l_Lean_Expr_hasLooseBVars(v_b_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2062_ = lean_box(5);
v___x_2063_ = lean_array_push(v_todo_1936_, v_binderType_2057_);
v___x_2064_ = lean_array_push(v___x_2063_, v_b_2060_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2062_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
return v___x_2066_;
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec_ref(v_b_2060_);
lean_dec_ref(v_binderType_2057_);
v___x_2067_ = lean_box(4);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v_todo_1936_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
}
default: 
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v___x_1956_);
lean_del_object(v___x_1947_);
lean_dec(v_a_1945_);
v___x_2081_ = lean_box(4);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v_todo_1936_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
v___jp_1949_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1951_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_v_1950_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v_todo_1936_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1952_);
v___x_1954_ = v___x_1947_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
v___jp_1957_:
{
lean_object* v___x_1965_; 
lean_inc(v_nargs_1959_);
v___x_1965_ = l_Lean_Meta_getFunInfoNArgs(v___x_1956_, v_nargs_1959_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v_paramInfo_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1993_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
v_paramInfo_1967_ = lean_ctor_get(v_a_1966_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_a_1966_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; 
v_unused_1994_ = lean_ctor_get(v_a_1966_, 1);
lean_dec(v_unused_1994_);
v___x_1969_ = v_a_1966_;
v_isShared_1970_ = v_isSharedCheck_1993_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_paramInfo_1967_);
lean_dec(v_a_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1993_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_unsigned_to_nat(1u);
v___x_1972_ = lean_nat_sub(v_nargs_1959_, v___x_1971_);
lean_dec(v_nargs_1959_);
v___x_1973_ = l_Lean_Meta_LazyDiscrTree_MatchClone_pushArgsAux(v_paramInfo_1967_, v___x_1972_, v_a_1945_, v_todo_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec_ref(v_paramInfo_1967_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1984_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 1, v_a_1974_);
lean_ctor_set(v___x_1969_, 0, v_k_1958_);
v___x_1979_ = v___x_1969_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_k_1958_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1979_);
v___x_1981_ = v___x_1976_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_del_object(v___x_1969_);
lean_dec(v_k_1958_);
v_a_1985_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1973_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1973_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_todo_1960_);
lean_dec(v_nargs_1959_);
lean_dec(v_k_1958_);
lean_dec(v_a_1945_);
v_a_1995_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1965_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1965_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_todo_1936_);
v_a_2085_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_1944_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_1944_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec_ref(v_e_1937_);
v___x_2093_ = lean_box(3);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v_todo_1936_);
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
return v___x_2095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushArgs___boxed(lean_object* v_root_2096_, lean_object* v_todo_2097_, lean_object* v_e_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
uint8_t v_root_boxed_2104_; lean_object* v_res_2105_; 
v_root_boxed_2104_ = lean_unbox(v_root_2096_);
v_res_2105_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v_root_boxed_2104_, v_todo_2097_, v_e_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(lean_object* v_00_u03b1_2106_, lean_object* v_msg_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___redArg(v_msg_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_msg_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0(v_00_u03b1_2114_, v_msg_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
return v_res_2121_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_initCapacity(void){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_unsigned_to_nat(8u);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey(lean_object* v_e_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
uint8_t v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = 1;
v___x_2130_ = lean_unsigned_to_nat(8u);
v___x_2131_ = lean_mk_empty_array_with_capacity(v___x_2130_);
v___x_2132_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2129_, v___x_2131_, v_e_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_rootKey___boxed(lean_object* v_e_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_e_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath(lean_object* v_op_2140_, uint8_t v_root_2141_, lean_object* v_todo_2142_, lean_object* v_keys_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2149_ = lean_array_get_size(v_todo_2142_);
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2151_ = lean_nat_dec_eq(v___x_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_e_2155_; lean_object* v_todo_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2152_ = l_Lean_instInhabitedExpr;
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = lean_nat_sub(v___x_2149_, v___x_2153_);
v_e_2155_ = lean_array_get(v___x_2152_, v_todo_2142_, v___x_2154_);
lean_dec(v___x_2154_);
v_todo_2156_ = lean_array_pop(v_todo_2142_);
v___x_2157_ = lean_box(v_root_2141_);
lean_inc_ref(v_op_2140_);
lean_inc(v_a_2147_);
lean_inc_ref(v_a_2146_);
lean_inc(v_a_2145_);
lean_inc_ref(v_a_2144_);
v___x_2158_ = lean_apply_8(v_op_2140_, v___x_2157_, v_todo_2156_, v_e_2155_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, lean_box(0));
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v_fst_2160_; lean_object* v_snd_2161_; lean_object* v___x_2162_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref(v___x_2158_);
v_fst_2160_ = lean_ctor_get(v_a_2159_, 0);
lean_inc(v_fst_2160_);
v_snd_2161_ = lean_ctor_get(v_a_2159_, 1);
lean_inc(v_snd_2161_);
lean_dec(v_a_2159_);
v___x_2162_ = lean_array_push(v_keys_2143_, v_fst_2160_);
v_root_2141_ = v___x_2151_;
v_todo_2142_ = v_snd_2161_;
v_keys_2143_ = v___x_2162_;
goto _start;
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_keys_2143_);
lean_dec_ref(v_op_2140_);
v_a_2164_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2158_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2158_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v___x_2172_; 
lean_dec_ref(v_todo_2142_);
lean_dec_ref(v_op_2140_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v_keys_2143_);
return v___x_2172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_buildPath___boxed(lean_object* v_op_2173_, lean_object* v_root_2174_, lean_object* v_todo_2175_, lean_object* v_keys_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
uint8_t v_root_boxed_2182_; lean_object* v_res_2183_; 
v_root_boxed_2182_ = lean_unbox(v_root_2174_);
v_res_2183_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2173_, v_root_boxed_2182_, v_todo_2175_, v_keys_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath(lean_object* v_e_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_op_2191_; lean_object* v___x_2192_; lean_object* v_todo_2193_; uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_op_2191_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_patternPath___closed__0));
v___x_2192_ = lean_unsigned_to_nat(8u);
v_todo_2193_ = lean_mk_empty_array_with_capacity(v___x_2192_);
v___x_2194_ = 1;
lean_inc_ref(v_todo_2193_);
v___x_2195_ = lean_array_push(v_todo_2193_, v_e_2185_);
v___x_2196_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2191_, v___x_2194_, v___x_2195_, v_todo_2193_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_patternPath___boxed(lean_object* v_e_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Meta_LazyDiscrTree_patternPath(v_e_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(uint8_t v_root_2204_, lean_object* v_todo_2205_, lean_object* v_e_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = 1;
v___x_2213_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_2206_, v___x_2212_, v_root_2204_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2231_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2231_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2231_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_fst_2218_; lean_object* v_snd_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2230_; 
v_fst_2218_ = lean_ctor_get(v_a_2214_, 0);
v_snd_2219_ = lean_ctor_get(v_a_2214_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_a_2214_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2221_ = v_a_2214_;
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_snd_2219_);
lean_inc(v_fst_2218_);
lean_dec(v_a_2214_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = l_Array_append___redArg(v_todo_2205_, v_snd_2219_);
lean_dec(v_snd_2219_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v___x_2223_);
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_fst_2218_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2225_);
v___x_2227_ = v___x_2216_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
else
{
lean_dec_ref(v_todo_2205_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___lam__0___boxed(lean_object* v_root_2232_, lean_object* v_todo_2233_, lean_object* v_e_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
uint8_t v_root_boxed_2240_; lean_object* v_res_2241_; 
v_root_boxed_2240_ = lean_unbox(v_root_2232_);
v_res_2241_ = l_Lean_Meta_LazyDiscrTree_targetPath___lam__0(v_root_boxed_2240_, v_todo_2233_, v_e_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath(lean_object* v_e_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_op_2249_; lean_object* v___x_2250_; lean_object* v_todo_2251_; uint8_t v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v_op_2249_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_targetPath___closed__0));
v___x_2250_ = lean_unsigned_to_nat(8u);
v_todo_2251_ = lean_mk_empty_array_with_capacity(v___x_2250_);
v___x_2252_ = 1;
lean_inc_ref(v_todo_2251_);
v___x_2253_ = lean_array_push(v_todo_2251_, v_e_2243_);
v___x_2254_ = l_Lean_Meta_LazyDiscrTree_buildPath(v_op_2249_, v___x_2252_, v___x_2253_, v_todo_2251_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_targetPath___boxed(lean_object* v_e_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_LazyDiscrTree_targetPath(v_e_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
return v_res_2261_;
}
}
static uint64_t _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0(void){
_start:
{
uint8_t v___x_2262_; uint64_t v___x_2263_; 
v___x_2262_ = 2;
v___x_2263_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg(lean_object* v_d_2264_, lean_object* v_m_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_tries_2271_; lean_object* v_roots_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2344_; 
v_tries_2271_ = lean_ctor_get(v_d_2264_, 0);
v_roots_2272_ = lean_ctor_get(v_d_2264_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_d_2264_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2274_ = v_d_2264_;
v_isShared_2275_ = v_isSharedCheck_2344_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_roots_2272_);
lean_inc(v_tries_2271_);
lean_dec(v_d_2264_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2344_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; uint8_t v_foApprox_2277_; uint8_t v_ctxApprox_2278_; uint8_t v_quasiPatternApprox_2279_; uint8_t v_constApprox_2280_; uint8_t v_isDefEqStuckEx_2281_; uint8_t v_unificationHints_2282_; uint8_t v_proofIrrelevance_2283_; uint8_t v_assignSyntheticOpaque_2284_; uint8_t v_offsetCnstrs_2285_; uint8_t v_etaStruct_2286_; uint8_t v_univApprox_2287_; uint8_t v_iota_2288_; uint8_t v_beta_2289_; uint8_t v_proj_2290_; uint8_t v_zeta_2291_; uint8_t v_zetaDelta_2292_; uint8_t v_zetaUnused_2293_; uint8_t v_zetaHave_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2343_; 
v___x_2276_ = l_Lean_Meta_Context_config(v_a_2266_);
v_foApprox_2277_ = lean_ctor_get_uint8(v___x_2276_, 0);
v_ctxApprox_2278_ = lean_ctor_get_uint8(v___x_2276_, 1);
v_quasiPatternApprox_2279_ = lean_ctor_get_uint8(v___x_2276_, 2);
v_constApprox_2280_ = lean_ctor_get_uint8(v___x_2276_, 3);
v_isDefEqStuckEx_2281_ = lean_ctor_get_uint8(v___x_2276_, 4);
v_unificationHints_2282_ = lean_ctor_get_uint8(v___x_2276_, 5);
v_proofIrrelevance_2283_ = lean_ctor_get_uint8(v___x_2276_, 6);
v_assignSyntheticOpaque_2284_ = lean_ctor_get_uint8(v___x_2276_, 7);
v_offsetCnstrs_2285_ = lean_ctor_get_uint8(v___x_2276_, 8);
v_etaStruct_2286_ = lean_ctor_get_uint8(v___x_2276_, 10);
v_univApprox_2287_ = lean_ctor_get_uint8(v___x_2276_, 11);
v_iota_2288_ = lean_ctor_get_uint8(v___x_2276_, 12);
v_beta_2289_ = lean_ctor_get_uint8(v___x_2276_, 13);
v_proj_2290_ = lean_ctor_get_uint8(v___x_2276_, 14);
v_zeta_2291_ = lean_ctor_get_uint8(v___x_2276_, 15);
v_zetaDelta_2292_ = lean_ctor_get_uint8(v___x_2276_, 16);
v_zetaUnused_2293_ = lean_ctor_get_uint8(v___x_2276_, 17);
v_zetaHave_2294_ = lean_ctor_get_uint8(v___x_2276_, 18);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2296_ = v___x_2276_;
v_isShared_2297_ = v_isSharedCheck_2343_;
goto v_resetjp_2295_;
}
else
{
lean_dec(v___x_2276_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2343_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; uint8_t v_trackZetaDelta_2299_; lean_object* v_zetaDeltaSet_2300_; lean_object* v_lctx_2301_; lean_object* v_localInstances_2302_; lean_object* v_defEqCtx_x3f_2303_; lean_object* v_synthPendingDepth_2304_; lean_object* v_canUnfold_x3f_2305_; uint8_t v_univApprox_2306_; uint8_t v_inTypeClassResolution_2307_; uint8_t v_cacheInferType_2308_; uint8_t v___x_2309_; lean_object* v_config_2311_; 
v___x_2298_ = lean_st_mk_ref(v_tries_2271_);
v_trackZetaDelta_2299_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*7);
v_zetaDeltaSet_2300_ = lean_ctor_get(v_a_2266_, 1);
v_lctx_2301_ = lean_ctor_get(v_a_2266_, 2);
v_localInstances_2302_ = lean_ctor_get(v_a_2266_, 3);
v_defEqCtx_x3f_2303_ = lean_ctor_get(v_a_2266_, 4);
v_synthPendingDepth_2304_ = lean_ctor_get(v_a_2266_, 5);
v_canUnfold_x3f_2305_ = lean_ctor_get(v_a_2266_, 6);
v_univApprox_2306_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2307_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*7 + 2);
v_cacheInferType_2308_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*7 + 3);
v___x_2309_ = 2;
if (v_isShared_2297_ == 0)
{
v_config_2311_ = v___x_2296_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 0, v_foApprox_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 1, v_ctxApprox_2278_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 2, v_quasiPatternApprox_2279_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 3, v_constApprox_2280_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 4, v_isDefEqStuckEx_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 5, v_unificationHints_2282_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 6, v_proofIrrelevance_2283_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 7, v_assignSyntheticOpaque_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 8, v_offsetCnstrs_2285_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 10, v_etaStruct_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 11, v_univApprox_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 12, v_iota_2288_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 13, v_beta_2289_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 14, v_proj_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 15, v_zeta_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 16, v_zetaDelta_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 17, v_zetaUnused_2293_);
lean_ctor_set_uint8(v_reuseFailAlloc_2342_, 18, v_zetaHave_2294_);
v_config_2311_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
uint64_t v___x_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; uint64_t v___x_2315_; uint64_t v___x_2316_; uint64_t v_key_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_ctor_set_uint8(v_config_2311_, 9, v___x_2309_);
v___x_2312_ = l_Lean_Meta_Context_configKey(v_a_2266_);
v___x_2313_ = 2ULL;
v___x_2314_ = lean_uint64_shift_right(v___x_2312_, v___x_2313_);
v___x_2315_ = lean_uint64_shift_left(v___x_2314_, v___x_2313_);
v___x_2316_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0);
v_key_2317_ = lean_uint64_lor(v___x_2315_, v___x_2316_);
v___x_2318_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2318_, 0, v_config_2311_);
lean_ctor_set_uint64(v___x_2318_, sizeof(void*)*1, v_key_2317_);
lean_inc(v_canUnfold_x3f_2305_);
lean_inc(v_synthPendingDepth_2304_);
lean_inc(v_defEqCtx_x3f_2303_);
lean_inc_ref(v_localInstances_2302_);
lean_inc_ref(v_lctx_2301_);
lean_inc(v_zetaDeltaSet_2300_);
v___x_2319_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v_zetaDeltaSet_2300_);
lean_ctor_set(v___x_2319_, 2, v_lctx_2301_);
lean_ctor_set(v___x_2319_, 3, v_localInstances_2302_);
lean_ctor_set(v___x_2319_, 4, v_defEqCtx_x3f_2303_);
lean_ctor_set(v___x_2319_, 5, v_synthPendingDepth_2304_);
lean_ctor_set(v___x_2319_, 6, v_canUnfold_x3f_2305_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*7, v_trackZetaDelta_2299_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*7 + 1, v_univApprox_2306_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2307_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*7 + 3, v_cacheInferType_2308_);
lean_inc(v_a_2269_);
lean_inc_ref(v_a_2268_);
lean_inc(v_a_2267_);
lean_inc(v___x_2298_);
v___x_2320_ = lean_apply_6(v_m_2265_, v___x_2298_, v___x_2319_, v_a_2267_, v_a_2268_, v_a_2269_, lean_box(0));
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2333_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2333_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2333_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = lean_st_ref_get(v___x_2298_);
lean_dec(v___x_2298_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2325_);
v___x_2327_ = v___x_2274_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_roots_2272_);
v___x_2327_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2328_, 0, v_a_2321_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2328_);
v___x_2330_ = v___x_2323_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v___x_2298_);
lean_del_object(v___x_2274_);
lean_dec_ref(v_roots_2272_);
v_a_2334_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2320_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2320_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___redArg___boxed(lean_object* v_d_2345_, lean_object* v_m_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2345_, v_m_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch(lean_object* v_00_u03b1_2353_, lean_object* v_00_u03b2_2354_, lean_object* v_d_2355_, lean_object* v_m_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_2355_, v_m_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_runMatch___boxed(lean_object* v_00_u03b1_2363_, lean_object* v_00_u03b2_2364_, lean_object* v_d_2365_, lean_object* v_m_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_Meta_LazyDiscrTree_runMatch(v_00_u03b1_2363_, v_00_u03b2_2364_, v_d_2365_, v_m_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg(lean_object* v_i_2373_, lean_object* v_v_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2377_ = lean_st_ref_take(v_a_2375_);
v___x_2378_ = lean_array_set(v___x_2377_, v_i_2373_, v_v_2374_);
v___x_2379_ = lean_st_ref_set(v_a_2375_, v___x_2378_);
v___x_2380_ = lean_box(0);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___redArg___boxed(lean_object* v_i_2382_, lean_object* v_v_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2382_, v_v_2383_, v_a_2384_);
lean_dec(v_a_2384_);
lean_dec(v_i_2382_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie(lean_object* v_00_u03b1_2387_, lean_object* v_i_2388_, lean_object* v_v_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_i_2388_, v_v_2389_, v_a_2390_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_setTrie___boxed(lean_object* v_00_u03b1_2397_, lean_object* v_i_2398_, lean_object* v_v_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_Meta_LazyDiscrTree_setTrie(v_00_u03b1_2397_, v_i_2398_, v_v_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec(v_i_2398_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0(lean_object* v_e_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_sz_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_sz_2409_ = lean_array_get_size(v_a_2408_);
v___x_2410_ = lean_unsigned_to_nat(0u);
v___x_2411_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2412_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_mk_empty_array_with_capacity(v___x_2413_);
v___x_2415_ = lean_array_push(v___x_2414_, v_e_2407_);
v___x_2416_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2411_);
lean_ctor_set(v___x_2416_, 1, v___x_2410_);
lean_ctor_set(v___x_2416_, 2, v___x_2412_);
lean_ctor_set(v___x_2416_, 3, v___x_2415_);
v___x_2417_ = lean_array_push(v_a_2408_, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v_sz_2409_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___redArg(lean_object* v_inst_2419_, lean_object* v_e_2420_){
_start:
{
lean_object* v_modifyGet_2421_; lean_object* v___f_2422_; lean_object* v___x_2423_; 
v_modifyGet_2421_ = lean_ctor_get(v_inst_2419_, 2);
lean_inc(v_modifyGet_2421_);
lean_dec_ref(v_inst_2419_);
v___f_2422_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_newTrie___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2422_, 0, v_e_2420_);
v___x_2423_ = lean_apply_2(v_modifyGet_2421_, lean_box(0), v___f_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie(lean_object* v_m_2424_, lean_object* v_00_u03b1_2425_, lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_e_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Meta_LazyDiscrTree_newTrie___redArg(v_inst_2427_, v_e_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___boxed(lean_object* v_m_2430_, lean_object* v_00_u03b1_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_e_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_Meta_LazyDiscrTree_newTrie(v_m_2430_, v_00_u03b1_2431_, v_inst_2432_, v_inst_2433_, v_e_2434_);
lean_dec_ref(v_inst_2432_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(lean_object* v_i_2436_, lean_object* v_e_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2440_; lean_object* v_fst_2442_; lean_object* v_snd_2443_; lean_object* v___x_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2440_ = lean_st_ref_take(v_a_2438_);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_array_get_size(v___x_2440_);
v___x_2448_ = lean_nat_dec_lt(v_i_2436_, v___x_2447_);
if (v___x_2448_ == 0)
{
lean_dec_ref(v_e_2437_);
v_fst_2442_ = v___x_2446_;
v_snd_2443_ = v___x_2440_;
goto v___jp_2441_;
}
else
{
lean_object* v_v_2449_; lean_object* v_xs_x27_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_v_2449_ = lean_array_fget(v___x_2440_, v_i_2436_);
v_xs_x27_2450_ = lean_array_fset(v___x_2440_, v_i_2436_, v___x_2446_);
v___x_2451_ = l_Lean_Meta_LazyDiscrTree_Trie_pushPending___redArg(v_v_2449_, v_e_2437_);
v___x_2452_ = lean_array_fset(v_xs_x27_2450_, v_i_2436_, v___x_2451_);
v_fst_2442_ = v___x_2446_;
v_snd_2443_ = v___x_2452_;
goto v___jp_2441_;
}
v___jp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_st_ref_set(v_a_2438_, v_snd_2443_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v_fst_2442_);
return v___x_2445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg___boxed(lean_object* v_i_2453_, lean_object* v_e_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2453_, v_e_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec(v_i_2453_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(lean_object* v_00_u03b1_2458_, lean_object* v_i_2459_, lean_object* v_e_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_i_2459_, v_e_2460_, v_a_2461_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___boxed(lean_object* v_00_u03b1_2468_, lean_object* v_i_2469_, lean_object* v_e_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie(v_00_u03b1_2468_, v_i_2469_, v_e_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec(v_i_2469_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(lean_object* v_x_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v___x_2485_; 
lean_inc(v___y_2479_);
v___x_2485_ = lean_apply_6(v_x_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, lean_box(0));
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed(lean_object* v_x_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0(v_x_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2487_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(lean_object* v_lctx_2494_, lean_object* v_localInsts_2495_, lean_object* v_x_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___f_2503_; lean_object* v___x_2504_; 
lean_inc(v___y_2497_);
v___f_2503_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2503_, 0, v_x_2496_);
lean_closure_set(v___f_2503_, 1, v___y_2497_);
v___x_2504_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_2494_, v_localInsts_2495_, v___f_2503_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
if (lean_obj_tag(v___x_2504_) == 0)
{
return v___x_2504_;
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg___boxed(lean_object* v_lctx_2513_, lean_object* v_localInsts_2514_, lean_object* v_x_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2513_, v_localInsts_2514_, v_x_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(lean_object* v_00_u03b1_2523_, lean_object* v_00_u03b1_2524_, lean_object* v_lctx_2525_, lean_object* v_localInsts_2526_, lean_object* v_x_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_lctx_2525_, v_localInsts_2526_, v_x_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___boxed(lean_object* v_00_u03b1_2535_, lean_object* v_00_u03b1_2536_, lean_object* v_lctx_2537_, lean_object* v_localInsts_2538_, lean_object* v_x_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0(v_00_u03b1_2535_, v_00_u03b1_2536_, v_lctx_2537_, v_localInsts_2538_, v_x_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(lean_object* v_e_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v_sz_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2550_ = lean_st_ref_take(v___y_2548_);
v_sz_2551_ = lean_array_get_size(v___x_2550_);
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_2554_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_2555_ = lean_unsigned_to_nat(1u);
v___x_2556_ = lean_mk_empty_array_with_capacity(v___x_2555_);
v___x_2557_ = lean_array_push(v___x_2556_, v_e_2547_);
v___x_2558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2553_);
lean_ctor_set(v___x_2558_, 1, v___x_2552_);
lean_ctor_set(v___x_2558_, 2, v___x_2554_);
lean_ctor_set(v___x_2558_, 3, v___x_2557_);
v___x_2559_ = lean_array_push(v___x_2550_, v___x_2558_);
v___x_2560_ = lean_st_ref_set(v___y_2548_, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_sz_2551_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg___boxed(lean_object* v_e_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2562_, v___y_2563_);
lean_dec(v___y_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(lean_object* v_00_u03b1_2566_, lean_object* v_e_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v_e_2567_, v___y_2568_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___boxed(lean_object* v_00_u03b1_2575_, lean_object* v_e_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2(v_00_u03b1_2575_, v_e_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(uint8_t v___x_2584_, lean_object* v_todo_2585_, lean_object* v_e_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Meta_LazyDiscrTree_pushArgs(v___x_2584_, v_todo_2585_, v_e_2586_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed(lean_object* v___x_2594_, lean_object* v_todo_2595_, lean_object* v_e_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
uint8_t v___x_4063__boxed_2603_; lean_object* v_res_2604_; 
v___x_4063__boxed_2603_ = lean_unbox(v___x_2594_);
v_res_2604_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0(v___x_4063__boxed_2603_, v_todo_2595_, v_e_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(lean_object* v_a_2605_, lean_object* v_b_2606_, lean_object* v_x_2607_){
_start:
{
if (lean_obj_tag(v_x_2607_) == 0)
{
lean_dec(v_b_2606_);
lean_dec(v_a_2605_);
return v_x_2607_;
}
else
{
lean_object* v_key_2608_; lean_object* v_value_2609_; lean_object* v_tail_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2622_; 
v_key_2608_ = lean_ctor_get(v_x_2607_, 0);
v_value_2609_ = lean_ctor_get(v_x_2607_, 1);
v_tail_2610_ = lean_ctor_get(v_x_2607_, 2);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2612_ = v_x_2607_;
v_isShared_2613_ = v_isSharedCheck_2622_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_tail_2610_);
lean_inc(v_value_2609_);
lean_inc(v_key_2608_);
lean_dec(v_x_2607_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2622_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
uint8_t v___x_2614_; 
v___x_2614_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2608_, v_a_2605_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
v___x_2615_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2605_, v_b_2606_, v_tail_2610_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 2, v___x_2615_);
v___x_2617_ = v___x_2612_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_key_2608_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_value_2609_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
else
{
lean_object* v___x_2620_; 
lean_dec(v_value_2609_);
lean_dec(v_key_2608_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 1, v_b_2606_);
lean_ctor_set(v___x_2612_, 0, v_a_2605_);
v___x_2620_ = v___x_2612_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2605_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_b_2606_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_tail_2610_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(lean_object* v_a_2623_, lean_object* v_x_2624_){
_start:
{
if (lean_obj_tag(v_x_2624_) == 0)
{
uint8_t v___x_2625_; 
v___x_2625_ = 0;
return v___x_2625_;
}
else
{
lean_object* v_key_2626_; lean_object* v_tail_2627_; uint8_t v___x_2628_; 
v_key_2626_ = lean_ctor_get(v_x_2624_, 0);
v_tail_2627_ = lean_ctor_get(v_x_2624_, 2);
v___x_2628_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2626_, v_a_2623_);
if (v___x_2628_ == 0)
{
v_x_2624_ = v_tail_2627_;
goto _start;
}
else
{
return v___x_2628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg___boxed(lean_object* v_a_2630_, lean_object* v_x_2631_){
_start:
{
uint8_t v_res_2632_; lean_object* v_r_2633_; 
v_res_2632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2630_, v_x_2631_);
lean_dec(v_x_2631_);
lean_dec(v_a_2630_);
v_r_2633_ = lean_box(v_res_2632_);
return v_r_2633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_x_2634_, lean_object* v_x_2635_){
_start:
{
if (lean_obj_tag(v_x_2635_) == 0)
{
return v_x_2634_;
}
else
{
lean_object* v_key_2636_; lean_object* v_value_2637_; lean_object* v_tail_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2661_; 
v_key_2636_ = lean_ctor_get(v_x_2635_, 0);
v_value_2637_ = lean_ctor_get(v_x_2635_, 1);
v_tail_2638_ = lean_ctor_get(v_x_2635_, 2);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_x_2635_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2640_ = v_x_2635_;
v_isShared_2641_ = v_isSharedCheck_2661_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_tail_2638_);
lean_inc(v_value_2637_);
lean_inc(v_key_2636_);
lean_dec(v_x_2635_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2661_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; uint64_t v___x_2643_; uint64_t v___x_2644_; uint64_t v___x_2645_; uint64_t v_fold_2646_; uint64_t v___x_2647_; uint64_t v___x_2648_; uint64_t v___x_2649_; size_t v___x_2650_; size_t v___x_2651_; size_t v___x_2652_; size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
v___x_2642_ = lean_array_get_size(v_x_2634_);
v___x_2643_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_key_2636_);
v___x_2644_ = 32ULL;
v___x_2645_ = lean_uint64_shift_right(v___x_2643_, v___x_2644_);
v_fold_2646_ = lean_uint64_xor(v___x_2643_, v___x_2645_);
v___x_2647_ = 16ULL;
v___x_2648_ = lean_uint64_shift_right(v_fold_2646_, v___x_2647_);
v___x_2649_ = lean_uint64_xor(v_fold_2646_, v___x_2648_);
v___x_2650_ = lean_uint64_to_usize(v___x_2649_);
v___x_2651_ = lean_usize_of_nat(v___x_2642_);
v___x_2652_ = ((size_t)1ULL);
v___x_2653_ = lean_usize_sub(v___x_2651_, v___x_2652_);
v___x_2654_ = lean_usize_land(v___x_2650_, v___x_2653_);
v___x_2655_ = lean_array_uget_borrowed(v_x_2634_, v___x_2654_);
lean_inc(v___x_2655_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 2, v___x_2655_);
v___x_2657_ = v___x_2640_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_key_2636_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_value_2637_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_array_uset(v_x_2634_, v___x_2654_, v___x_2657_);
v_x_2634_ = v___x_2658_;
v_x_2635_ = v_tail_2638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(lean_object* v_i_2662_, lean_object* v_source_2663_, lean_object* v_target_2664_){
_start:
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = lean_array_get_size(v_source_2663_);
v___x_2666_ = lean_nat_dec_lt(v_i_2662_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_dec_ref(v_source_2663_);
lean_dec(v_i_2662_);
return v_target_2664_;
}
else
{
lean_object* v_es_2667_; lean_object* v___x_2668_; lean_object* v_source_2669_; lean_object* v_target_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_es_2667_ = lean_array_fget(v_source_2663_, v_i_2662_);
v___x_2668_ = lean_box(0);
v_source_2669_ = lean_array_fset(v_source_2663_, v_i_2662_, v___x_2668_);
v_target_2670_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_target_2664_, v_es_2667_);
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = lean_nat_add(v_i_2662_, v___x_2671_);
lean_dec(v_i_2662_);
v_i_2662_ = v___x_2672_;
v_source_2663_ = v_source_2669_;
v_target_2664_ = v_target_2670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(lean_object* v_data_2674_){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v_nbuckets_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2675_ = lean_array_get_size(v_data_2674_);
v___x_2676_ = lean_unsigned_to_nat(2u);
v_nbuckets_2677_ = lean_nat_mul(v___x_2675_, v___x_2676_);
v___x_2678_ = lean_unsigned_to_nat(0u);
v___x_2679_ = lean_box(0);
v___x_2680_ = lean_mk_array(v_nbuckets_2677_, v___x_2679_);
v___x_2681_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v___x_2678_, v_data_2674_, v___x_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(lean_object* v_m_2682_, lean_object* v_a_2683_, lean_object* v_b_2684_){
_start:
{
lean_object* v_size_2685_; lean_object* v_buckets_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2729_; 
v_size_2685_ = lean_ctor_get(v_m_2682_, 0);
v_buckets_2686_ = lean_ctor_get(v_m_2682_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_m_2682_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2688_ = v_m_2682_;
v_isShared_2689_ = v_isSharedCheck_2729_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_buckets_2686_);
lean_inc(v_size_2685_);
lean_dec(v_m_2682_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2729_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; uint64_t v___x_2691_; uint64_t v___x_2692_; uint64_t v___x_2693_; uint64_t v_fold_2694_; uint64_t v___x_2695_; uint64_t v___x_2696_; uint64_t v___x_2697_; size_t v___x_2698_; size_t v___x_2699_; size_t v___x_2700_; size_t v___x_2701_; size_t v___x_2702_; lean_object* v_bkt_2703_; uint8_t v___x_2704_; 
v___x_2690_ = lean_array_get_size(v_buckets_2686_);
v___x_2691_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2683_);
v___x_2692_ = 32ULL;
v___x_2693_ = lean_uint64_shift_right(v___x_2691_, v___x_2692_);
v_fold_2694_ = lean_uint64_xor(v___x_2691_, v___x_2693_);
v___x_2695_ = 16ULL;
v___x_2696_ = lean_uint64_shift_right(v_fold_2694_, v___x_2695_);
v___x_2697_ = lean_uint64_xor(v_fold_2694_, v___x_2696_);
v___x_2698_ = lean_uint64_to_usize(v___x_2697_);
v___x_2699_ = lean_usize_of_nat(v___x_2690_);
v___x_2700_ = ((size_t)1ULL);
v___x_2701_ = lean_usize_sub(v___x_2699_, v___x_2700_);
v___x_2702_ = lean_usize_land(v___x_2698_, v___x_2701_);
v_bkt_2703_ = lean_array_uget_borrowed(v_buckets_2686_, v___x_2702_);
v___x_2704_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2683_, v_bkt_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; lean_object* v_size_x27_2706_; lean_object* v___x_2707_; lean_object* v_buckets_x27_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2705_ = lean_unsigned_to_nat(1u);
v_size_x27_2706_ = lean_nat_add(v_size_2685_, v___x_2705_);
lean_dec(v_size_2685_);
lean_inc(v_bkt_2703_);
v___x_2707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2707_, 0, v_a_2683_);
lean_ctor_set(v___x_2707_, 1, v_b_2684_);
lean_ctor_set(v___x_2707_, 2, v_bkt_2703_);
v_buckets_x27_2708_ = lean_array_uset(v_buckets_2686_, v___x_2702_, v___x_2707_);
v___x_2709_ = lean_unsigned_to_nat(4u);
v___x_2710_ = lean_nat_mul(v_size_x27_2706_, v___x_2709_);
v___x_2711_ = lean_unsigned_to_nat(3u);
v___x_2712_ = lean_nat_div(v___x_2710_, v___x_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_array_get_size(v_buckets_x27_2708_);
v___x_2714_ = lean_nat_dec_le(v___x_2712_, v___x_2713_);
lean_dec(v___x_2712_);
if (v___x_2714_ == 0)
{
lean_object* v_val_2715_; lean_object* v___x_2717_; 
v_val_2715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_buckets_x27_2708_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v_val_2715_);
lean_ctor_set(v___x_2688_, 0, v_size_x27_2706_);
v___x_2717_ = v___x_2688_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_size_x27_2706_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_val_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
else
{
lean_object* v___x_2720_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v_buckets_x27_2708_);
lean_ctor_set(v___x_2688_, 0, v_size_x27_2706_);
v___x_2720_ = v___x_2688_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_size_x27_2706_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_buckets_x27_2708_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
else
{
lean_object* v___x_2722_; lean_object* v_buckets_x27_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_inc(v_bkt_2703_);
v___x_2722_ = lean_box(0);
v_buckets_x27_2723_ = lean_array_uset(v_buckets_2686_, v___x_2702_, v___x_2722_);
v___x_2724_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2683_, v_b_2684_, v_bkt_2703_);
v___x_2725_ = lean_array_uset(v_buckets_x27_2723_, v___x_2702_, v___x_2724_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v___x_2725_);
v___x_2727_ = v___x_2688_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_size_2685_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(lean_object* v_a_2730_, lean_object* v_x_2731_){
_start:
{
if (lean_obj_tag(v_x_2731_) == 0)
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_box(0);
return v___x_2732_;
}
else
{
lean_object* v_key_2733_; lean_object* v_value_2734_; lean_object* v_tail_2735_; uint8_t v___x_2736_; 
v_key_2733_ = lean_ctor_get(v_x_2731_, 0);
v_value_2734_ = lean_ctor_get(v_x_2731_, 1);
v_tail_2735_ = lean_ctor_get(v_x_2731_, 2);
v___x_2736_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_2733_, v_a_2730_);
if (v___x_2736_ == 0)
{
v_x_2731_ = v_tail_2735_;
goto _start;
}
else
{
lean_object* v___x_2738_; 
lean_inc(v_value_2734_);
v___x_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_value_2734_);
return v___x_2738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg___boxed(lean_object* v_a_2739_, lean_object* v_x_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2739_, v_x_2740_);
lean_dec(v_x_2740_);
lean_dec(v_a_2739_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(lean_object* v_m_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_buckets_2744_; lean_object* v___x_2745_; uint64_t v___x_2746_; uint64_t v___x_2747_; uint64_t v___x_2748_; uint64_t v_fold_2749_; uint64_t v___x_2750_; uint64_t v___x_2751_; uint64_t v___x_2752_; size_t v___x_2753_; size_t v___x_2754_; size_t v___x_2755_; size_t v___x_2756_; size_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_buckets_2744_ = lean_ctor_get(v_m_2742_, 1);
v___x_2745_ = lean_array_get_size(v_buckets_2744_);
v___x_2746_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_2743_);
v___x_2747_ = 32ULL;
v___x_2748_ = lean_uint64_shift_right(v___x_2746_, v___x_2747_);
v_fold_2749_ = lean_uint64_xor(v___x_2746_, v___x_2748_);
v___x_2750_ = 16ULL;
v___x_2751_ = lean_uint64_shift_right(v_fold_2749_, v___x_2750_);
v___x_2752_ = lean_uint64_xor(v_fold_2749_, v___x_2751_);
v___x_2753_ = lean_uint64_to_usize(v___x_2752_);
v___x_2754_ = lean_usize_of_nat(v___x_2745_);
v___x_2755_ = ((size_t)1ULL);
v___x_2756_ = lean_usize_sub(v___x_2754_, v___x_2755_);
v___x_2757_ = lean_usize_land(v___x_2753_, v___x_2756_);
v___x_2758_ = lean_array_uget_borrowed(v_buckets_2744_, v___x_2757_);
v___x_2759_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2743_, v___x_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg___boxed(lean_object* v_m_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2760_, v_a_2761_);
lean_dec(v_a_2761_);
lean_dec_ref(v_m_2760_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(lean_object* v_p_2763_, lean_object* v_entry_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_snd_2771_; lean_object* v_snd_2772_; lean_object* v_fst_2773_; lean_object* v_fst_2774_; lean_object* v_snd_2775_; lean_object* v_fst_2776_; lean_object* v_fst_2777_; lean_object* v_snd_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v_snd_2771_ = lean_ctor_get(v_p_2763_, 1);
v_snd_2772_ = lean_ctor_get(v_entry_2764_, 1);
lean_inc(v_snd_2772_);
v_fst_2773_ = lean_ctor_get(v_p_2763_, 0);
v_fst_2774_ = lean_ctor_get(v_snd_2771_, 0);
v_snd_2775_ = lean_ctor_get(v_snd_2771_, 1);
v_fst_2776_ = lean_ctor_get(v_entry_2764_, 0);
lean_inc(v_fst_2776_);
lean_dec_ref(v_entry_2764_);
v_fst_2777_ = lean_ctor_get(v_snd_2772_, 0);
lean_inc(v_fst_2777_);
v_snd_2778_ = lean_ctor_get(v_snd_2772_, 1);
v___x_2779_ = lean_array_get_size(v_fst_2776_);
v___x_2780_ = lean_unsigned_to_nat(0u);
v___x_2781_ = lean_nat_dec_eq(v___x_2779_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v_fst_2782_; lean_object* v_snd_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2888_; 
v_fst_2782_ = lean_ctor_get(v_fst_2777_, 0);
v_snd_2783_ = lean_ctor_get(v_fst_2777_, 1);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_fst_2777_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2785_ = v_fst_2777_;
v_isShared_2786_ = v_isSharedCheck_2888_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_snd_2783_);
lean_inc(v_fst_2782_);
lean_dec(v_fst_2777_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2888_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v_e_2790_; lean_object* v_todo_2791_; lean_object* v___x_2792_; lean_object* v___f_2793_; lean_object* v___x_2794_; 
v___x_2787_ = l_Lean_instInhabitedExpr;
v___x_2788_ = lean_unsigned_to_nat(1u);
v___x_2789_ = lean_nat_sub(v___x_2779_, v___x_2788_);
v_e_2790_ = lean_array_get(v___x_2787_, v_fst_2776_, v___x_2789_);
lean_dec(v___x_2789_);
v_todo_2791_ = lean_array_pop(v_fst_2776_);
v___x_2792_ = lean_box(v___x_2781_);
v___f_2793_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2793_, 0, v___x_2792_);
lean_closure_set(v___f_2793_, 1, v_todo_2791_);
lean_closure_set(v___f_2793_, 2, v_e_2790_);
v___x_2794_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__0___redArg(v_fst_2782_, v_snd_2783_, v___f_2793_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v_fst_2796_; lean_object* v_snd_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2879_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref(v___x_2794_);
v_fst_2796_ = lean_ctor_get(v_a_2795_, 0);
v_snd_2797_ = lean_ctor_get(v_a_2795_, 1);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_a_2795_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2799_ = v_a_2795_;
v_isShared_2800_ = v_isSharedCheck_2879_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_snd_2797_);
lean_inc(v_fst_2796_);
lean_dec(v_a_2795_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2879_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2801_ = lean_box(3);
v___x_2802_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_fst_2796_, v___x_2801_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_2775_, v_fst_2796_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v___x_2805_; 
lean_inc(v_snd_2775_);
lean_inc(v_fst_2774_);
lean_inc(v_fst_2773_);
lean_dec_ref(v_p_2763_);
lean_inc(v_snd_2772_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 1, v_snd_2772_);
lean_ctor_set(v___x_2799_, 0, v_snd_2797_);
v___x_2805_ = v___x_2799_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_snd_2797_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_snd_2772_);
v___x_2805_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2825_; 
v_isSharedCheck_2825_ = !lean_is_exclusive(v_snd_2772_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; lean_object* v_unused_2827_; 
v_unused_2826_ = lean_ctor_get(v_snd_2772_, 1);
lean_dec(v_unused_2826_);
v_unused_2827_ = lean_ctor_get(v_snd_2772_, 0);
lean_dec(v_unused_2827_);
v___x_2807_ = v_snd_2772_;
v_isShared_2808_ = v_isSharedCheck_2825_;
goto v_resetjp_2806_;
}
else
{
lean_dec(v_snd_2772_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2825_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2824_; 
v___x_2809_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2805_, v_a_2765_);
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2824_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2824_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2816_; 
v___x_2814_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_snd_2775_, v_fst_2796_, v_a_2810_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v___x_2814_);
lean_ctor_set(v___x_2785_, 0, v_fst_2774_);
v___x_2816_ = v___x_2785_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_fst_2774_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
lean_object* v___x_2818_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 1, v___x_2816_);
lean_ctor_set(v___x_2807_, 0, v_fst_2773_);
v___x_2818_ = v___x_2807_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_fst_2773_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2816_);
v___x_2818_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2818_);
v___x_2820_ = v___x_2812_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2829_; lean_object* v___x_2831_; 
lean_dec(v_fst_2796_);
lean_del_object(v___x_2785_);
v_val_2829_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_val_2829_);
lean_dec_ref(v___x_2803_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 1, v_snd_2772_);
lean_ctor_set(v___x_2799_, 0, v_snd_2797_);
v___x_2831_ = v___x_2799_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_snd_2797_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_snd_2772_);
v___x_2831_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v___x_2832_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_val_2829_, v___x_2831_, v_a_2765_);
lean_dec(v_val_2829_);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v___x_2832_, 0);
lean_dec(v_unused_2840_);
v___x_2834_ = v___x_2832_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_dec(v___x_2832_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v_p_2763_);
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_p_2763_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
else
{
uint8_t v___x_2842_; 
lean_dec(v_fst_2796_);
v___x_2842_ = lean_nat_dec_eq(v_fst_2774_, v___x_2780_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2844_; 
lean_del_object(v___x_2785_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 1, v_snd_2772_);
lean_ctor_set(v___x_2799_, 0, v_snd_2797_);
v___x_2844_ = v___x_2799_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_snd_2797_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_snd_2772_);
v___x_2844_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v___x_2845_ = l_Lean_Meta_LazyDiscrTree_addLazyEntryToTrie___redArg(v_fst_2774_, v___x_2844_, v_a_2765_);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; 
v_unused_2853_ = lean_ctor_get(v___x_2845_, 0);
lean_dec(v_unused_2853_);
v___x_2847_ = v___x_2845_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_dec(v___x_2845_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v_p_2763_);
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_p_2763_);
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
else
{
lean_object* v___x_2856_; 
lean_inc(v_snd_2775_);
lean_inc(v_fst_2773_);
lean_dec_ref(v_p_2763_);
lean_inc(v_snd_2772_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 1, v_snd_2772_);
lean_ctor_set(v___x_2799_, 0, v_snd_2797_);
v___x_2856_ = v___x_2799_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_snd_2797_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_snd_2772_);
v___x_2856_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2875_; 
v_isSharedCheck_2875_ = !lean_is_exclusive(v_snd_2772_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; lean_object* v_unused_2877_; 
v_unused_2876_ = lean_ctor_get(v_snd_2772_, 1);
lean_dec(v_unused_2876_);
v_unused_2877_ = lean_ctor_get(v_snd_2772_, 0);
lean_dec(v_unused_2877_);
v___x_2858_ = v_snd_2772_;
v_isShared_2859_ = v_isSharedCheck_2875_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v_snd_2772_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2875_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2874_; 
v___x_2860_ = l_Lean_Meta_LazyDiscrTree_newTrie___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__2___redArg(v___x_2856_, v_a_2765_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2874_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2874_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v_snd_2775_);
lean_ctor_set(v___x_2785_, 0, v_a_2861_);
v___x_2866_ = v___x_2785_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2861_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_snd_2775_);
v___x_2866_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2868_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v___x_2866_);
lean_ctor_set(v___x_2858_, 0, v_fst_2773_);
v___x_2868_ = v___x_2858_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_fst_2773_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2868_);
v___x_2870_ = v___x_2863_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
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
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_del_object(v___x_2785_);
lean_dec(v_snd_2772_);
lean_dec_ref(v_p_2763_);
v_a_2880_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2794_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2794_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
else
{
lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2897_; 
lean_inc(v_snd_2778_);
lean_inc(v_fst_2773_);
lean_inc(v_snd_2771_);
lean_dec(v_fst_2777_);
lean_dec(v_fst_2776_);
lean_dec_ref(v_p_2763_);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_snd_2772_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; lean_object* v_unused_2899_; 
v_unused_2898_ = lean_ctor_get(v_snd_2772_, 1);
lean_dec(v_unused_2898_);
v_unused_2899_ = lean_ctor_get(v_snd_2772_, 0);
lean_dec(v_unused_2899_);
v___x_2890_ = v_snd_2772_;
v_isShared_2891_ = v_isSharedCheck_2897_;
goto v_resetjp_2889_;
}
else
{
lean_dec(v_snd_2772_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2897_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v_values_2892_; lean_object* v___x_2894_; 
v_values_2892_ = lean_array_push(v_fst_2773_, v_snd_2778_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 1, v_snd_2771_);
lean_ctor_set(v___x_2890_, 0, v_values_2892_);
v___x_2894_ = v___x_2890_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_values_2892_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_snd_2771_);
v___x_2894_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg___boxed(lean_object* v_p_2900_, lean_object* v_entry_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2900_, v_entry_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry(lean_object* v_00_u03b1_2909_, lean_object* v_p_2910_, lean_object* v_entry_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_p_2910_, v_entry_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntry___boxed(lean_object* v_00_u03b1_2919_, lean_object* v_p_2920_, lean_object* v_entry_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry(v_00_u03b1_2919_, v_p_2920_, v_entry_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2922_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(lean_object* v_00_u03b2_2929_, lean_object* v_m_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_m_2930_, v_a_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___boxed(lean_object* v_00_u03b2_2933_, lean_object* v_m_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1(v_00_u03b2_2933_, v_m_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_m_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3(lean_object* v_00_u03b2_2937_, lean_object* v_m_2938_, lean_object* v_a_2939_, lean_object* v_b_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_m_2938_, v_a_2939_, v_b_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(lean_object* v_00_u03b2_2942_, lean_object* v_a_2943_, lean_object* v_x_2944_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___redArg(v_a_2943_, v_x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2946_, lean_object* v_a_2947_, lean_object* v_x_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1_spec__1(v_00_u03b2_2946_, v_a_2947_, v_x_2948_);
lean_dec(v_x_2948_);
lean_dec(v_a_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(lean_object* v_00_u03b2_2950_, lean_object* v_a_2951_, lean_object* v_x_2952_){
_start:
{
uint8_t v___x_2953_; 
v___x_2953_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___redArg(v_a_2951_, v_x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2954_, lean_object* v_a_2955_, lean_object* v_x_2956_){
_start:
{
uint8_t v_res_2957_; lean_object* v_r_2958_; 
v_res_2957_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__4(v_00_u03b2_2954_, v_a_2955_, v_x_2956_);
lean_dec(v_x_2956_);
lean_dec(v_a_2955_);
v_r_2958_ = lean_box(v_res_2957_);
return v_r_2958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5(lean_object* v_00_u03b2_2959_, lean_object* v_data_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5___redArg(v_data_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6(lean_object* v_00_u03b2_2962_, lean_object* v_a_2963_, lean_object* v_b_2964_, lean_object* v_x_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__6___redArg(v_a_2963_, v_b_2964_, v_x_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_2967_, lean_object* v_i_2968_, lean_object* v_source_2969_, lean_object* v_target_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6___redArg(v_i_2968_, v_source_2969_, v_target_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3_spec__5_spec__6_spec__7___redArg(v_x_2973_, v_x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(lean_object* v_as_2976_, size_t v_i_2977_, size_t v_stop_2978_, lean_object* v_b_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
uint8_t v___x_2986_; 
v___x_2986_ = lean_usize_dec_eq(v_i_2977_, v_stop_2978_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_array_uget_borrowed(v_as_2976_, v_i_2977_);
lean_inc(v___x_2987_);
v___x_2988_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntry___redArg(v_b_2979_, v___x_2987_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; size_t v___x_2990_; size_t v___x_2991_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref(v___x_2988_);
v___x_2990_ = ((size_t)1ULL);
v___x_2991_ = lean_usize_add(v_i_2977_, v___x_2990_);
v_i_2977_ = v___x_2991_;
v_b_2979_ = v_a_2989_;
goto _start;
}
else
{
return v___x_2988_;
}
}
else
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v_b_2979_);
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg___boxed(lean_object* v_as_2994_, lean_object* v_i_2995_, lean_object* v_stop_2996_, lean_object* v_b_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
size_t v_i_boxed_3004_; size_t v_stop_boxed_3005_; lean_object* v_res_3006_; 
v_i_boxed_3004_ = lean_unbox_usize(v_i_2995_);
lean_dec(v_i_2995_);
v_stop_boxed_3005_ = lean_unbox_usize(v_stop_2996_);
lean_dec(v_stop_2996_);
v_res_3006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_2994_, v_i_boxed_3004_, v_stop_boxed_3005_, v_b_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v_as_2994_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(lean_object* v_values_3007_, lean_object* v_starIdx_3008_, lean_object* v_children_3009_, lean_object* v_entries_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v_starIdx_3008_);
lean_ctor_set(v___x_3017_, 1, v_children_3009_);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v_values_3007_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_unsigned_to_nat(0u);
v___x_3020_ = lean_array_get_size(v_entries_3010_);
v___x_3021_ = lean_nat_dec_lt(v___x_3019_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3018_);
return v___x_3022_;
}
else
{
uint8_t v___x_3023_; 
v___x_3023_ = lean_nat_dec_le(v___x_3020_, v___x_3020_);
if (v___x_3023_ == 0)
{
if (v___x_3021_ == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3018_);
return v___x_3024_;
}
else
{
size_t v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = ((size_t)0ULL);
v___x_3026_ = lean_usize_of_nat(v___x_3020_);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3010_, v___x_3025_, v___x_3026_, v___x_3018_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
return v___x_3027_;
}
}
else
{
size_t v___x_3028_; size_t v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = ((size_t)0ULL);
v___x_3029_ = lean_usize_of_nat(v___x_3020_);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_entries_3010_, v___x_3028_, v___x_3029_, v___x_3018_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
return v___x_3030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg___boxed(lean_object* v_values_3031_, lean_object* v_starIdx_3032_, lean_object* v_children_3033_, lean_object* v_entries_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3031_, v_starIdx_3032_, v_children_3033_, v_entries_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_entries_3034_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries(lean_object* v_00_u03b1_3042_, lean_object* v_values_3043_, lean_object* v_starIdx_3044_, lean_object* v_children_3045_, lean_object* v_entries_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3043_, v_starIdx_3044_, v_children_3045_, v_entries_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalLazyEntries___boxed(lean_object* v_00_u03b1_3054_, lean_object* v_values_3055_, lean_object* v_starIdx_3056_, lean_object* v_children_3057_, lean_object* v_entries_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries(v_00_u03b1_3054_, v_values_3055_, v_starIdx_3056_, v_children_3057_, v_entries_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_entries_3058_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(lean_object* v_00_u03b1_3066_, lean_object* v_as_3067_, size_t v_i_3068_, size_t v_stop_3069_, lean_object* v_b_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___redArg(v_as_3067_, v_i_3068_, v_stop_3069_, v_b_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0___boxed(lean_object* v_00_u03b1_3078_, lean_object* v_as_3079_, lean_object* v_i_3080_, lean_object* v_stop_3081_, lean_object* v_b_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
size_t v_i_boxed_3089_; size_t v_stop_boxed_3090_; lean_object* v_res_3091_; 
v_i_boxed_3089_ = lean_unbox_usize(v_i_3080_);
lean_dec(v_i_3080_);
v_stop_boxed_3090_ = lean_unbox_usize(v_stop_3081_);
lean_dec(v_stop_3081_);
v_res_3091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_evalLazyEntries_spec__0(v_00_u03b1_3078_, v_as_3079_, v_i_boxed_3089_, v_stop_boxed_3090_, v_b_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v_as_3079_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg(lean_object* v_c_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_values_3104_; lean_object* v_star_3105_; lean_object* v_children_3106_; lean_object* v_pending_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3137_; 
v___x_3101_ = lean_st_ref_get(v_a_3095_);
v___x_3102_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie___closed__0);
v___x_3103_ = lean_array_get(v___x_3102_, v___x_3101_, v_c_3094_);
lean_dec(v___x_3101_);
v_values_3104_ = lean_ctor_get(v___x_3103_, 0);
v_star_3105_ = lean_ctor_get(v___x_3103_, 1);
v_children_3106_ = lean_ctor_get(v___x_3103_, 2);
v_pending_3107_ = lean_ctor_get(v___x_3103_, 3);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3109_ = v___x_3103_;
v_isShared_3110_ = v_isSharedCheck_3137_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_pending_3107_);
lean_inc(v_children_3106_);
lean_inc(v_star_3105_);
lean_inc(v_values_3104_);
lean_dec(v___x_3103_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3137_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3111_ = lean_array_get_size(v_pending_3107_);
v___x_3112_ = lean_unsigned_to_nat(0u);
v___x_3113_ = lean_nat_dec_eq(v___x_3111_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3094_, v___x_3102_, v_a_3095_);
lean_dec_ref(v___x_3114_);
v___x_3115_ = l_Lean_Meta_LazyDiscrTree_evalLazyEntries___redArg(v_values_3104_, v_star_3105_, v_children_3106_, v_pending_3107_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec_ref(v_pending_3107_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v_snd_3117_; lean_object* v_fst_3118_; lean_object* v_fst_3119_; lean_object* v_snd_3120_; lean_object* v___x_3121_; lean_object* v___x_3123_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref(v___x_3115_);
v_snd_3117_ = lean_ctor_get(v_a_3116_, 1);
v_fst_3118_ = lean_ctor_get(v_a_3116_, 0);
v_fst_3119_ = lean_ctor_get(v_snd_3117_, 0);
v_snd_3120_ = lean_ctor_get(v_snd_3117_, 1);
v___x_3121_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_evalNode___redArg___closed__0));
lean_inc(v_snd_3120_);
lean_inc(v_fst_3119_);
lean_inc(v_fst_3118_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 3, v___x_3121_);
lean_ctor_set(v___x_3109_, 2, v_snd_3120_);
lean_ctor_set(v___x_3109_, 1, v_fst_3119_);
lean_ctor_set(v___x_3109_, 0, v_fst_3118_);
v___x_3123_ = v___x_3109_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_fst_3118_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v_fst_3119_);
lean_ctor_set(v_reuseFailAlloc_3133_, 2, v_snd_3120_);
lean_ctor_set(v_reuseFailAlloc_3133_, 3, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
v___x_3124_ = l_Lean_Meta_LazyDiscrTree_setTrie___redArg(v_c_3094_, v___x_3123_, v_a_3095_);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v___x_3124_, 0);
lean_dec(v_unused_3132_);
v___x_3126_ = v___x_3124_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_dec(v___x_3124_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v_a_3116_);
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3116_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_del_object(v___x_3109_);
return v___x_3115_;
}
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_del_object(v___x_3109_);
lean_dec_ref(v_pending_3107_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v_star_3105_);
lean_ctor_set(v___x_3134_, 1, v_children_3106_);
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_values_3104_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___redArg___boxed(lean_object* v_c_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
lean_dec(v_a_3143_);
lean_dec_ref(v_a_3142_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_a_3139_);
lean_dec(v_c_3138_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode(lean_object* v_00_u03b1_3146_, lean_object* v_c_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3154_; 
v___x_3154_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_evalNode___boxed(lean_object* v_00_u03b1_3155_, lean_object* v_c_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_Meta_LazyDiscrTree_evalNode(v_00_u03b1_3155_, v_c_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec(v_c_3156_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(lean_object* v_a_3164_, lean_object* v_fallback_3165_, lean_object* v_x_3166_){
_start:
{
if (lean_obj_tag(v_x_3166_) == 0)
{
lean_inc(v_fallback_3165_);
return v_fallback_3165_;
}
else
{
lean_object* v_key_3167_; lean_object* v_value_3168_; lean_object* v_tail_3169_; uint8_t v___x_3170_; 
v_key_3167_ = lean_ctor_get(v_x_3166_, 0);
v_value_3168_ = lean_ctor_get(v_x_3166_, 1);
v_tail_3169_ = lean_ctor_get(v_x_3166_, 2);
v___x_3170_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_3167_, v_a_3164_);
if (v___x_3170_ == 0)
{
v_x_3166_ = v_tail_3169_;
goto _start;
}
else
{
lean_inc(v_value_3168_);
return v_value_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3172_, lean_object* v_fallback_3173_, lean_object* v_x_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3172_, v_fallback_3173_, v_x_3174_);
lean_dec(v_x_3174_);
lean_dec(v_fallback_3173_);
lean_dec(v_a_3172_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(lean_object* v_m_3176_, lean_object* v_a_3177_, lean_object* v_fallback_3178_){
_start:
{
lean_object* v_buckets_3179_; lean_object* v___x_3180_; uint64_t v___x_3181_; uint64_t v___x_3182_; uint64_t v___x_3183_; uint64_t v_fold_3184_; uint64_t v___x_3185_; uint64_t v___x_3186_; uint64_t v___x_3187_; size_t v___x_3188_; size_t v___x_3189_; size_t v___x_3190_; size_t v___x_3191_; size_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_buckets_3179_ = lean_ctor_get(v_m_3176_, 1);
v___x_3180_ = lean_array_get_size(v_buckets_3179_);
v___x_3181_ = l_Lean_Meta_LazyDiscrTree_Key_hash(v_a_3177_);
v___x_3182_ = 32ULL;
v___x_3183_ = lean_uint64_shift_right(v___x_3181_, v___x_3182_);
v_fold_3184_ = lean_uint64_xor(v___x_3181_, v___x_3183_);
v___x_3185_ = 16ULL;
v___x_3186_ = lean_uint64_shift_right(v_fold_3184_, v___x_3185_);
v___x_3187_ = lean_uint64_xor(v_fold_3184_, v___x_3186_);
v___x_3188_ = lean_uint64_to_usize(v___x_3187_);
v___x_3189_ = lean_usize_of_nat(v___x_3180_);
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_sub(v___x_3189_, v___x_3190_);
v___x_3192_ = lean_usize_land(v___x_3188_, v___x_3191_);
v___x_3193_ = lean_array_uget_borrowed(v_buckets_3179_, v___x_3192_);
v___x_3194_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3177_, v_fallback_3178_, v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg___boxed(lean_object* v_m_3195_, lean_object* v_a_3196_, lean_object* v_fallback_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3195_, v_a_3196_, v_fallback_3197_);
lean_dec(v_fallback_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_m_3195_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(lean_object* v_next_3199_, lean_object* v_rest_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___x_3207_ = lean_unsigned_to_nat(0u);
v___x_3208_ = lean_nat_dec_eq(v_next_3199_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_3199_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3235_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3235_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3235_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v_snd_3214_; 
v_snd_3214_ = lean_ctor_get(v_a_3210_, 1);
lean_inc(v_snd_3214_);
lean_dec(v_a_3210_);
if (lean_obj_tag(v_rest_3200_) == 0)
{
lean_object* v_fst_3215_; lean_object* v_snd_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v_fst_3215_ = lean_ctor_get(v_snd_3214_, 0);
lean_inc(v_fst_3215_);
v_snd_3216_ = lean_ctor_get(v_snd_3214_, 1);
lean_inc(v_snd_3216_);
lean_dec(v_snd_3214_);
v___x_3217_ = lean_st_ref_take(v_a_3201_);
v___x_3218_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_3219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
lean_ctor_set(v___x_3219_, 1, v_fst_3215_);
lean_ctor_set(v___x_3219_, 2, v_snd_3216_);
lean_ctor_set(v___x_3219_, 3, v___x_3218_);
v___x_3220_ = lean_array_set(v___x_3217_, v_next_3199_, v___x_3219_);
lean_dec(v_next_3199_);
v___x_3221_ = lean_st_ref_set(v_a_3201_, v___x_3220_);
v___x_3222_ = lean_box(0);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3222_);
v___x_3224_ = v___x_3212_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
else
{
lean_object* v_fst_3226_; lean_object* v_snd_3227_; lean_object* v_head_3228_; lean_object* v_tail_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
lean_del_object(v___x_3212_);
lean_dec(v_next_3199_);
v_fst_3226_ = lean_ctor_get(v_snd_3214_, 0);
lean_inc(v_fst_3226_);
v_snd_3227_ = lean_ctor_get(v_snd_3214_, 1);
lean_inc(v_snd_3227_);
lean_dec(v_snd_3214_);
v_head_3228_ = lean_ctor_get(v_rest_3200_, 0);
v_tail_3229_ = lean_ctor_get(v_rest_3200_, 1);
v___x_3230_ = lean_box(3);
v___x_3231_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_3228_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; 
lean_dec(v_fst_3226_);
v___x_3232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_3227_, v_head_3228_, v___x_3207_);
lean_dec(v_snd_3227_);
v_next_3199_ = v___x_3232_;
v_rest_3200_ = v_tail_3229_;
goto _start;
}
else
{
lean_dec(v_snd_3227_);
v_next_3199_ = v_fst_3226_;
v_rest_3200_ = v_tail_3229_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec(v_next_3199_);
v_a_3236_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3209_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3209_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
lean_dec(v_next_3199_);
v___x_3244_ = lean_box(0);
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg___boxed(lean_object* v_next_3246_, lean_object* v_rest_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3246_, v_rest_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec(v_rest_3247_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux(lean_object* v_00_u03b1_3255_, lean_object* v_next_3256_, lean_object* v_rest_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux___redArg(v_next_3256_, v_rest_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed(lean_object* v_00_u03b1_3265_, lean_object* v_next_3266_, lean_object* v_rest_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_Meta_LazyDiscrTree_dropKeyAux(v_00_u03b1_3265_, v_next_3266_, v_rest_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
lean_dec(v_a_3272_);
lean_dec_ref(v_a_3271_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec(v_rest_3267_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(lean_object* v_00_u03b2_3275_, lean_object* v_m_3276_, lean_object* v_a_3277_, lean_object* v_fallback_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_m_3276_, v_a_3277_, v_fallback_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___boxed(lean_object* v_00_u03b2_3280_, lean_object* v_m_3281_, lean_object* v_a_3282_, lean_object* v_fallback_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0(v_00_u03b2_3280_, v_m_3281_, v_a_3282_, v_fallback_3283_);
lean_dec(v_fallback_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_m_3281_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(lean_object* v_00_u03b2_3285_, lean_object* v_a_3286_, lean_object* v_fallback_3287_, lean_object* v_x_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___redArg(v_a_3286_, v_fallback_3287_, v_x_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3290_, lean_object* v_a_3291_, lean_object* v_fallback_3292_, lean_object* v_x_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0_spec__0(v_00_u03b2_3290_, v_a_3291_, v_fallback_3292_, v_x_3293_);
lean_dec(v_x_3293_);
lean_dec(v_fallback_3292_);
lean_dec(v_a_3291_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg(lean_object* v_t_3295_, lean_object* v_path_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
if (lean_obj_tag(v_path_3296_) == 0)
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3302_, 0, v_t_3295_);
return v___x_3302_;
}
else
{
lean_object* v_head_3303_; lean_object* v_tail_3304_; lean_object* v_roots_3305_; lean_object* v___x_3306_; lean_object* v_idx_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_head_3303_ = lean_ctor_get(v_path_3296_, 0);
lean_inc(v_head_3303_);
v_tail_3304_ = lean_ctor_get(v_path_3296_, 1);
lean_inc(v_tail_3304_);
lean_dec_ref(v_path_3296_);
v_roots_3305_ = lean_ctor_get(v_t_3295_, 1);
v___x_3306_ = lean_unsigned_to_nat(0u);
v_idx_3307_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_3305_, v_head_3303_, v___x_3306_);
lean_dec(v_head_3303_);
v___x_3308_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_dropKeyAux___boxed), 9, 3);
lean_closure_set(v___x_3308_, 0, lean_box(0));
lean_closure_set(v___x_3308_, 1, v_idx_3307_);
lean_closure_set(v___x_3308_, 2, v_tail_3304_);
v___x_3309_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_3295_, v___x_3308_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3318_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v_snd_3314_; lean_object* v___x_3316_; 
v_snd_3314_ = lean_ctor_get(v_a_3310_, 1);
lean_inc(v_snd_3314_);
lean_dec(v_a_3310_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v_snd_3314_);
v___x_3316_ = v___x_3312_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_snd_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
v_a_3319_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3309_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3309_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___redArg___boxed(lean_object* v_t_3327_, lean_object* v_path_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3327_, v_path_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
lean_dec(v_a_3332_);
lean_dec_ref(v_a_3331_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey(lean_object* v_00_u03b1_3335_, lean_object* v_t_3336_, lean_object* v_path_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_t_3336_, v_path_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKey___boxed(lean_object* v_00_u03b1_3344_, lean_object* v_t_3345_, lean_object* v_path_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Meta_LazyDiscrTree_dropKey(v_00_u03b1_3344_, v_t_3345_, v_path_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(lean_object* v_score_3355_, lean_object* v_e_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = lean_array_get_size(v_a_3357_);
v___x_3359_ = lean_nat_dec_lt(v___x_3358_, v_score_3355_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3360_ = lean_unsigned_to_nat(1u);
v___x_3361_ = lean_mk_empty_array_with_capacity(v___x_3360_);
v___x_3362_ = lean_array_push(v___x_3361_, v_e_3356_);
v___x_3363_ = lean_array_push(v_a_3357_, v___x_3362_);
return v___x_3363_;
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = ((lean_object*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___closed__0));
v___x_3365_ = lean_array_push(v_a_3357_, v___x_3364_);
v_a_3357_ = v___x_3365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg___boxed(lean_object* v_score_3367_, lean_object* v_e_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3367_, v_e_3368_, v_a_3369_);
lean_dec(v_score_3367_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(lean_object* v_00_u03b1_3371_, lean_object* v_score_3372_, lean_object* v_e_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3372_, v_e_3373_, v_a_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___boxed(lean_object* v_00_u03b1_3376_, lean_object* v_score_3377_, lean_object* v_e_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop(v_00_u03b1_3376_, v_score_3377_, v_e_3378_, v_a_3379_);
lean_dec(v_score_3377_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(lean_object* v_r_3381_, lean_object* v_score_3382_, lean_object* v_e_3383_){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3384_ = lean_array_get_size(v_e_3383_);
v___x_3385_ = lean_unsigned_to_nat(0u);
v___x_3386_ = lean_nat_dec_eq(v___x_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = lean_array_get_size(v_r_3381_);
v___x_3388_ = lean_nat_dec_lt(v_score_3382_, v___x_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
v___x_3389_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_MatchResult_push_loop___redArg(v_score_3382_, v_e_3383_, v_r_3381_);
return v___x_3389_;
}
else
{
if (v___x_3388_ == 0)
{
lean_dec_ref(v_e_3383_);
return v_r_3381_;
}
else
{
lean_object* v_v_3390_; lean_object* v___x_3391_; lean_object* v_xs_x27_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v_v_3390_ = lean_array_fget(v_r_3381_, v_score_3382_);
v___x_3391_ = lean_box(0);
v_xs_x27_3392_ = lean_array_fset(v_r_3381_, v_score_3382_, v___x_3391_);
v___x_3393_ = lean_array_push(v_v_3390_, v_e_3383_);
v___x_3394_ = lean_array_fset(v_xs_x27_3392_, v_score_3382_, v___x_3393_);
return v___x_3394_;
}
}
}
else
{
lean_dec_ref(v_e_3383_);
return v_r_3381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg___boxed(lean_object* v_r_3395_, lean_object* v_score_3396_, lean_object* v_e_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3395_, v_score_3396_, v_e_3397_);
lean_dec(v_score_3396_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push(lean_object* v_00_u03b1_3399_, lean_object* v_r_3400_, lean_object* v_score_3401_, lean_object* v_e_3402_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_r_3400_, v_score_3401_, v_e_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_push___boxed(lean_object* v_00_u03b1_3404_, lean_object* v_r_3405_, lean_object* v_score_3406_, lean_object* v_e_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push(v_00_u03b1_3404_, v_r_3405_, v_score_3406_, v_e_3407_);
lean_dec(v_score_3406_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(lean_object* v_as_3409_, size_t v_i_3410_, size_t v_stop_3411_, lean_object* v_b_3412_){
_start:
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_usize_dec_eq(v_i_3410_, v_stop_3411_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; size_t v___x_3417_; size_t v___x_3418_; 
v___x_3414_ = lean_array_uget_borrowed(v_as_3409_, v_i_3410_);
v___x_3415_ = lean_array_get_size(v___x_3414_);
v___x_3416_ = lean_nat_add(v_b_3412_, v___x_3415_);
lean_dec(v_b_3412_);
v___x_3417_ = ((size_t)1ULL);
v___x_3418_ = lean_usize_add(v_i_3410_, v___x_3417_);
v_i_3410_ = v___x_3418_;
v_b_3412_ = v___x_3416_;
goto _start;
}
else
{
return v_b_3412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg___boxed(lean_object* v_as_3420_, lean_object* v_i_3421_, lean_object* v_stop_3422_, lean_object* v_b_3423_){
_start:
{
size_t v_i_boxed_3424_; size_t v_stop_boxed_3425_; lean_object* v_res_3426_; 
v_i_boxed_3424_ = lean_unbox_usize(v_i_3421_);
lean_dec(v_i_3421_);
v_stop_boxed_3425_ = lean_unbox_usize(v_stop_3422_);
lean_dec(v_stop_3422_);
v_res_3426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3420_, v_i_boxed_3424_, v_stop_boxed_3425_, v_b_3423_);
lean_dec_ref(v_as_3420_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(lean_object* v_as_3427_, size_t v_i_3428_, size_t v_stop_3429_, lean_object* v_b_3430_){
_start:
{
lean_object* v___y_3432_; uint8_t v___x_3436_; 
v___x_3436_ = lean_usize_dec_eq(v_i_3428_, v_stop_3429_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3437_ = lean_array_uget_borrowed(v_as_3427_, v_i_3428_);
v___x_3438_ = lean_unsigned_to_nat(0u);
v___x_3439_ = lean_array_get_size(v___x_3437_);
v___x_3440_ = lean_nat_dec_lt(v___x_3438_, v___x_3439_);
if (v___x_3440_ == 0)
{
v___y_3432_ = v_b_3430_;
goto v___jp_3431_;
}
else
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_nat_dec_le(v___x_3439_, v___x_3439_);
if (v___x_3441_ == 0)
{
if (v___x_3440_ == 0)
{
v___y_3432_ = v_b_3430_;
goto v___jp_3431_;
}
else
{
size_t v___x_3442_; size_t v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = ((size_t)0ULL);
v___x_3443_ = lean_usize_of_nat(v___x_3439_);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3437_, v___x_3442_, v___x_3443_, v_b_3430_);
v___y_3432_ = v___x_3444_;
goto v___jp_3431_;
}
}
else
{
size_t v___x_3445_; size_t v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = ((size_t)0ULL);
v___x_3446_ = lean_usize_of_nat(v___x_3439_);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v___x_3437_, v___x_3445_, v___x_3446_, v_b_3430_);
v___y_3432_ = v___x_3447_;
goto v___jp_3431_;
}
}
}
else
{
return v_b_3430_;
}
v___jp_3431_:
{
size_t v___x_3433_; size_t v___x_3434_; 
v___x_3433_ = ((size_t)1ULL);
v___x_3434_ = lean_usize_add(v_i_3428_, v___x_3433_);
v_i_3428_ = v___x_3434_;
v_b_3430_ = v___y_3432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg___boxed(lean_object* v_as_3448_, lean_object* v_i_3449_, lean_object* v_stop_3450_, lean_object* v_b_3451_){
_start:
{
size_t v_i_boxed_3452_; size_t v_stop_boxed_3453_; lean_object* v_res_3454_; 
v_i_boxed_3452_ = lean_unbox_usize(v_i_3449_);
lean_dec(v_i_3449_);
v_stop_boxed_3453_ = lean_unbox_usize(v_stop_3450_);
lean_dec(v_stop_3450_);
v_res_3454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3448_, v_i_boxed_3452_, v_stop_boxed_3453_, v_b_3451_);
lean_dec_ref(v_as_3448_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(lean_object* v_mr_3455_){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v___x_3456_ = lean_unsigned_to_nat(0u);
v___x_3457_ = lean_array_get_size(v_mr_3455_);
v___x_3458_ = lean_nat_dec_lt(v___x_3456_, v___x_3457_);
if (v___x_3458_ == 0)
{
return v___x_3456_;
}
else
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_nat_dec_le(v___x_3457_, v___x_3457_);
if (v___x_3459_ == 0)
{
if (v___x_3458_ == 0)
{
return v___x_3456_;
}
else
{
size_t v___x_3460_; size_t v___x_3461_; lean_object* v___x_3462_; 
v___x_3460_ = ((size_t)0ULL);
v___x_3461_ = lean_usize_of_nat(v___x_3457_);
v___x_3462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3455_, v___x_3460_, v___x_3461_, v___x_3456_);
return v___x_3462_;
}
}
else
{
size_t v___x_3463_; size_t v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = ((size_t)0ULL);
v___x_3464_ = lean_usize_of_nat(v___x_3457_);
v___x_3465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_mr_3455_, v___x_3463_, v___x_3464_, v___x_3456_);
return v___x_3465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg___boxed(lean_object* v_mr_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3466_);
lean_dec_ref(v_mr_3466_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size(lean_object* v_00_u03b1_3468_, lean_object* v_mr_3469_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_mr_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_size___boxed(lean_object* v_00_u03b1_3471_, lean_object* v_mr_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size(v_00_u03b1_3471_, v_mr_3472_);
lean_dec_ref(v_mr_3472_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(lean_object* v_00_u03b1_3474_, lean_object* v_as_3475_, size_t v_i_3476_, size_t v_stop_3477_, lean_object* v_b_3478_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___redArg(v_as_3475_, v_i_3476_, v_stop_3477_, v_b_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0___boxed(lean_object* v_00_u03b1_3480_, lean_object* v_as_3481_, lean_object* v_i_3482_, lean_object* v_stop_3483_, lean_object* v_b_3484_){
_start:
{
size_t v_i_boxed_3485_; size_t v_stop_boxed_3486_; lean_object* v_res_3487_; 
v_i_boxed_3485_ = lean_unbox_usize(v_i_3482_);
lean_dec(v_i_3482_);
v_stop_boxed_3486_ = lean_unbox_usize(v_stop_3483_);
lean_dec(v_stop_3483_);
v_res_3487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__0(v_00_u03b1_3480_, v_as_3481_, v_i_boxed_3485_, v_stop_boxed_3486_, v_b_3484_);
lean_dec_ref(v_as_3481_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(lean_object* v_00_u03b1_3488_, lean_object* v_as_3489_, size_t v_i_3490_, size_t v_stop_3491_, lean_object* v_b_3492_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___redArg(v_as_3489_, v_i_3490_, v_stop_3491_, v_b_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1___boxed(lean_object* v_00_u03b1_3494_, lean_object* v_as_3495_, lean_object* v_i_3496_, lean_object* v_stop_3497_, lean_object* v_b_3498_){
_start:
{
size_t v_i_boxed_3499_; size_t v_stop_boxed_3500_; lean_object* v_res_3501_; 
v_i_boxed_3499_ = lean_unbox_usize(v_i_3496_);
lean_dec(v_i_3496_);
v_stop_boxed_3500_ = lean_unbox_usize(v_stop_3497_);
lean_dec(v_stop_3497_);
v_res_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_size_spec__1(v_00_u03b1_3494_, v_as_3495_, v_i_boxed_3499_, v_stop_boxed_3500_, v_b_3498_);
lean_dec_ref(v_as_3495_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0(lean_object* v_f_3502_, lean_object* v_j_3503_, lean_object* v_x_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = lean_apply_2(v_f_3502_, v_j_3503_, v_x_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1(lean_object* v___f_3525_, lean_object* v_x1_3526_, lean_object* v_x2_3527_){
_start:
{
lean_object* v___x_3528_; size_t v_sz_3529_; size_t v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3528_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v_sz_3529_ = lean_array_size(v_x2_3527_);
v___x_3530_ = ((size_t)0ULL);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3528_, v___f_3525_, v_sz_3529_, v___x_3530_, v_x2_3527_);
v___x_3532_ = l_Array_append___redArg(v_x1_3526_, v___x_3531_);
lean_dec(v___x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(lean_object* v_n_3533_, lean_object* v_mr_3534_, lean_object* v_f_3535_, lean_object* v_i_3536_, lean_object* v_x_3537_, lean_object* v_r_3538_){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v_j_3541_; lean_object* v_b_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; uint8_t v___x_3546_; 
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = lean_nat_sub(v_n_3533_, v___x_3539_);
v_j_3541_ = lean_nat_sub(v___x_3540_, v_i_3536_);
lean_dec(v___x_3540_);
v_b_3542_ = lean_array_fget_borrowed(v_mr_3534_, v_j_3541_);
v___x_3543_ = lean_unsigned_to_nat(0u);
v___x_3544_ = lean_array_get_size(v_b_3542_);
v___x_3545_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_3546_ = lean_nat_dec_lt(v___x_3543_, v___x_3544_);
if (v___x_3546_ == 0)
{
lean_dec(v_j_3541_);
lean_dec(v_f_3535_);
return v_r_3538_;
}
else
{
lean_object* v___f_3547_; lean_object* v___f_3548_; uint8_t v___x_3549_; 
v___f_3547_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3547_, 0, v_f_3535_);
lean_closure_set(v___f_3547_, 1, v_j_3541_);
v___f_3548_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_3548_, 0, v___f_3547_);
v___x_3549_ = lean_nat_dec_le(v___x_3544_, v___x_3544_);
if (v___x_3549_ == 0)
{
if (v___x_3546_ == 0)
{
lean_dec_ref(v___f_3548_);
return v_r_3538_;
}
else
{
size_t v___x_3550_; size_t v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = ((size_t)0ULL);
v___x_3551_ = lean_usize_of_nat(v___x_3544_);
lean_inc(v_b_3542_);
v___x_3552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3545_, v___f_3548_, v_b_3542_, v___x_3550_, v___x_3551_, v_r_3538_);
return v___x_3552_;
}
}
else
{
size_t v___x_3553_; size_t v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = ((size_t)0ULL);
v___x_3554_ = lean_usize_of_nat(v___x_3544_);
lean_inc(v_b_3542_);
v___x_3555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3545_, v___f_3548_, v_b_3542_, v___x_3553_, v___x_3554_, v_r_3538_);
return v___x_3555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed(lean_object* v_n_3556_, lean_object* v_mr_3557_, lean_object* v_f_3558_, lean_object* v_i_3559_, lean_object* v_x_3560_, lean_object* v_r_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2(v_n_3556_, v_mr_3557_, v_f_3558_, v_i_3559_, v_x_3560_, v_r_3561_);
lean_dec(v_i_3559_);
lean_dec_ref(v_mr_3557_);
lean_dec(v_n_3556_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(lean_object* v_mr_3563_, lean_object* v_a_3564_, lean_object* v_f_3565_){
_start:
{
lean_object* v_n_3566_; lean_object* v___f_3567_; lean_object* v___x_3568_; 
v_n_3566_ = lean_array_get_size(v_mr_3563_);
v___f_3567_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_3567_, 0, v_n_3566_);
lean_closure_set(v___f_3567_, 1, v_mr_3563_);
lean_closure_set(v___f_3567_, 2, v_f_3565_);
v___x_3568_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3566_, v___f_3567_, v_n_3566_, lean_box(0), v_a_3564_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux(lean_object* v_00_u03b1_3569_, lean_object* v_00_u03b2_3570_, lean_object* v_mr_3571_, lean_object* v_a_3572_, lean_object* v_f_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg(v_mr_3571_, v_a_3572_, v_f_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(size_t v_sz_3575_, size_t v_i_3576_, lean_object* v_bs_3577_){
_start:
{
uint8_t v___x_3578_; 
v___x_3578_ = lean_usize_dec_lt(v_i_3576_, v_sz_3575_);
if (v___x_3578_ == 0)
{
return v_bs_3577_;
}
else
{
lean_object* v_v_3579_; lean_object* v___x_3580_; lean_object* v_bs_x27_3581_; size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_3584_; 
v_v_3579_ = lean_array_uget(v_bs_3577_, v_i_3576_);
v___x_3580_ = lean_unsigned_to_nat(0u);
v_bs_x27_3581_ = lean_array_uset(v_bs_3577_, v_i_3576_, v___x_3580_);
v___x_3582_ = ((size_t)1ULL);
v___x_3583_ = lean_usize_add(v_i_3576_, v___x_3582_);
v___x_3584_ = lean_array_uset(v_bs_x27_3581_, v_i_3576_, v_v_3579_);
v_i_3576_ = v___x_3583_;
v_bs_3577_ = v___x_3584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg___boxed(lean_object* v_sz_3586_, lean_object* v_i_3587_, lean_object* v_bs_3588_){
_start:
{
size_t v_sz_boxed_3589_; size_t v_i_boxed_3590_; lean_object* v_res_3591_; 
v_sz_boxed_3589_ = lean_unbox_usize(v_sz_3586_);
lean_dec(v_sz_3586_);
v_i_boxed_3590_ = lean_unbox_usize(v_i_3587_);
lean_dec(v_i_3587_);
v_res_3591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_boxed_3589_, v_i_boxed_3590_, v_bs_3588_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(lean_object* v_as_3592_, size_t v_i_3593_, size_t v_stop_3594_, lean_object* v_b_3595_){
_start:
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_usize_dec_eq(v_i_3593_, v_stop_3594_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; size_t v_sz_3598_; size_t v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; size_t v___x_3602_; size_t v___x_3603_; 
v___x_3597_ = lean_array_uget_borrowed(v_as_3592_, v_i_3593_);
v_sz_3598_ = lean_array_size(v___x_3597_);
v___x_3599_ = ((size_t)0ULL);
lean_inc(v___x_3597_);
v___x_3600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3598_, v___x_3599_, v___x_3597_);
v___x_3601_ = l_Array_append___redArg(v_b_3595_, v___x_3600_);
lean_dec_ref(v___x_3600_);
v___x_3602_ = ((size_t)1ULL);
v___x_3603_ = lean_usize_add(v_i_3593_, v___x_3602_);
v_i_3593_ = v___x_3603_;
v_b_3595_ = v___x_3601_;
goto _start;
}
else
{
return v_b_3595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg___boxed(lean_object* v_as_3605_, lean_object* v_i_3606_, lean_object* v_stop_3607_, lean_object* v_b_3608_){
_start:
{
size_t v_i_boxed_3609_; size_t v_stop_boxed_3610_; lean_object* v_res_3611_; 
v_i_boxed_3609_ = lean_unbox_usize(v_i_3606_);
lean_dec(v_i_3606_);
v_stop_boxed_3610_ = lean_unbox_usize(v_stop_3607_);
lean_dec(v_stop_3607_);
v_res_3611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3605_, v_i_boxed_3609_, v_stop_boxed_3610_, v_b_3608_);
lean_dec_ref(v_as_3605_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(lean_object* v_n_3612_, lean_object* v_aa_3613_, lean_object* v_n_3614_, lean_object* v_j_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v_zero_3617_; uint8_t v_isZero_3618_; 
v_zero_3617_ = lean_unsigned_to_nat(0u);
v_isZero_3618_ = lean_nat_dec_eq(v_j_3615_, v_zero_3617_);
if (v_isZero_3618_ == 1)
{
lean_dec(v_j_3615_);
return v_a_3616_;
}
else
{
lean_object* v_one_3619_; lean_object* v_n_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v_j_3623_; lean_object* v_b_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; 
v_one_3619_ = lean_unsigned_to_nat(1u);
v_n_3620_ = lean_nat_sub(v_j_3615_, v_one_3619_);
v___x_3621_ = lean_nat_sub(v_n_3614_, v_j_3615_);
lean_dec(v_j_3615_);
v___x_3622_ = lean_nat_sub(v_n_3612_, v_one_3619_);
v_j_3623_ = lean_nat_sub(v___x_3622_, v___x_3621_);
lean_dec(v___x_3621_);
lean_dec(v___x_3622_);
v_b_3624_ = lean_array_fget_borrowed(v_aa_3613_, v_j_3623_);
lean_dec(v_j_3623_);
v___x_3625_ = lean_array_get_size(v_b_3624_);
v___x_3626_ = lean_nat_dec_lt(v_zero_3617_, v___x_3625_);
if (v___x_3626_ == 0)
{
v_j_3615_ = v_n_3620_;
goto _start;
}
else
{
uint8_t v___x_3628_; 
v___x_3628_ = lean_nat_dec_le(v___x_3625_, v___x_3625_);
if (v___x_3628_ == 0)
{
if (v___x_3626_ == 0)
{
v_j_3615_ = v_n_3620_;
goto _start;
}
else
{
size_t v___x_3630_; size_t v___x_3631_; lean_object* v___x_3632_; 
v___x_3630_ = ((size_t)0ULL);
v___x_3631_ = lean_usize_of_nat(v___x_3625_);
v___x_3632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3624_, v___x_3630_, v___x_3631_, v_a_3616_);
v_j_3615_ = v_n_3620_;
v_a_3616_ = v___x_3632_;
goto _start;
}
}
else
{
size_t v___x_3634_; size_t v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = ((size_t)0ULL);
v___x_3635_ = lean_usize_of_nat(v___x_3625_);
v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_b_3624_, v___x_3634_, v___x_3635_, v_a_3616_);
v_j_3615_ = v_n_3620_;
v_a_3616_ = v___x_3636_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg___boxed(lean_object* v_n_3638_, lean_object* v_aa_3639_, lean_object* v_n_3640_, lean_object* v_j_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3638_, v_aa_3639_, v_n_3640_, v_j_3641_, v_a_3642_);
lean_dec(v_n_3640_);
lean_dec_ref(v_aa_3639_);
lean_dec(v_n_3638_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(lean_object* v_mr_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v_n_3646_; lean_object* v___x_3647_; 
v_n_3646_ = lean_array_get_size(v_mr_3644_);
v___x_3647_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3646_, v_mr_3644_, v_n_3646_, v_n_3646_, v_a_3645_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg___boxed(lean_object* v_mr_3648_, lean_object* v_a_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3648_, v_a_3649_);
lean_dec_ref(v_mr_3648_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(lean_object* v_mr_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3651_, v_a_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg___boxed(lean_object* v_mr_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___redArg(v_mr_3654_, v_a_3655_);
lean_dec_ref(v_mr_3654_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(lean_object* v_00_u03b1_3657_, lean_object* v_mr_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3658_, v_a_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults___boxed(lean_object* v_00_u03b1_3661_, lean_object* v_mr_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResults(v_00_u03b1_3661_, v_mr_3662_, v_a_3663_);
lean_dec_ref(v_mr_3662_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(lean_object* v_00_u03b1_3665_, lean_object* v_mr_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___redArg(v_mr_3666_, v_a_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0___boxed(lean_object* v_00_u03b1_3669_, lean_object* v_mr_3670_, lean_object* v_a_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0(v_00_u03b1_3669_, v_mr_3670_, v_a_3671_);
lean_dec_ref(v_mr_3670_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(lean_object* v_00_u03b1_3673_, size_t v_sz_3674_, size_t v_i_3675_, lean_object* v_bs_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___redArg(v_sz_3674_, v_i_3675_, v_bs_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3678_, lean_object* v_sz_3679_, lean_object* v_i_3680_, lean_object* v_bs_3681_){
_start:
{
size_t v_sz_boxed_3682_; size_t v_i_boxed_3683_; lean_object* v_res_3684_; 
v_sz_boxed_3682_ = lean_unbox_usize(v_sz_3679_);
lean_dec(v_sz_3679_);
v_i_boxed_3683_ = lean_unbox_usize(v_i_3680_);
lean_dec(v_i_3680_);
v_res_3684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__0(v_00_u03b1_3678_, v_sz_boxed_3682_, v_i_boxed_3683_, v_bs_3681_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(lean_object* v_00_u03b1_3685_, lean_object* v_as_3686_, size_t v_i_3687_, size_t v_stop_3688_, lean_object* v_b_3689_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___redArg(v_as_3686_, v_i_3687_, v_stop_3688_, v_b_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3691_, lean_object* v_as_3692_, lean_object* v_i_3693_, lean_object* v_stop_3694_, lean_object* v_b_3695_){
_start:
{
size_t v_i_boxed_3696_; size_t v_stop_boxed_3697_; lean_object* v_res_3698_; 
v_i_boxed_3696_ = lean_unbox_usize(v_i_3693_);
lean_dec(v_i_3693_);
v_stop_boxed_3697_ = lean_unbox_usize(v_stop_3694_);
lean_dec(v_stop_3694_);
v_res_3698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__1(v_00_u03b1_3691_, v_as_3692_, v_i_boxed_3696_, v_stop_boxed_3697_, v_b_3695_);
lean_dec_ref(v_as_3692_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(lean_object* v_00_u03b1_3699_, lean_object* v_n_3700_, lean_object* v_aa_3701_, lean_object* v_n_3702_, lean_object* v_j_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___redArg(v_n_3700_, v_aa_3701_, v_n_3702_, v_j_3703_, v_a_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3707_, lean_object* v_n_3708_, lean_object* v_aa_3709_, lean_object* v_n_3710_, lean_object* v_j_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResults_spec__0_spec__2(v_00_u03b1_3707_, v_n_3708_, v_aa_3709_, v_n_3710_, v_j_3711_, v_a_3712_, v_a_3713_);
lean_dec(v_n_3710_);
lean_dec_ref(v_aa_3709_);
lean_dec(v_n_3708_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(lean_object* v_snd_3722_, lean_object* v___x_3723_, lean_object* v_score_3724_, lean_object* v___x_3725_, lean_object* v_k_3726_, lean_object* v_args_3727_, lean_object* v_cases_3728_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_snd_3722_, v_k_3726_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_dec_ref(v___x_3723_);
return v_cases_3728_;
}
else
{
lean_object* v_val_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_val_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_val_3730_);
lean_dec_ref(v___x_3729_);
v___x_3731_ = l_Array_append___redArg(v___x_3723_, v_args_3727_);
v___x_3732_ = lean_nat_add(v_score_3724_, v___x_3725_);
v___x_3733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
lean_ctor_set(v___x_3733_, 2, v_val_3730_);
v___x_3734_ = lean_array_push(v_cases_3728_, v___x_3733_);
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed(lean_object* v_snd_3735_, lean_object* v___x_3736_, lean_object* v_score_3737_, lean_object* v___x_3738_, lean_object* v_k_3739_, lean_object* v_args_3740_, lean_object* v_cases_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0(v_snd_3735_, v___x_3736_, v_score_3737_, v___x_3738_, v_k_3739_, v_args_3740_, v_cases_3741_);
lean_dec_ref(v_args_3740_);
lean_dec(v_k_3739_);
lean_dec(v___x_3738_);
lean_dec(v_score_3737_);
lean_dec_ref(v_snd_3735_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(lean_object* v_cases_3743_, lean_object* v_result_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
v___x_3751_ = lean_array_get_size(v_cases_3743_);
v___x_3752_ = lean_unsigned_to_nat(0u);
v___x_3753_ = lean_nat_dec_eq(v___x_3751_, v___x_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v_ca_3757_; lean_object* v_todo_3758_; lean_object* v_score_3759_; lean_object* v_c_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3826_; 
v___x_3754_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPartialMatch_default));
v___x_3755_ = lean_unsigned_to_nat(1u);
v___x_3756_ = lean_nat_sub(v___x_3751_, v___x_3755_);
v_ca_3757_ = lean_array_get(v___x_3754_, v_cases_3743_, v___x_3756_);
lean_dec(v___x_3756_);
v_todo_3758_ = lean_ctor_get(v_ca_3757_, 0);
v_score_3759_ = lean_ctor_get(v_ca_3757_, 1);
v_c_3760_ = lean_ctor_get(v_ca_3757_, 2);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_ca_3757_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3762_ = v_ca_3757_;
v_isShared_3763_ = v_isSharedCheck_3826_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_c_3760_);
lean_inc(v_score_3759_);
lean_inc(v_todo_3758_);
lean_dec(v_ca_3757_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3826_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_c_3760_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
lean_dec(v_c_3760_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; uint8_t v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_snd_3793_; lean_object* v_fst_3794_; lean_object* v_fst_3795_; lean_object* v_snd_3796_; lean_object* v_cases_3797_; lean_object* v___x_3798_; uint8_t v___y_3800_; uint8_t v___x_3812_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref(v___x_3764_);
v_snd_3793_ = lean_ctor_get(v_a_3765_, 1);
lean_inc(v_snd_3793_);
v_fst_3794_ = lean_ctor_get(v_a_3765_, 0);
lean_inc(v_fst_3794_);
lean_dec(v_a_3765_);
v_fst_3795_ = lean_ctor_get(v_snd_3793_, 0);
lean_inc(v_fst_3795_);
v_snd_3796_ = lean_ctor_get(v_snd_3793_, 1);
lean_inc(v_snd_3796_);
lean_dec(v_snd_3793_);
v_cases_3797_ = lean_array_pop(v_cases_3743_);
v___x_3798_ = lean_array_get_size(v_todo_3758_);
v___x_3812_ = lean_nat_dec_eq(v___x_3798_, v___x_3752_);
if (v___x_3812_ == 0)
{
uint8_t v___x_3813_; 
lean_dec(v_fst_3794_);
v___x_3813_ = lean_nat_dec_eq(v_fst_3795_, v___x_3752_);
if (v___x_3813_ == 0)
{
v___y_3800_ = v___x_3813_;
goto v___jp_3799_;
}
else
{
lean_object* v_size_3814_; uint8_t v___x_3815_; 
v_size_3814_ = lean_ctor_get(v_snd_3796_, 0);
v___x_3815_ = lean_nat_dec_eq(v_size_3814_, v___x_3752_);
v___y_3800_ = v___x_3815_;
goto v___jp_3799_;
}
}
else
{
lean_object* v___x_3816_; 
lean_dec(v_snd_3796_);
lean_dec(v_fst_3795_);
lean_del_object(v___x_3762_);
lean_dec_ref(v_todo_3758_);
v___x_3816_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v_result_3744_, v_score_3759_, v_fst_3794_);
lean_dec(v_score_3759_);
v_cases_3743_ = v_cases_3797_;
v_result_3744_ = v___x_3816_;
goto _start;
}
v___jp_3766_:
{
uint8_t v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = 1;
v___x_3772_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v___y_3768_, v___x_3771_, v___y_3767_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v_fst_3774_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref(v___x_3772_);
v_fst_3774_ = lean_ctor_get(v_a_3773_, 0);
lean_inc(v_fst_3774_);
switch(lean_obj_tag(v_fst_3774_))
{
case 3:
{
lean_dec(v_a_3773_);
lean_dec_ref(v___y_3769_);
v_cases_3743_ = v___y_3770_;
goto _start;
}
case 5:
{
lean_object* v_snd_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v_snd_3776_ = lean_ctor_get(v_a_3773_, 1);
lean_inc(v_snd_3776_);
lean_dec(v_a_3773_);
v___x_3777_ = lean_box(4);
v___x_3778_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
lean_inc_ref(v___y_3769_);
v___x_3779_ = lean_apply_3(v___y_3769_, v___x_3777_, v___x_3778_, v___y_3770_);
v___x_3780_ = lean_apply_3(v___y_3769_, v_fst_3774_, v_snd_3776_, v___x_3779_);
v_cases_3743_ = v___x_3780_;
goto _start;
}
default: 
{
lean_object* v_snd_3782_; lean_object* v___x_3783_; 
v_snd_3782_ = lean_ctor_get(v_a_3773_, 1);
lean_inc(v_snd_3782_);
lean_dec(v_a_3773_);
v___x_3783_ = lean_apply_3(v___y_3769_, v_fst_3774_, v_snd_3782_, v___y_3770_);
v_cases_3743_ = v___x_3783_;
goto _start;
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec_ref(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec_ref(v_result_3744_);
v_a_3785_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3772_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3772_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
v___jp_3799_:
{
if (v___y_3800_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___f_3805_; uint8_t v___x_3806_; 
v___x_3801_ = l_Lean_instInhabitedExpr;
v___x_3802_ = lean_nat_sub(v___x_3798_, v___x_3755_);
v___x_3803_ = lean_array_get(v___x_3801_, v_todo_3758_, v___x_3802_);
lean_dec(v___x_3802_);
v___x_3804_ = lean_array_pop(v_todo_3758_);
lean_inc(v_score_3759_);
lean_inc_ref(v___x_3804_);
v___f_3805_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_3805_, 0, v_snd_3796_);
lean_closure_set(v___f_3805_, 1, v___x_3804_);
lean_closure_set(v___f_3805_, 2, v_score_3759_);
lean_closure_set(v___f_3805_, 3, v___x_3755_);
v___x_3806_ = lean_nat_dec_eq(v_fst_3795_, v___x_3752_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3808_; 
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 2, v_fst_3795_);
lean_ctor_set(v___x_3762_, 0, v___x_3804_);
v___x_3808_ = v___x_3762_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_score_3759_);
lean_ctor_set(v_reuseFailAlloc_3810_, 2, v_fst_3795_);
v___x_3808_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_array_push(v_cases_3797_, v___x_3808_);
v___y_3767_ = v___y_3800_;
v___y_3768_ = v___x_3803_;
v___y_3769_ = v___f_3805_;
v___y_3770_ = v___x_3809_;
goto v___jp_3766_;
}
}
else
{
lean_dec_ref(v___x_3804_);
lean_dec(v_fst_3795_);
lean_del_object(v___x_3762_);
lean_dec(v_score_3759_);
v___y_3767_ = v___y_3800_;
v___y_3768_ = v___x_3803_;
v___y_3769_ = v___f_3805_;
v___y_3770_ = v_cases_3797_;
goto v___jp_3766_;
}
}
else
{
lean_dec(v_snd_3796_);
lean_dec(v_fst_3795_);
lean_del_object(v___x_3762_);
lean_dec(v_score_3759_);
lean_dec_ref(v_todo_3758_);
v_cases_3743_ = v_cases_3797_;
goto _start;
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_del_object(v___x_3762_);
lean_dec(v_score_3759_);
lean_dec_ref(v_todo_3758_);
lean_dec_ref(v_result_3744_);
lean_dec_ref(v_cases_3743_);
v_a_3818_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3764_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3764_);
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
}
else
{
lean_object* v___x_3827_; 
lean_dec_ref(v_cases_3743_);
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v_result_3744_);
return v___x_3827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg___boxed(lean_object* v_cases_3828_, lean_object* v_result_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3828_, v_result_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec(v_a_3832_);
lean_dec_ref(v_a_3831_);
lean_dec(v_a_3830_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop(lean_object* v_00_u03b1_3837_, lean_object* v_cases_3838_, lean_object* v_result_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v_cases_3838_, v_result_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchLoop___boxed(lean_object* v_00_u03b1_3847_, lean_object* v_cases_3848_, lean_object* v_result_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop(v_00_u03b1_3847_, v_cases_3848_, v_result_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
lean_dec(v_a_3854_);
lean_dec_ref(v_a_3853_);
lean_dec(v_a_3852_);
lean_dec_ref(v_a_3851_);
lean_dec(v_a_3850_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(lean_object* v_root_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3866_ = lean_box(3);
v___x_3867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_root_3859_, v___x_3866_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
return v___x_3869_;
}
else
{
lean_object* v_val_3870_; lean_object* v___x_3871_; 
v_val_3870_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_val_3870_);
lean_dec_ref(v___x_3867_);
v___x_3871_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_val_3870_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
lean_dec(v_val_3870_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3883_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3883_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3883_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v_fst_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3881_; 
v_fst_3876_ = lean_ctor_get(v_a_3872_, 0);
lean_inc(v_fst_3876_);
lean_dec(v_a_3872_);
v___x_3877_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___closed__0));
v___x_3878_ = lean_unsigned_to_nat(1u);
v___x_3879_ = l_Lean_Meta_LazyDiscrTree_MatchResult_push___redArg(v___x_3877_, v___x_3878_, v_fst_3876_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v___x_3879_);
v___x_3881_ = v___x_3874_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
v_a_3884_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3871_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3871_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___redArg___boxed(lean_object* v_root_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
lean_dec(v_a_3897_);
lean_dec_ref(v_a_3896_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
lean_dec(v_a_3893_);
lean_dec_ref(v_root_3892_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult(lean_object* v_00_u03b1_3900_, lean_object* v_root_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getStarResult___boxed(lean_object* v_00_u03b1_3909_, lean_object* v_root_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Lean_Meta_LazyDiscrTree_getStarResult(v_00_u03b1_3909_, v_root_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
lean_dec(v_a_3915_);
lean_dec_ref(v_a_3914_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_root_3910_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase(lean_object* v_r_3918_, lean_object* v_k_3919_, lean_object* v_args_3920_, lean_object* v_cases_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_r_3918_, v_k_3919_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_dec_ref(v_args_3920_);
return v_cases_3921_;
}
else
{
lean_object* v_val_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_val_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_val_3923_);
lean_dec_ref(v___x_3922_);
v___x_3924_ = lean_unsigned_to_nat(1u);
v___x_3925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3925_, 0, v_args_3920_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
lean_ctor_set(v___x_3925_, 2, v_val_3923_);
v___x_3926_ = lean_array_push(v_cases_3921_, v___x_3925_);
return v___x_3926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_pushRootCase___boxed(lean_object* v_r_3927_, lean_object* v_k_3928_, lean_object* v_args_3929_, lean_object* v_cases_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_r_3927_, v_k_3928_, v_args_3929_, v_cases_3930_);
lean_dec(v_k_3928_);
lean_dec_ref(v_r_3927_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(lean_object* v_root_3934_, lean_object* v_e_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Lean_Meta_LazyDiscrTree_getStarResult___redArg(v_root_3934_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; uint8_t v___x_3944_; lean_object* v___x_3945_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref(v___x_3942_);
v___x_3944_ = 1;
v___x_3945_ = l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs(v_e_3935_, v___x_3944_, v___x_3944_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v_fst_3947_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref(v___x_3945_);
v_fst_3947_ = lean_ctor_get(v_a_3946_, 0);
lean_inc(v_fst_3947_);
switch(lean_obj_tag(v_fst_3947_))
{
case 3:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_dec(v_a_3946_);
v___x_3948_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3949_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3948_, v_a_3943_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
return v___x_3949_;
}
case 5:
{
lean_object* v_snd_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_snd_3950_ = lean_ctor_get(v_a_3946_, 1);
lean_inc(v_snd_3950_);
lean_dec(v_a_3946_);
v___x_3951_ = lean_box(4);
v___x_3952_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchClone_getKeyArgs___closed__0));
v___x_3953_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3934_, v___x_3951_, v___x_3952_, v___x_3952_);
v___x_3954_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3934_, v_fst_3947_, v_snd_3950_, v___x_3953_);
v___x_3955_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3954_, v_a_3943_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
return v___x_3955_;
}
default: 
{
lean_object* v_snd_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v_snd_3956_ = lean_ctor_get(v_a_3946_, 1);
lean_inc(v_snd_3956_);
lean_dec(v_a_3946_);
v___x_3957_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___closed__0));
v___x_3958_ = l_Lean_Meta_LazyDiscrTree_pushRootCase(v_root_3934_, v_fst_3947_, v_snd_3956_, v___x_3957_);
lean_dec(v_fst_3947_);
v___x_3959_ = l_Lean_Meta_LazyDiscrTree_getMatchLoop___redArg(v___x_3958_, v_a_3943_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
return v___x_3959_;
}
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec(v_a_3943_);
v_a_3960_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3945_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3945_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
else
{
lean_dec_ref(v_e_3935_);
return v___x_3942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg___boxed(lean_object* v_root_3968_, lean_object* v_e_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3968_, v_e_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_);
lean_dec(v_a_3974_);
lean_dec_ref(v_a_3973_);
lean_dec(v_a_3972_);
lean_dec_ref(v_a_3971_);
lean_dec(v_a_3970_);
lean_dec_ref(v_root_3968_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore(lean_object* v_00_u03b1_3977_, lean_object* v_root_3978_, lean_object* v_e_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lean_Meta_LazyDiscrTree_getMatchCore___redArg(v_root_3978_, v_e_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed(lean_object* v_00_u03b1_3987_, lean_object* v_root_3988_, lean_object* v_e_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_Meta_LazyDiscrTree_getMatchCore(v_00_u03b1_3987_, v_root_3988_, v_e_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
lean_dec_ref(v_root_3988_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg(lean_object* v_d_3997_, lean_object* v_e_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_roots_4004_; lean_object* v___x_4005_; uint8_t v_foApprox_4006_; uint8_t v_ctxApprox_4007_; uint8_t v_quasiPatternApprox_4008_; uint8_t v_constApprox_4009_; uint8_t v_isDefEqStuckEx_4010_; uint8_t v_unificationHints_4011_; uint8_t v_proofIrrelevance_4012_; uint8_t v_assignSyntheticOpaque_4013_; uint8_t v_offsetCnstrs_4014_; uint8_t v_etaStruct_4015_; uint8_t v_univApprox_4016_; uint8_t v_iota_4017_; uint8_t v_beta_4018_; uint8_t v_proj_4019_; uint8_t v_zeta_4020_; uint8_t v_zetaDelta_4021_; uint8_t v_zetaUnused_4022_; uint8_t v_zetaHave_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4051_; 
v_roots_4004_ = lean_ctor_get(v_d_3997_, 1);
v___x_4005_ = l_Lean_Meta_Context_config(v_a_3999_);
v_foApprox_4006_ = lean_ctor_get_uint8(v___x_4005_, 0);
v_ctxApprox_4007_ = lean_ctor_get_uint8(v___x_4005_, 1);
v_quasiPatternApprox_4008_ = lean_ctor_get_uint8(v___x_4005_, 2);
v_constApprox_4009_ = lean_ctor_get_uint8(v___x_4005_, 3);
v_isDefEqStuckEx_4010_ = lean_ctor_get_uint8(v___x_4005_, 4);
v_unificationHints_4011_ = lean_ctor_get_uint8(v___x_4005_, 5);
v_proofIrrelevance_4012_ = lean_ctor_get_uint8(v___x_4005_, 6);
v_assignSyntheticOpaque_4013_ = lean_ctor_get_uint8(v___x_4005_, 7);
v_offsetCnstrs_4014_ = lean_ctor_get_uint8(v___x_4005_, 8);
v_etaStruct_4015_ = lean_ctor_get_uint8(v___x_4005_, 10);
v_univApprox_4016_ = lean_ctor_get_uint8(v___x_4005_, 11);
v_iota_4017_ = lean_ctor_get_uint8(v___x_4005_, 12);
v_beta_4018_ = lean_ctor_get_uint8(v___x_4005_, 13);
v_proj_4019_ = lean_ctor_get_uint8(v___x_4005_, 14);
v_zeta_4020_ = lean_ctor_get_uint8(v___x_4005_, 15);
v_zetaDelta_4021_ = lean_ctor_get_uint8(v___x_4005_, 16);
v_zetaUnused_4022_ = lean_ctor_get_uint8(v___x_4005_, 17);
v_zetaHave_4023_ = lean_ctor_get_uint8(v___x_4005_, 18);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4025_ = v___x_4005_;
v_isShared_4026_ = v_isSharedCheck_4051_;
goto v_resetjp_4024_;
}
else
{
lean_dec(v___x_4005_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4051_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
uint8_t v_trackZetaDelta_4027_; lean_object* v_zetaDeltaSet_4028_; lean_object* v_lctx_4029_; lean_object* v_localInstances_4030_; lean_object* v_defEqCtx_x3f_4031_; lean_object* v_synthPendingDepth_4032_; lean_object* v_canUnfold_x3f_4033_; uint8_t v_univApprox_4034_; uint8_t v_inTypeClassResolution_4035_; uint8_t v_cacheInferType_4036_; uint8_t v___x_4037_; lean_object* v_config_4039_; 
v_trackZetaDelta_4027_ = lean_ctor_get_uint8(v_a_3999_, sizeof(void*)*7);
v_zetaDeltaSet_4028_ = lean_ctor_get(v_a_3999_, 1);
v_lctx_4029_ = lean_ctor_get(v_a_3999_, 2);
v_localInstances_4030_ = lean_ctor_get(v_a_3999_, 3);
v_defEqCtx_x3f_4031_ = lean_ctor_get(v_a_3999_, 4);
v_synthPendingDepth_4032_ = lean_ctor_get(v_a_3999_, 5);
v_canUnfold_x3f_4033_ = lean_ctor_get(v_a_3999_, 6);
v_univApprox_4034_ = lean_ctor_get_uint8(v_a_3999_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4035_ = lean_ctor_get_uint8(v_a_3999_, sizeof(void*)*7 + 2);
v_cacheInferType_4036_ = lean_ctor_get_uint8(v_a_3999_, sizeof(void*)*7 + 3);
v___x_4037_ = 2;
if (v_isShared_4026_ == 0)
{
v_config_4039_ = v___x_4025_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 0, v_foApprox_4006_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 1, v_ctxApprox_4007_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 2, v_quasiPatternApprox_4008_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 3, v_constApprox_4009_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 4, v_isDefEqStuckEx_4010_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 5, v_unificationHints_4011_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 6, v_proofIrrelevance_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 7, v_assignSyntheticOpaque_4013_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 8, v_offsetCnstrs_4014_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 10, v_etaStruct_4015_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 11, v_univApprox_4016_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 12, v_iota_4017_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 13, v_beta_4018_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 14, v_proj_4019_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 15, v_zeta_4020_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 16, v_zetaDelta_4021_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 17, v_zetaUnused_4022_);
lean_ctor_set_uint8(v_reuseFailAlloc_4050_, 18, v_zetaHave_4023_);
v_config_4039_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
uint64_t v___x_4040_; uint64_t v___x_4041_; uint64_t v___x_4042_; lean_object* v___x_4043_; uint64_t v___x_4044_; uint64_t v___x_4045_; uint64_t v_key_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
lean_ctor_set_uint8(v_config_4039_, 9, v___x_4037_);
v___x_4040_ = l_Lean_Meta_Context_configKey(v_a_3999_);
v___x_4041_ = 2ULL;
v___x_4042_ = lean_uint64_shift_right(v___x_4040_, v___x_4041_);
lean_inc_ref(v_roots_4004_);
v___x_4043_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getMatchCore___boxed), 9, 3);
lean_closure_set(v___x_4043_, 0, lean_box(0));
lean_closure_set(v___x_4043_, 1, v_roots_4004_);
lean_closure_set(v___x_4043_, 2, v_e_3998_);
v___x_4044_ = lean_uint64_shift_left(v___x_4042_, v___x_4041_);
v___x_4045_ = lean_uint64_once(&l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_runMatch___redArg___closed__0);
v_key_4046_ = lean_uint64_lor(v___x_4044_, v___x_4045_);
v___x_4047_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4047_, 0, v_config_4039_);
lean_ctor_set_uint64(v___x_4047_, sizeof(void*)*1, v_key_4046_);
lean_inc(v_canUnfold_x3f_4033_);
lean_inc(v_synthPendingDepth_4032_);
lean_inc(v_defEqCtx_x3f_4031_);
lean_inc_ref(v_localInstances_4030_);
lean_inc_ref(v_lctx_4029_);
lean_inc(v_zetaDeltaSet_4028_);
v___x_4048_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
lean_ctor_set(v___x_4048_, 1, v_zetaDeltaSet_4028_);
lean_ctor_set(v___x_4048_, 2, v_lctx_4029_);
lean_ctor_set(v___x_4048_, 3, v_localInstances_4030_);
lean_ctor_set(v___x_4048_, 4, v_defEqCtx_x3f_4031_);
lean_ctor_set(v___x_4048_, 5, v_synthPendingDepth_4032_);
lean_ctor_set(v___x_4048_, 6, v_canUnfold_x3f_4033_);
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*7, v_trackZetaDelta_4027_);
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*7 + 1, v_univApprox_4034_);
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4035_);
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*7 + 3, v_cacheInferType_4036_);
v___x_4049_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_d_3997_, v___x_4043_, v___x_4048_, v_a_4000_, v_a_4001_, v_a_4002_);
lean_dec_ref(v___x_4048_);
return v___x_4049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___redArg___boxed(lean_object* v_d_4052_, lean_object* v_e_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4052_, v_e_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch(lean_object* v_00_u03b1_4060_, lean_object* v_d_4061_, lean_object* v_e_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_d_4061_, v_e_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getMatch___boxed(lean_object* v_00_u03b1_4069_, lean_object* v_d_4070_, lean_object* v_e_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Lean_Meta_LazyDiscrTree_getMatch(v_00_u03b1_4069_, v_d_4070_, v_e_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec_ref(v_a_4072_);
return v_res_4077_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1(void){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4080_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__0));
v___x_4081_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v___x_4080_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_object* v_a_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default___closed__1);
return v___x_4084_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0(void){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree_default(lean_box(0));
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree(lean_object* v_a_4086_){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedPreDiscrTree___closed__0);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(lean_object* v_d_4088_, lean_object* v_k_4089_, lean_object* v_f_4090_){
_start:
{
lean_object* v_roots_4091_; lean_object* v_tries_4092_; lean_object* v___x_4093_; 
v_roots_4091_ = lean_ctor_get(v_d_4088_, 0);
v_tries_4092_ = lean_ctor_get(v_d_4088_, 1);
v___x_4093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__1___redArg(v_roots_4091_, v_k_4089_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4105_; 
lean_inc_ref(v_tries_4092_);
lean_inc_ref(v_roots_4091_);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_d_4088_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; lean_object* v_unused_4107_; 
v_unused_4106_ = lean_ctor_get(v_d_4088_, 1);
lean_dec(v_unused_4106_);
v_unused_4107_ = lean_ctor_get(v_d_4088_, 0);
lean_dec(v_unused_4107_);
v___x_4095_ = v_d_4088_;
v_isShared_4096_ = v_isSharedCheck_4105_;
goto v_resetjp_4094_;
}
else
{
lean_dec(v_d_4088_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4105_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4097_; lean_object* v_roots_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4103_; 
v___x_4097_ = lean_array_get_size(v_tries_4092_);
v_roots_4098_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_roots_4091_, v_k_4089_, v___x_4097_);
v___x_4099_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_evalNode___redArg___closed__0));
v___x_4100_ = lean_apply_1(v_f_4090_, v___x_4099_);
v___x_4101_ = lean_array_push(v_tries_4092_, v___x_4100_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 1, v___x_4101_);
lean_ctor_set(v___x_4095_, 0, v_roots_4098_);
v___x_4103_ = v___x_4095_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_roots_4098_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
else
{
lean_object* v_val_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
lean_dec(v_k_4089_);
v_val_4108_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_val_4108_);
lean_dec_ref(v___x_4093_);
v___x_4109_ = lean_array_get_size(v_tries_4092_);
v___x_4110_ = lean_nat_dec_lt(v_val_4108_, v___x_4109_);
if (v___x_4110_ == 0)
{
lean_dec(v_val_4108_);
lean_dec_ref(v_f_4090_);
return v_d_4088_;
}
else
{
lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4122_; 
lean_inc_ref(v_tries_4092_);
lean_inc_ref(v_roots_4091_);
v_isSharedCheck_4122_ = !lean_is_exclusive(v_d_4088_);
if (v_isSharedCheck_4122_ == 0)
{
lean_object* v_unused_4123_; lean_object* v_unused_4124_; 
v_unused_4123_ = lean_ctor_get(v_d_4088_, 1);
lean_dec(v_unused_4123_);
v_unused_4124_ = lean_ctor_get(v_d_4088_, 0);
lean_dec(v_unused_4124_);
v___x_4112_ = v_d_4088_;
v_isShared_4113_ = v_isSharedCheck_4122_;
goto v_resetjp_4111_;
}
else
{
lean_dec(v_d_4088_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4122_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v_v_4114_; lean_object* v___x_4115_; lean_object* v_xs_x27_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
v_v_4114_ = lean_array_fget(v_tries_4092_, v_val_4108_);
v___x_4115_ = lean_box(0);
v_xs_x27_4116_ = lean_array_fset(v_tries_4092_, v_val_4108_, v___x_4115_);
v___x_4117_ = lean_apply_1(v_f_4090_, v_v_4114_);
v___x_4118_ = lean_array_fset(v_xs_x27_4116_, v_val_4108_, v___x_4117_);
lean_dec(v_val_4108_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 1, v___x_4118_);
v___x_4120_ = v___x_4112_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_roots_4091_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt(lean_object* v_00_u03b1_4125_, lean_object* v_d_4126_, lean_object* v_k_4127_, lean_object* v_f_4128_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4126_, v_k_4127_, v_f_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0(lean_object* v_e_4130_, lean_object* v_x_4131_){
_start:
{
lean_object* v___x_4132_; 
v___x_4132_ = lean_array_push(v_x_4131_, v_e_4130_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(lean_object* v_d_4133_, lean_object* v_k_4134_, lean_object* v_e_4135_){
_start:
{
lean_object* v___f_4136_; lean_object* v___x_4137_; 
v___f_4136_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4136_, 0, v_e_4135_);
v___x_4137_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_d_4133_, v_k_4134_, v___f_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push(lean_object* v_00_u03b1_4138_, lean_object* v_d_4139_, lean_object* v_k_4140_, lean_object* v_e_4141_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_d_4139_, v_k_4140_, v_e_4141_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(size_t v_sz_4143_, size_t v_i_4144_, lean_object* v_bs_4145_){
_start:
{
uint8_t v___x_4146_; 
v___x_4146_ = lean_usize_dec_lt(v_i_4144_, v_sz_4143_);
if (v___x_4146_ == 0)
{
return v_bs_4145_;
}
else
{
lean_object* v_v_4147_; lean_object* v___x_4148_; lean_object* v_bs_x27_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; size_t v___x_4153_; size_t v___x_4154_; lean_object* v___x_4155_; 
v_v_4147_ = lean_array_uget(v_bs_4145_, v_i_4144_);
v___x_4148_ = lean_unsigned_to_nat(0u);
v_bs_x27_4149_ = lean_array_uset(v_bs_4145_, v_i_4144_, v___x_4148_);
v___x_4150_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__0));
v___x_4151_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4150_);
lean_ctor_set(v___x_4152_, 1, v___x_4148_);
lean_ctor_set(v___x_4152_, 2, v___x_4151_);
lean_ctor_set(v___x_4152_, 3, v_v_4147_);
v___x_4153_ = ((size_t)1ULL);
v___x_4154_ = lean_usize_add(v_i_4144_, v___x_4153_);
v___x_4155_ = lean_array_uset(v_bs_x27_4149_, v_i_4144_, v___x_4152_);
v_i_4144_ = v___x_4154_;
v_bs_4145_ = v___x_4155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg___boxed(lean_object* v_sz_4157_, lean_object* v_i_4158_, lean_object* v_bs_4159_){
_start:
{
size_t v_sz_boxed_4160_; size_t v_i_boxed_4161_; lean_object* v_res_4162_; 
v_sz_boxed_4160_ = lean_unbox_usize(v_sz_4157_);
lean_dec(v_sz_4157_);
v_i_boxed_4161_ = lean_unbox_usize(v_i_4158_);
lean_dec(v_i_4158_);
v_res_4162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_boxed_4160_, v_i_boxed_4161_, v_bs_4159_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(lean_object* v_x_4163_, lean_object* v_x_4164_){
_start:
{
if (lean_obj_tag(v_x_4164_) == 0)
{
return v_x_4163_;
}
else
{
lean_object* v_key_4165_; lean_object* v_value_4166_; lean_object* v_tail_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v_key_4165_ = lean_ctor_get(v_x_4164_, 0);
lean_inc(v_key_4165_);
v_value_4166_ = lean_ctor_get(v_x_4164_, 1);
lean_inc(v_value_4166_);
v_tail_4167_ = lean_ctor_get(v_x_4164_, 2);
lean_inc(v_tail_4167_);
lean_dec_ref(v_x_4164_);
v___x_4168_ = lean_unsigned_to_nat(1u);
v___x_4169_ = lean_nat_add(v_value_4166_, v___x_4168_);
lean_dec(v_value_4166_);
v___x_4170_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_LazyDiscrTree_evalLazyEntry_spec__3___redArg(v_x_4163_, v_key_4165_, v___x_4169_);
v_x_4163_ = v___x_4170_;
v_x_4164_ = v_tail_4167_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(lean_object* v_as_4172_, size_t v_i_4173_, size_t v_stop_4174_, lean_object* v_b_4175_){
_start:
{
uint8_t v___x_4176_; 
v___x_4176_ = lean_usize_dec_eq(v_i_4173_, v_stop_4174_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; lean_object* v___x_4178_; size_t v___x_4179_; size_t v___x_4180_; 
v___x_4177_ = lean_array_uget_borrowed(v_as_4172_, v_i_4173_);
lean_inc(v___x_4177_);
v___x_4178_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__1(v_b_4175_, v___x_4177_);
v___x_4179_ = ((size_t)1ULL);
v___x_4180_ = lean_usize_add(v_i_4173_, v___x_4179_);
v_i_4173_ = v___x_4180_;
v_b_4175_ = v___x_4178_;
goto _start;
}
else
{
return v_b_4175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2___boxed(lean_object* v_as_4182_, lean_object* v_i_4183_, lean_object* v_stop_4184_, lean_object* v_b_4185_){
_start:
{
size_t v_i_boxed_4186_; size_t v_stop_boxed_4187_; lean_object* v_res_4188_; 
v_i_boxed_4186_ = lean_unbox_usize(v_i_4183_);
lean_dec(v_i_4183_);
v_stop_boxed_4187_ = lean_unbox_usize(v_stop_4184_);
lean_dec(v_stop_4184_);
v_res_4188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_as_4182_, v_i_boxed_4186_, v_stop_boxed_4187_, v_b_4185_);
lean_dec_ref(v_as_4182_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(lean_object* v_d_4189_){
_start:
{
lean_object* v_roots_4190_; lean_object* v_tries_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4218_; 
v_roots_4190_ = lean_ctor_get(v_d_4189_, 0);
v_tries_4191_ = lean_ctor_get(v_d_4189_, 1);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_d_4189_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4193_ = v_d_4189_;
v_isShared_4194_ = v_isSharedCheck_4218_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_tries_4191_);
lean_inc(v_roots_4190_);
lean_dec(v_d_4189_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4218_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___y_4196_; lean_object* v_buckets_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v_buckets_4207_ = lean_ctor_get(v_roots_4190_, 1);
v___x_4208_ = lean_unsigned_to_nat(0u);
v___x_4209_ = lean_array_get_size(v_buckets_4207_);
v___x_4210_ = lean_nat_dec_lt(v___x_4208_, v___x_4209_);
if (v___x_4210_ == 0)
{
v___y_4196_ = v_roots_4190_;
goto v___jp_4195_;
}
else
{
uint8_t v___x_4211_; 
v___x_4211_ = lean_nat_dec_le(v___x_4209_, v___x_4209_);
if (v___x_4211_ == 0)
{
if (v___x_4210_ == 0)
{
v___y_4196_ = v_roots_4190_;
goto v___jp_4195_;
}
else
{
size_t v___x_4212_; size_t v___x_4213_; lean_object* v___x_4214_; 
lean_inc_ref(v_buckets_4207_);
v___x_4212_ = ((size_t)0ULL);
v___x_4213_ = lean_usize_of_nat(v___x_4209_);
v___x_4214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4207_, v___x_4212_, v___x_4213_, v_roots_4190_);
lean_dec_ref(v_buckets_4207_);
v___y_4196_ = v___x_4214_;
goto v___jp_4195_;
}
}
else
{
size_t v___x_4215_; size_t v___x_4216_; lean_object* v___x_4217_; 
lean_inc_ref(v_buckets_4207_);
v___x_4215_ = ((size_t)0ULL);
v___x_4216_ = lean_usize_of_nat(v___x_4209_);
v___x_4217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__2(v_buckets_4207_, v___x_4215_, v___x_4216_, v_roots_4190_);
lean_dec_ref(v_buckets_4207_);
v___y_4196_ = v___x_4217_;
goto v___jp_4195_;
}
}
v___jp_4195_:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; size_t v_sz_4200_; size_t v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4205_; 
v___x_4197_ = lean_unsigned_to_nat(1u);
v___x_4198_ = lean_mk_empty_array_with_capacity(v___x_4197_);
lean_dec_ref(v___x_4198_);
v___x_4199_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0, &l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabited___closed__0);
v_sz_4200_ = lean_array_size(v_tries_4191_);
v___x_4201_ = ((size_t)0ULL);
v___x_4202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4200_, v___x_4201_, v_tries_4191_);
v___x_4203_ = l_Array_append___redArg(v___x_4199_, v___x_4202_);
lean_dec_ref(v___x_4202_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 1, v___y_4196_);
lean_ctor_set(v___x_4193_, 0, v___x_4203_);
v___x_4205_ = v___x_4193_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4203_);
lean_ctor_set(v_reuseFailAlloc_4206_, 1, v___y_4196_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy(lean_object* v_00_u03b1_4219_, lean_object* v_d_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_d_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(lean_object* v_00_u03b1_4222_, size_t v_sz_4223_, size_t v_i_4224_, lean_object* v_bs_4225_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___redArg(v_sz_4223_, v_i_4224_, v_bs_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0___boxed(lean_object* v_00_u03b1_4227_, lean_object* v_sz_4228_, lean_object* v_i_4229_, lean_object* v_bs_4230_){
_start:
{
size_t v_sz_boxed_4231_; size_t v_i_boxed_4232_; lean_object* v_res_4233_; 
v_sz_boxed_4231_ = lean_unbox_usize(v_sz_4228_);
lean_dec(v_sz_4228_);
v_i_boxed_4232_ = lean_unbox_usize(v_i_4229_);
lean_dec(v_i_4229_);
v_res_4233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy_spec__0(v_00_u03b1_4227_, v_sz_boxed_4231_, v_i_boxed_4232_, v_bs_4230_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(lean_object* v_y_4234_, lean_object* v_x_4235_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Array_append___redArg(v_x_4235_, v_y_4234_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0___boxed(lean_object* v_y_4237_, lean_object* v_x_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___lam__0(v_y_4237_, v_x_4238_);
lean_dec_ref(v_y_4237_);
return v_res_4239_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l_Array_instInhabited(lean_box(0));
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(lean_object* v_tries_4241_, lean_object* v_snd_4242_, lean_object* v_x_4243_, lean_object* v_x_4244_){
_start:
{
if (lean_obj_tag(v_x_4244_) == 0)
{
lean_dec_ref(v_snd_4242_);
return v_x_4243_;
}
else
{
lean_object* v_key_4245_; lean_object* v_value_4246_; lean_object* v_tail_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v_key_4245_ = lean_ctor_get(v_x_4244_, 0);
lean_inc(v_key_4245_);
v_value_4246_ = lean_ctor_get(v_x_4244_, 1);
lean_inc(v_value_4246_);
v_tail_4247_ = lean_ctor_get(v_x_4244_, 2);
lean_inc(v_tail_4247_);
lean_dec_ref(v_x_4244_);
v___x_4248_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___closed__0);
v___x_4249_ = lean_array_get_borrowed(v___x_4248_, v_tries_4241_, v_value_4246_);
lean_dec(v_value_4246_);
lean_inc_ref(v_snd_4242_);
lean_inc(v___x_4249_);
v___x_4250_ = lean_apply_1(v_snd_4242_, v___x_4249_);
v___x_4251_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_modifyAt___redArg(v_x_4243_, v_key_4245_, v___x_4250_);
v_x_4243_ = v___x_4251_;
v_x_4244_ = v_tail_4247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg___boxed(lean_object* v_tries_4253_, lean_object* v_snd_4254_, lean_object* v_x_4255_, lean_object* v_x_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4253_, v_snd_4254_, v_x_4255_, v_x_4256_);
lean_dec_ref(v_tries_4253_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(lean_object* v_tries_4258_, lean_object* v_snd_4259_, lean_object* v_as_4260_, size_t v_i_4261_, size_t v_stop_4262_, lean_object* v_b_4263_){
_start:
{
uint8_t v___x_4264_; 
v___x_4264_ = lean_usize_dec_eq(v_i_4261_, v_stop_4262_);
if (v___x_4264_ == 0)
{
lean_object* v___x_4265_; lean_object* v___x_4266_; size_t v___x_4267_; size_t v___x_4268_; 
v___x_4265_ = lean_array_uget_borrowed(v_as_4260_, v_i_4261_);
lean_inc(v___x_4265_);
lean_inc_ref(v_snd_4259_);
v___x_4266_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4258_, v_snd_4259_, v_b_4263_, v___x_4265_);
v___x_4267_ = ((size_t)1ULL);
v___x_4268_ = lean_usize_add(v_i_4261_, v___x_4267_);
v_i_4261_ = v___x_4268_;
v_b_4263_ = v___x_4266_;
goto _start;
}
else
{
lean_dec_ref(v_snd_4259_);
return v_b_4263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg___boxed(lean_object* v_tries_4270_, lean_object* v_snd_4271_, lean_object* v_as_4272_, lean_object* v_i_4273_, lean_object* v_stop_4274_, lean_object* v_b_4275_){
_start:
{
size_t v_i_boxed_4276_; size_t v_stop_boxed_4277_; lean_object* v_res_4278_; 
v_i_boxed_4276_ = lean_unbox_usize(v_i_4273_);
lean_dec(v_i_4273_);
v_stop_boxed_4277_ = lean_unbox_usize(v_stop_4274_);
lean_dec(v_stop_4274_);
v_res_4278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4270_, v_snd_4271_, v_as_4272_, v_i_boxed_4276_, v_stop_boxed_4277_, v_b_4275_);
lean_dec_ref(v_as_4272_);
lean_dec_ref(v_tries_4270_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(lean_object* v_x_4281_, lean_object* v_y_4282_){
_start:
{
lean_object* v_fst_4284_; lean_object* v_buckets_4285_; lean_object* v_tries_4286_; lean_object* v_snd_4287_; lean_object* v_roots_4298_; lean_object* v_roots_4299_; lean_object* v_tries_4300_; lean_object* v_size_4301_; lean_object* v_buckets_4302_; lean_object* v_tries_4303_; lean_object* v_size_4304_; lean_object* v_buckets_4305_; uint8_t v___x_4306_; 
v_roots_4298_ = lean_ctor_get(v_y_4282_, 0);
v_roots_4299_ = lean_ctor_get(v_x_4281_, 0);
v_tries_4300_ = lean_ctor_get(v_y_4282_, 1);
v_size_4301_ = lean_ctor_get(v_roots_4298_, 0);
v_buckets_4302_ = lean_ctor_get(v_roots_4298_, 1);
v_tries_4303_ = lean_ctor_get(v_x_4281_, 1);
v_size_4304_ = lean_ctor_get(v_roots_4299_, 0);
v_buckets_4305_ = lean_ctor_get(v_roots_4299_, 1);
v___x_4306_ = lean_nat_dec_le(v_size_4301_, v_size_4304_);
if (v___x_4306_ == 0)
{
lean_object* v___f_4307_; 
lean_inc_ref(v_buckets_4305_);
lean_inc_ref(v_tries_4303_);
lean_dec_ref(v_x_4281_);
v___f_4307_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__0));
v_fst_4284_ = v_y_4282_;
v_buckets_4285_ = v_buckets_4305_;
v_tries_4286_ = v_tries_4303_;
v_snd_4287_ = v___f_4307_;
goto v___jp_4283_;
}
else
{
lean_object* v___f_4308_; 
lean_inc_ref(v_buckets_4302_);
lean_inc_ref(v_tries_4300_);
lean_dec_ref(v_y_4282_);
v___f_4308_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg___closed__1));
v_fst_4284_ = v_x_4281_;
v_buckets_4285_ = v_buckets_4302_;
v_tries_4286_ = v_tries_4300_;
v_snd_4287_ = v___f_4308_;
goto v___jp_4283_;
}
v___jp_4283_:
{
lean_object* v___x_4288_; lean_object* v___x_4289_; uint8_t v___x_4290_; 
v___x_4288_ = lean_unsigned_to_nat(0u);
v___x_4289_ = lean_array_get_size(v_buckets_4285_);
v___x_4290_ = lean_nat_dec_lt(v___x_4288_, v___x_4289_);
if (v___x_4290_ == 0)
{
lean_dec_ref(v_tries_4286_);
lean_dec_ref(v_buckets_4285_);
return v_fst_4284_;
}
else
{
uint8_t v___x_4291_; 
v___x_4291_ = lean_nat_dec_le(v___x_4289_, v___x_4289_);
if (v___x_4291_ == 0)
{
if (v___x_4290_ == 0)
{
lean_dec_ref(v_tries_4286_);
lean_dec_ref(v_buckets_4285_);
return v_fst_4284_;
}
else
{
size_t v___x_4292_; size_t v___x_4293_; lean_object* v___x_4294_; 
v___x_4292_ = ((size_t)0ULL);
v___x_4293_ = lean_usize_of_nat(v___x_4289_);
lean_inc_ref(v_snd_4287_);
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4286_, v_snd_4287_, v_buckets_4285_, v___x_4292_, v___x_4293_, v_fst_4284_);
lean_dec_ref(v_buckets_4285_);
lean_dec_ref(v_tries_4286_);
return v___x_4294_;
}
}
else
{
size_t v___x_4295_; size_t v___x_4296_; lean_object* v___x_4297_; 
v___x_4295_ = ((size_t)0ULL);
v___x_4296_ = lean_usize_of_nat(v___x_4289_);
lean_inc_ref(v_snd_4287_);
v___x_4297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4286_, v_snd_4287_, v_buckets_4285_, v___x_4295_, v___x_4296_, v_fst_4284_);
lean_dec_ref(v_buckets_4285_);
lean_dec_ref(v_tries_4286_);
return v___x_4297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append(lean_object* v_00_u03b1_4309_, lean_object* v_x_4310_, lean_object* v_y_4311_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_x_4310_, v_y_4311_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(lean_object* v_00_u03b1_4313_, lean_object* v_tries_4314_, lean_object* v_snd_4315_, lean_object* v_x_4316_, lean_object* v_x_4317_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___redArg(v_tries_4314_, v_snd_4315_, v_x_4316_, v_x_4317_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0___boxed(lean_object* v_00_u03b1_4319_, lean_object* v_tries_4320_, lean_object* v_snd_4321_, lean_object* v_x_4322_, lean_object* v_x_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__0(v_00_u03b1_4319_, v_tries_4320_, v_snd_4321_, v_x_4322_, v_x_4323_);
lean_dec_ref(v_tries_4320_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(lean_object* v_00_u03b1_4325_, lean_object* v_tries_4326_, lean_object* v_snd_4327_, lean_object* v_as_4328_, size_t v_i_4329_, size_t v_stop_4330_, lean_object* v_b_4331_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___redArg(v_tries_4326_, v_snd_4327_, v_as_4328_, v_i_4329_, v_stop_4330_, v_b_4331_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1___boxed(lean_object* v_00_u03b1_4333_, lean_object* v_tries_4334_, lean_object* v_snd_4335_, lean_object* v_as_4336_, lean_object* v_i_4337_, lean_object* v_stop_4338_, lean_object* v_b_4339_){
_start:
{
size_t v_i_boxed_4340_; size_t v_stop_boxed_4341_; lean_object* v_res_4342_; 
v_i_boxed_4340_ = lean_unbox_usize(v_i_4337_);
lean_dec(v_i_4337_);
v_stop_boxed_4341_ = lean_unbox_usize(v_stop_4338_);
lean_dec(v_stop_4338_);
v_res_4342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_PreDiscrTree_append_spec__1(v_00_u03b1_4333_, v_tries_4334_, v_snd_4335_, v_as_4336_, v_i_boxed_4340_, v_stop_boxed_4341_, v_b_4339_);
lean_dec_ref(v_as_4336_);
lean_dec_ref(v_tries_4334_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend(lean_object* v_00_u03b1_4344_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_PreDiscrTree_instAppend___closed__0));
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object* v_expr_4346_, lean_object* v_value_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Lean_Meta_LazyDiscrTree_rootKey(v_expr_4346_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4375_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4356_ = v___x_4353_;
v_isShared_4357_ = v_isSharedCheck_4375_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4353_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4375_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v_fst_4358_; lean_object* v_snd_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4374_; 
v_fst_4358_ = lean_ctor_get(v_a_4354_, 0);
v_snd_4359_ = lean_ctor_get(v_a_4354_, 1);
v_isSharedCheck_4374_ = !lean_is_exclusive(v_a_4354_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4361_ = v_a_4354_;
v_isShared_4362_ = v_isSharedCheck_4374_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_snd_4359_);
lean_inc(v_fst_4358_);
lean_dec(v_a_4354_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4374_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v_lctx_4363_; lean_object* v_localInstances_4364_; lean_object* v___x_4366_; 
v_lctx_4363_ = lean_ctor_get(v_a_4348_, 2);
v_localInstances_4364_ = lean_ctor_get(v_a_4348_, 3);
lean_inc_ref(v_localInstances_4364_);
lean_inc_ref(v_lctx_4363_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 1, v_localInstances_4364_);
lean_ctor_set(v___x_4361_, 0, v_lctx_4363_);
v___x_4366_ = v___x_4361_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_lctx_4363_);
lean_ctor_set(v_reuseFailAlloc_4373_, 1, v_localInstances_4364_);
v___x_4366_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4371_; 
v___x_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
lean_ctor_set(v___x_4367_, 1, v_value_4347_);
v___x_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4368_, 0, v_snd_4359_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4369_, 0, v_fst_4358_);
lean_ctor_set(v___x_4369_, 1, v___x_4368_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v___x_4369_);
v___x_4371_ = v___x_4356_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4369_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec(v_value_4347_);
v_a_4376_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4353_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4353_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg___boxed(lean_object* v_expr_4384_, lean_object* v_value_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4384_, v_value_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(lean_object* v_00_u03b1_4392_, lean_object* v_expr_4393_, lean_object* v_value_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_expr_4393_, v_value_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___boxed(lean_object* v_00_u03b1_4401_, lean_object* v_expr_4402_, lean_object* v_value_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr(v_00_u03b1_4401_, v_expr_4402_, v_value_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
lean_dec(v_a_4405_);
lean_dec_ref(v_a_4404_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object* v_e_4410_, lean_object* v_idx_4411_, lean_object* v_value_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_){
_start:
{
lean_object* v_entry_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4464_; 
v_entry_4418_ = lean_ctor_get(v_e_4410_, 1);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_e_4410_);
if (v_isSharedCheck_4464_ == 0)
{
lean_object* v_unused_4465_; 
v_unused_4465_ = lean_ctor_get(v_e_4410_, 0);
lean_dec(v_unused_4465_);
v___x_4420_ = v_e_4410_;
v_isShared_4421_ = v_isSharedCheck_4464_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_entry_4418_);
lean_dec(v_e_4410_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4464_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v_snd_4422_; lean_object* v_fst_4423_; lean_object* v_fst_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4462_; 
v_snd_4422_ = lean_ctor_get(v_entry_4418_, 1);
lean_inc(v_snd_4422_);
v_fst_4423_ = lean_ctor_get(v_entry_4418_, 0);
lean_inc(v_fst_4423_);
lean_dec_ref(v_entry_4418_);
v_fst_4424_ = lean_ctor_get(v_snd_4422_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_snd_4422_);
if (v_isSharedCheck_4462_ == 0)
{
lean_object* v_unused_4463_; 
v_unused_4463_ = lean_ctor_get(v_snd_4422_, 1);
lean_dec(v_unused_4463_);
v___x_4426_ = v_snd_4422_;
v_isShared_4427_ = v_isSharedCheck_4462_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_fst_4424_);
lean_dec(v_snd_4422_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4462_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4428_ = l_Lean_instInhabitedExpr;
v___x_4429_ = lean_array_get(v___x_4428_, v_fst_4423_, v_idx_4411_);
lean_dec(v_fst_4423_);
v___x_4430_ = l_Lean_Meta_LazyDiscrTree_rootKey(v___x_4429_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4453_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4433_ = v___x_4430_;
v_isShared_4434_ = v_isSharedCheck_4453_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4453_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v_fst_4435_; lean_object* v_snd_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4452_; 
v_fst_4435_ = lean_ctor_get(v_a_4431_, 0);
v_snd_4436_ = lean_ctor_get(v_a_4431_, 1);
v_isSharedCheck_4452_ = !lean_is_exclusive(v_a_4431_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4438_ = v_a_4431_;
v_isShared_4439_ = v_isSharedCheck_4452_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_snd_4436_);
lean_inc(v_fst_4435_);
lean_dec(v_a_4431_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4452_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 1, v_value_4412_);
lean_ctor_set(v___x_4438_, 0, v_fst_4424_);
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_fst_4424_);
lean_ctor_set(v_reuseFailAlloc_4451_, 1, v_value_4412_);
v___x_4441_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
lean_object* v___x_4443_; 
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 1, v___x_4441_);
lean_ctor_set(v___x_4426_, 0, v_snd_4436_);
v___x_4443_ = v___x_4426_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_snd_4436_);
lean_ctor_set(v_reuseFailAlloc_4450_, 1, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
lean_object* v___x_4445_; 
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 1, v___x_4443_);
lean_ctor_set(v___x_4420_, 0, v_fst_4435_);
v___x_4445_ = v___x_4420_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_fst_4435_);
lean_ctor_set(v_reuseFailAlloc_4449_, 1, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4447_; 
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 0, v___x_4445_);
v___x_4447_ = v___x_4433_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_del_object(v___x_4426_);
lean_dec(v_fst_4424_);
lean_del_object(v___x_4420_);
lean_dec(v_value_4412_);
v_a_4454_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4430_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4430_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg___boxed(lean_object* v_e_4466_, lean_object* v_idx_4467_, lean_object* v_value_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4466_, v_idx_4467_, v_value_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
lean_dec(v_a_4472_);
lean_dec_ref(v_a_4471_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_idx_4467_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(lean_object* v_00_u03b1_4475_, lean_object* v_e_4476_, lean_object* v_idx_4477_, lean_object* v_value_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v___x_4484_; 
v___x_4484_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_e_4476_, v_idx_4477_, v_value_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___boxed(lean_object* v_00_u03b1_4485_, lean_object* v_e_4486_, lean_object* v_idx_4487_, lean_object* v_value_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry(v_00_u03b1_4485_, v_e_4486_, v_idx_4487_, v_value_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
lean_dec(v_a_4492_);
lean_dec_ref(v_a_4491_);
lean_dec(v_a_4490_);
lean_dec_ref(v_a_4489_);
lean_dec(v_idx_4487_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new(){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
v___x_4498_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4499_ = lean_st_mk_ref(v___x_4498_);
return v___x_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_ImportData_new___boxed(lean_object* v_a_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
return v_res_4501_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0(void){
_start:
{
lean_object* v___x_4502_; 
v___x_4502_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4502_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1(void){
_start:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4503_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__0);
v___x_4504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
return v___x_4504_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4505_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
return v___x_4506_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3(void){
_start:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4507_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__1);
v___x_4508_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4507_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
lean_ctor_set(v___x_4508_, 2, v___x_4507_);
lean_ctor_set(v___x_4508_, 3, v___x_4507_);
lean_ctor_set(v___x_4508_, 4, v___x_4507_);
lean_ctor_set(v___x_4508_, 5, v___x_4507_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_Cache_empty(lean_object* v_ngen_4509_){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4510_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__2);
v___x_4511_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3, &l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_Cache_empty___closed__3);
v___x_4512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4512_, 0, v_ngen_4509_);
lean_ctor_set(v___x_4512_, 1, v___x_4510_);
lean_ctor_set(v___x_4512_, 2, v___x_4511_);
return v___x_4512_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(lean_object* v_env_4513_, lean_object* v_declName_4514_){
_start:
{
uint8_t v___x_4515_; 
v___x_4515_ = l_Lean_isPrivateName(v_declName_4514_);
if (v___x_4515_ == 0)
{
return v___x_4515_;
}
else
{
lean_object* v___x_4516_; 
v___x_4516_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4513_, v_declName_4514_);
if (lean_obj_tag(v___x_4516_) == 0)
{
return v___x_4515_;
}
else
{
lean_object* v_val_4517_; lean_object* v___x_4518_; uint8_t v_isModule_4519_; 
v_val_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_val_4517_);
lean_dec_ref(v___x_4516_);
v___x_4518_ = l_Lean_Environment_header(v_env_4513_);
v_isModule_4519_ = lean_ctor_get_uint8(v___x_4518_, sizeof(void*)*7 + 4);
if (v_isModule_4519_ == 0)
{
lean_dec_ref(v___x_4518_);
lean_dec(v_val_4517_);
return v_isModule_4519_;
}
else
{
lean_object* v_modules_4520_; lean_object* v___x_4521_; uint8_t v___x_4522_; 
v_modules_4520_ = lean_ctor_get(v___x_4518_, 3);
lean_inc_ref(v_modules_4520_);
lean_dec_ref(v___x_4518_);
v___x_4521_ = lean_array_get_size(v_modules_4520_);
v___x_4522_ = lean_nat_dec_lt(v_val_4517_, v___x_4521_);
if (v___x_4522_ == 0)
{
lean_dec_ref(v_modules_4520_);
lean_dec(v_val_4517_);
return v___x_4522_;
}
else
{
lean_object* v___x_4523_; lean_object* v_toImport_4524_; uint8_t v_importAll_4525_; 
v___x_4523_ = lean_array_fget(v_modules_4520_, v_val_4517_);
lean_dec(v_val_4517_);
lean_dec_ref(v_modules_4520_);
v_toImport_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc_ref(v_toImport_4524_);
lean_dec(v___x_4523_);
v_importAll_4525_ = lean_ctor_get_uint8(v_toImport_4524_, sizeof(void*)*1);
lean_dec_ref(v_toImport_4524_);
return v_importAll_4525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName___boxed(lean_object* v_env_4526_, lean_object* v_declName_4527_){
_start:
{
uint8_t v_res_4528_; lean_object* v_r_4529_; 
v_res_4528_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4526_, v_declName_4527_);
lean_dec(v_declName_4527_);
lean_dec_ref(v_env_4526_);
v_r_4529_ = lean_box(v_res_4528_);
return v_r_4529_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LazyDiscrTree_blacklistInsertion(lean_object* v_env_4535_, lean_object* v_declName_4536_){
_start:
{
uint8_t v___x_4537_; 
lean_inc(v_declName_4536_);
lean_inc_ref(v_env_4535_);
v___x_4537_ = l_Lean_Meta_allowCompletion(v_env_4535_, v_declName_4536_);
if (v___x_4537_ == 0)
{
uint8_t v___x_4538_; 
lean_dec(v_declName_4536_);
lean_dec_ref(v_env_4535_);
v___x_4538_ = 1;
return v___x_4538_;
}
else
{
lean_object* v___x_4539_; uint8_t v___x_4540_; uint8_t v___y_4550_; 
v___x_4539_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__1));
v___x_4540_ = lean_name_eq(v_declName_4536_, v___x_4539_);
if (v___x_4540_ == 0)
{
uint8_t v___x_4551_; 
lean_inc(v_declName_4536_);
v___x_4551_ = l_Lean_Name_isInternalDetail(v_declName_4536_);
if (v___x_4551_ == 0)
{
lean_dec_ref(v_env_4535_);
v___y_4550_ = v___x_4551_;
goto v___jp_4549_;
}
else
{
uint8_t v___x_4552_; 
v___x_4552_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_isAccessiblePrivateName(v_env_4535_, v_declName_4536_);
lean_dec_ref(v_env_4535_);
if (v___x_4552_ == 0)
{
v___y_4550_ = v___x_4551_;
goto v___jp_4549_;
}
else
{
goto v___jp_4545_;
}
}
}
else
{
lean_dec(v_declName_4536_);
lean_dec_ref(v_env_4535_);
return v___x_4540_;
}
v___jp_4541_:
{
if (lean_obj_tag(v_declName_4536_) == 1)
{
lean_object* v_str_4542_; lean_object* v___x_4543_; uint8_t v___x_4544_; 
v_str_4542_ = lean_ctor_get(v_declName_4536_, 1);
lean_inc_ref(v_str_4542_);
lean_dec_ref(v_declName_4536_);
v___x_4543_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__2));
v___x_4544_ = lean_string_dec_eq(v_str_4542_, v___x_4543_);
lean_dec_ref(v_str_4542_);
if (v___x_4544_ == 0)
{
return v___x_4540_;
}
else
{
return v___x_4537_;
}
}
else
{
lean_dec(v_declName_4536_);
return v___x_4540_;
}
}
v___jp_4545_:
{
if (lean_obj_tag(v_declName_4536_) == 1)
{
lean_object* v_str_4546_; lean_object* v___x_4547_; uint8_t v___x_4548_; 
v_str_4546_ = lean_ctor_get(v_declName_4536_, 1);
v___x_4547_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_blacklistInsertion___closed__3));
v___x_4548_ = lean_string_dec_eq(v_str_4546_, v___x_4547_);
if (v___x_4548_ == 0)
{
goto v___jp_4541_;
}
else
{
lean_dec_ref(v_declName_4536_);
return v___x_4537_;
}
}
else
{
goto v___jp_4541_;
}
}
v___jp_4549_:
{
if (v___y_4550_ == 0)
{
goto v___jp_4545_;
}
else
{
lean_dec(v_declName_4536_);
return v___y_4550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_blacklistInsertion___boxed(lean_object* v_env_4553_, lean_object* v_declName_4554_){
_start:
{
uint8_t v_res_4555_; lean_object* v_r_4556_; 
v_res_4555_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4553_, v_declName_4554_);
v_r_4556_ = lean_box(v_res_4555_);
return v_r_4556_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(lean_object* v_opts_4557_, lean_object* v_opt_4558_){
_start:
{
lean_object* v_name_4559_; lean_object* v_defValue_4560_; lean_object* v_map_4561_; lean_object* v___x_4562_; 
v_name_4559_ = lean_ctor_get(v_opt_4558_, 0);
v_defValue_4560_ = lean_ctor_get(v_opt_4558_, 1);
v_map_4561_ = lean_ctor_get(v_opts_4557_, 0);
v___x_4562_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4561_, v_name_4559_);
if (lean_obj_tag(v___x_4562_) == 0)
{
uint8_t v___x_4563_; 
v___x_4563_ = lean_unbox(v_defValue_4560_);
return v___x_4563_;
}
else
{
lean_object* v_val_4564_; 
v_val_4564_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_val_4564_);
lean_dec_ref(v___x_4562_);
if (lean_obj_tag(v_val_4564_) == 1)
{
uint8_t v_v_4565_; 
v_v_4565_ = lean_ctor_get_uint8(v_val_4564_, 0);
lean_dec_ref(v_val_4564_);
return v_v_4565_;
}
else
{
uint8_t v___x_4566_; 
lean_dec(v_val_4564_);
v___x_4566_ = lean_unbox(v_defValue_4560_);
return v___x_4566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0___boxed(lean_object* v_opts_4567_, lean_object* v_opt_4568_){
_start:
{
uint8_t v_res_4569_; lean_object* v_r_4570_; 
v_res_4569_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_opts_4567_, v_opt_4568_);
lean_dec_ref(v_opt_4568_);
lean_dec_ref(v_opts_4567_);
v_r_4570_ = lean_box(v_res_4569_);
return v_r_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(lean_object* v_opts_4571_, lean_object* v_opt_4572_){
_start:
{
lean_object* v_name_4573_; lean_object* v_defValue_4574_; lean_object* v_map_4575_; lean_object* v___x_4576_; 
v_name_4573_ = lean_ctor_get(v_opt_4572_, 0);
v_defValue_4574_ = lean_ctor_get(v_opt_4572_, 1);
v_map_4575_ = lean_ctor_get(v_opts_4571_, 0);
v___x_4576_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4575_, v_name_4573_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_inc(v_defValue_4574_);
return v_defValue_4574_;
}
else
{
lean_object* v_val_4577_; 
v_val_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_val_4577_);
lean_dec_ref(v___x_4576_);
if (lean_obj_tag(v_val_4577_) == 3)
{
lean_object* v_v_4578_; 
v_v_4578_ = lean_ctor_get(v_val_4577_, 0);
lean_inc(v_v_4578_);
lean_dec_ref(v_val_4577_);
return v_v_4578_;
}
else
{
lean_dec(v_val_4577_);
lean_inc(v_defValue_4574_);
return v_defValue_4574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1___boxed(lean_object* v_opts_4579_, lean_object* v_opt_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_opts_4579_, v_opt_4580_);
lean_dec_ref(v_opt_4580_);
lean_dec_ref(v_opts_4579_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(lean_object* v_as_4582_, size_t v_i_4583_, size_t v_stop_4584_, lean_object* v_b_4585_){
_start:
{
uint8_t v___x_4586_; 
v___x_4586_ = lean_usize_dec_eq(v_i_4583_, v_stop_4584_);
if (v___x_4586_ == 0)
{
lean_object* v___x_4587_; lean_object* v_key_4588_; lean_object* v_entry_4589_; lean_object* v___x_4590_; size_t v___x_4591_; size_t v___x_4592_; 
v___x_4587_ = lean_array_uget_borrowed(v_as_4582_, v_i_4583_);
v_key_4588_ = lean_ctor_get(v___x_4587_, 0);
v_entry_4589_ = lean_ctor_get(v___x_4587_, 1);
lean_inc_ref(v_entry_4589_);
lean_inc(v_key_4588_);
v___x_4590_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_push___redArg(v_b_4585_, v_key_4588_, v_entry_4589_);
v___x_4591_ = ((size_t)1ULL);
v___x_4592_ = lean_usize_add(v_i_4583_, v___x_4591_);
v_i_4583_ = v___x_4592_;
v_b_4585_ = v___x_4590_;
goto _start;
}
else
{
return v_b_4585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg___boxed(lean_object* v_as_4594_, lean_object* v_i_4595_, lean_object* v_stop_4596_, lean_object* v_b_4597_){
_start:
{
size_t v_i_boxed_4598_; size_t v_stop_boxed_4599_; lean_object* v_res_4600_; 
v_i_boxed_4598_ = lean_unbox_usize(v_i_4595_);
lean_dec(v_i_4595_);
v_stop_boxed_4599_ = lean_unbox_usize(v_stop_4596_);
lean_dec(v_stop_4596_);
v_res_4600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4594_, v_i_boxed_4598_, v_stop_boxed_4599_, v_b_4597_);
lean_dec_ref(v_as_4594_);
return v_res_4600_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0(void){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4601_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1(void){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__0);
v___x_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
return v___x_4603_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2(void){
_start:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4604_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4605_ = lean_unsigned_to_nat(0u);
v___x_4606_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4606_, 0, v___x_4605_);
lean_ctor_set(v___x_4606_, 1, v___x_4605_);
lean_ctor_set(v___x_4606_, 2, v___x_4605_);
lean_ctor_set(v___x_4606_, 3, v___x_4604_);
lean_ctor_set(v___x_4606_, 4, v___x_4604_);
lean_ctor_set(v___x_4606_, 5, v___x_4604_);
lean_ctor_set(v___x_4606_, 6, v___x_4604_);
lean_ctor_set(v___x_4606_, 7, v___x_4604_);
lean_ctor_set(v___x_4606_, 8, v___x_4604_);
return v___x_4606_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = lean_unsigned_to_nat(32u);
v___x_4608_ = lean_mk_empty_array_with_capacity(v___x_4607_);
v___x_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
return v___x_4609_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4(void){
_start:
{
size_t v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4610_ = ((size_t)5ULL);
v___x_4611_ = lean_unsigned_to_nat(0u);
v___x_4612_ = lean_unsigned_to_nat(32u);
v___x_4613_ = lean_mk_empty_array_with_capacity(v___x_4612_);
v___x_4614_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__3);
v___x_4615_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
lean_ctor_set(v___x_4615_, 1, v___x_4613_);
lean_ctor_set(v___x_4615_, 2, v___x_4611_);
lean_ctor_set(v___x_4615_, 3, v___x_4611_);
lean_ctor_set_usize(v___x_4615_, 4, v___x_4610_);
return v___x_4615_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
lean_ctor_set(v___x_4617_, 1, v___x_4616_);
lean_ctor_set(v___x_4617_, 2, v___x_4616_);
lean_ctor_set(v___x_4617_, 3, v___x_4616_);
lean_ctor_set(v___x_4617_, 4, v___x_4616_);
return v___x_4617_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6(void){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4618_ = lean_box(1);
v___x_4619_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4620_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
lean_ctor_set(v___x_4621_, 1, v___x_4619_);
lean_ctor_set(v___x_4621_, 2, v___x_4618_);
return v___x_4621_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8(void){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4624_ = lean_unsigned_to_nat(1u);
v___x_4625_ = l_Lean_firstFrontendMacroScope;
v___x_4626_ = lean_nat_add(v___x_4625_, v___x_4624_);
return v___x_4626_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10(void){
_start:
{
lean_object* v___x_4631_; uint64_t v___x_4632_; lean_object* v___x_4633_; 
v___x_4631_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4632_ = 0ULL;
v___x_4633_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4633_, 0, v___x_4631_);
lean_ctor_set_uint64(v___x_4633_, sizeof(void*)*1, v___x_4632_);
return v___x_4633_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11(void){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4634_ = l_Lean_NameSet_empty;
v___x_4635_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
lean_ctor_set(v___x_4636_, 1, v___x_4635_);
lean_ctor_set(v___x_4636_, 2, v___x_4634_);
return v___x_4636_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12(void){
_start:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; lean_object* v___x_4640_; 
v___x_4637_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4638_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4639_ = 1;
v___x_4640_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4640_, 0, v___x_4638_);
lean_ctor_set(v___x_4640_, 1, v___x_4638_);
lean_ctor_set(v___x_4640_, 2, v___x_4637_);
lean_ctor_set_uint8(v___x_4640_, sizeof(void*)*3, v___x_4639_);
return v___x_4640_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_4642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(lean_object* v_cctx_4643_, lean_object* v_env_4644_, lean_object* v_modName_4645_, lean_object* v_d_4646_, lean_object* v_cacheRef_4647_, lean_object* v_tree_4648_, lean_object* v_act_4649_, lean_object* v_name_4650_, lean_object* v_constInfo_4651_){
_start:
{
uint8_t v___x_4653_; 
v___x_4653_ = l_Lean_ConstantInfo_isUnsafe(v_constInfo_4651_);
if (v___x_4653_ == 0)
{
uint8_t v___x_4654_; 
lean_inc(v_name_4650_);
lean_inc_ref(v_env_4644_);
v___x_4654_ = l_Lean_Meta_LazyDiscrTree_blacklistInsertion(v_env_4644_, v_name_4650_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; lean_object* v_ngen_4656_; lean_object* v_core_4657_; lean_object* v_meta_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4792_; 
v___x_4655_ = lean_st_ref_get(v_cacheRef_4647_);
v_ngen_4656_ = lean_ctor_get(v___x_4655_, 0);
v_core_4657_ = lean_ctor_get(v___x_4655_, 1);
v_meta_4658_ = lean_ctor_get(v___x_4655_, 2);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4660_ = v___x_4655_;
v_isShared_4661_ = v_isSharedCheck_4792_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_meta_4658_);
lean_inc(v_core_4657_);
lean_inc(v_ngen_4656_);
lean_dec(v___x_4655_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4792_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; uint8_t v___x_4672_; uint8_t v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v_fileName_4690_; lean_object* v_fileMap_4691_; lean_object* v_options_4692_; lean_object* v_currRecDepth_4693_; lean_object* v_maxRecDepth_4694_; lean_object* v_ref_4695_; lean_object* v_currNamespace_4696_; lean_object* v_openDecls_4697_; lean_object* v_initHeartbeats_4698_; lean_object* v_maxHeartbeats_4699_; lean_object* v_quotContext_4700_; lean_object* v_currMacroScope_4701_; uint8_t v_diag_4702_; lean_object* v_cancelTk_x3f_4703_; uint8_t v_suppressElabErrors_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4790_; 
v___x_4662_ = lean_unsigned_to_nat(0u);
v___x_4663_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_4664_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__4);
v___x_4665_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__5);
lean_inc_ref(v_ngen_4656_);
v___x_4666_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_4656_);
v___x_4667_ = lean_st_ref_set(v_cacheRef_4647_, v___x_4666_);
v___x_4668_ = lean_box(1);
v___x_4669_ = 1;
v___x_4670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4663_);
lean_ctor_set(v___x_4670_, 1, v_meta_4658_);
lean_ctor_set(v___x_4670_, 2, v___x_4668_);
lean_ctor_set(v___x_4670_, 3, v___x_4664_);
lean_ctor_set(v___x_4670_, 4, v___x_4665_);
v___x_4671_ = 2;
v___x_4672_ = 0;
v___x_4673_ = 2;
v___x_4674_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_4674_, 0, v___x_4654_);
lean_ctor_set_uint8(v___x_4674_, 1, v___x_4654_);
lean_ctor_set_uint8(v___x_4674_, 2, v___x_4654_);
lean_ctor_set_uint8(v___x_4674_, 3, v___x_4654_);
lean_ctor_set_uint8(v___x_4674_, 4, v___x_4654_);
lean_ctor_set_uint8(v___x_4674_, 5, v___x_4669_);
lean_ctor_set_uint8(v___x_4674_, 6, v___x_4669_);
lean_ctor_set_uint8(v___x_4674_, 7, v___x_4654_);
lean_ctor_set_uint8(v___x_4674_, 8, v___x_4669_);
lean_ctor_set_uint8(v___x_4674_, 9, v___x_4671_);
lean_ctor_set_uint8(v___x_4674_, 10, v___x_4672_);
lean_ctor_set_uint8(v___x_4674_, 11, v___x_4669_);
lean_ctor_set_uint8(v___x_4674_, 12, v___x_4669_);
lean_ctor_set_uint8(v___x_4674_, 13, v___x_4669_);
lean_ctor_set_uint8(v___x_4674_, 14, v___x_4673_);
lean_ctor_set_uint8(v___x_4674_, 15, v___x_4669_);
lean_ctor_set_uint8(v___x_4674_, 16, v___x_4669_);
lean_ctor_set_uint8(v___x_4674_, 17, v___x_4669_);
lean_ctor_set_uint8(v___x_4674_, 18, v___x_4669_);
v___x_4675_ = l_Lean_Meta_Config_toConfigWithKey(v___x_4674_);
v___x_4676_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__6);
v___x_4677_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__7));
v___x_4678_ = lean_box(0);
v___x_4679_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4679_, 0, v___x_4675_);
lean_ctor_set(v___x_4679_, 1, v___x_4668_);
lean_ctor_set(v___x_4679_, 2, v___x_4676_);
lean_ctor_set(v___x_4679_, 3, v___x_4677_);
lean_ctor_set(v___x_4679_, 4, v___x_4678_);
lean_ctor_set(v___x_4679_, 5, v___x_4662_);
lean_ctor_set(v___x_4679_, 6, v___x_4678_);
lean_ctor_set_uint8(v___x_4679_, sizeof(void*)*7, v___x_4654_);
lean_ctor_set_uint8(v___x_4679_, sizeof(void*)*7 + 1, v___x_4654_);
lean_ctor_set_uint8(v___x_4679_, sizeof(void*)*7 + 2, v___x_4654_);
lean_ctor_set_uint8(v___x_4679_, sizeof(void*)*7 + 3, v___x_4669_);
v___x_4680_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__8);
v___x_4681_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__9));
v___x_4682_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__10);
v___x_4683_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__11);
v___x_4684_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__12);
v___x_4685_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4685_, 0, v_env_4644_);
lean_ctor_set(v___x_4685_, 1, v___x_4680_);
lean_ctor_set(v___x_4685_, 2, v_ngen_4656_);
lean_ctor_set(v___x_4685_, 3, v___x_4681_);
lean_ctor_set(v___x_4685_, 4, v___x_4682_);
lean_ctor_set(v___x_4685_, 5, v_core_4657_);
lean_ctor_set(v___x_4685_, 6, v___x_4683_);
lean_ctor_set(v___x_4685_, 7, v___x_4684_);
lean_ctor_set(v___x_4685_, 8, v___x_4677_);
v___x_4686_ = lean_st_mk_ref(v___x_4685_);
v___x_4687_ = l_Lean_inheritedTraceOptions;
v___x_4688_ = lean_st_ref_get(v___x_4687_);
v___x_4689_ = lean_st_ref_get(v___x_4686_);
v_fileName_4690_ = lean_ctor_get(v_cctx_4643_, 0);
v_fileMap_4691_ = lean_ctor_get(v_cctx_4643_, 1);
v_options_4692_ = lean_ctor_get(v_cctx_4643_, 2);
v_currRecDepth_4693_ = lean_ctor_get(v_cctx_4643_, 3);
v_maxRecDepth_4694_ = lean_ctor_get(v_cctx_4643_, 4);
v_ref_4695_ = lean_ctor_get(v_cctx_4643_, 5);
v_currNamespace_4696_ = lean_ctor_get(v_cctx_4643_, 6);
v_openDecls_4697_ = lean_ctor_get(v_cctx_4643_, 7);
v_initHeartbeats_4698_ = lean_ctor_get(v_cctx_4643_, 8);
v_maxHeartbeats_4699_ = lean_ctor_get(v_cctx_4643_, 9);
v_quotContext_4700_ = lean_ctor_get(v_cctx_4643_, 10);
v_currMacroScope_4701_ = lean_ctor_get(v_cctx_4643_, 11);
v_diag_4702_ = lean_ctor_get_uint8(v_cctx_4643_, sizeof(void*)*14);
v_cancelTk_x3f_4703_ = lean_ctor_get(v_cctx_4643_, 12);
v_suppressElabErrors_4704_ = lean_ctor_get_uint8(v_cctx_4643_, sizeof(void*)*14 + 1);
v_isSharedCheck_4790_ = !lean_is_exclusive(v_cctx_4643_);
if (v_isSharedCheck_4790_ == 0)
{
lean_object* v_unused_4791_; 
v_unused_4791_ = lean_ctor_get(v_cctx_4643_, 13);
lean_dec(v_unused_4791_);
v___x_4706_ = v_cctx_4643_;
v_isShared_4707_ = v_isSharedCheck_4790_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_cancelTk_x3f_4703_);
lean_inc(v_currMacroScope_4701_);
lean_inc(v_quotContext_4700_);
lean_inc(v_maxHeartbeats_4699_);
lean_inc(v_initHeartbeats_4698_);
lean_inc(v_openDecls_4697_);
lean_inc(v_currNamespace_4696_);
lean_inc(v_ref_4695_);
lean_inc(v_maxRecDepth_4694_);
lean_inc(v_currRecDepth_4693_);
lean_inc(v_options_4692_);
lean_inc(v_fileMap_4691_);
lean_inc(v_fileName_4690_);
lean_dec(v_cctx_4643_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4790_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v_env_4708_; lean_object* v___x_4710_; 
v_env_4708_ = lean_ctor_get(v___x_4689_, 0);
lean_inc_ref(v_env_4708_);
lean_dec(v___x_4689_);
lean_inc_ref(v_options_4692_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 13, v___x_4688_);
v___x_4710_ = v___x_4706_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_fileName_4690_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_fileMap_4691_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_options_4692_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v_currRecDepth_4693_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v_maxRecDepth_4694_);
lean_ctor_set(v_reuseFailAlloc_4789_, 5, v_ref_4695_);
lean_ctor_set(v_reuseFailAlloc_4789_, 6, v_currNamespace_4696_);
lean_ctor_set(v_reuseFailAlloc_4789_, 7, v_openDecls_4697_);
lean_ctor_set(v_reuseFailAlloc_4789_, 8, v_initHeartbeats_4698_);
lean_ctor_set(v_reuseFailAlloc_4789_, 9, v_maxHeartbeats_4699_);
lean_ctor_set(v_reuseFailAlloc_4789_, 10, v_quotContext_4700_);
lean_ctor_set(v_reuseFailAlloc_4789_, 11, v_currMacroScope_4701_);
lean_ctor_set(v_reuseFailAlloc_4789_, 12, v_cancelTk_x3f_4703_);
lean_ctor_set(v_reuseFailAlloc_4789_, 13, v___x_4688_);
lean_ctor_set_uint8(v_reuseFailAlloc_4789_, sizeof(void*)*14, v_diag_4702_);
lean_ctor_set_uint8(v_reuseFailAlloc_4789_, sizeof(void*)*14 + 1, v_suppressElabErrors_4704_);
v___x_4710_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4711_; uint8_t v___x_4712_; lean_object* v___y_4714_; lean_object* v___y_4715_; uint8_t v___y_4767_; uint8_t v___x_4788_; 
v___x_4711_ = l_Lean_diagnostics;
v___x_4712_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_4692_, v___x_4711_);
v___x_4788_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4708_);
lean_dec_ref(v_env_4708_);
if (v___x_4788_ == 0)
{
if (v___x_4712_ == 0)
{
lean_inc(v___x_4686_);
v___y_4714_ = v___x_4710_;
v___y_4715_ = v___x_4686_;
goto v___jp_4713_;
}
else
{
v___y_4767_ = v___x_4788_;
goto v___jp_4766_;
}
}
else
{
v___y_4767_ = v___x_4712_;
goto v___jp_4766_;
}
v___jp_4713_:
{
lean_object* v___x_4716_; lean_object* v_fileName_4717_; lean_object* v_fileMap_4718_; lean_object* v_currRecDepth_4719_; lean_object* v_ref_4720_; lean_object* v_currNamespace_4721_; lean_object* v_openDecls_4722_; lean_object* v_initHeartbeats_4723_; lean_object* v_maxHeartbeats_4724_; lean_object* v_quotContext_4725_; lean_object* v_currMacroScope_4726_; lean_object* v_cancelTk_x3f_4727_; uint8_t v_suppressElabErrors_4728_; lean_object* v_inheritedTraceOptions_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4763_; 
v___x_4716_ = lean_st_mk_ref(v___x_4670_);
v_fileName_4717_ = lean_ctor_get(v___y_4714_, 0);
v_fileMap_4718_ = lean_ctor_get(v___y_4714_, 1);
v_currRecDepth_4719_ = lean_ctor_get(v___y_4714_, 3);
v_ref_4720_ = lean_ctor_get(v___y_4714_, 5);
v_currNamespace_4721_ = lean_ctor_get(v___y_4714_, 6);
v_openDecls_4722_ = lean_ctor_get(v___y_4714_, 7);
v_initHeartbeats_4723_ = lean_ctor_get(v___y_4714_, 8);
v_maxHeartbeats_4724_ = lean_ctor_get(v___y_4714_, 9);
v_quotContext_4725_ = lean_ctor_get(v___y_4714_, 10);
v_currMacroScope_4726_ = lean_ctor_get(v___y_4714_, 11);
v_cancelTk_x3f_4727_ = lean_ctor_get(v___y_4714_, 12);
v_suppressElabErrors_4728_ = lean_ctor_get_uint8(v___y_4714_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4729_ = lean_ctor_get(v___y_4714_, 13);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___y_4714_);
if (v_isSharedCheck_4763_ == 0)
{
lean_object* v_unused_4764_; lean_object* v_unused_4765_; 
v_unused_4764_ = lean_ctor_get(v___y_4714_, 4);
lean_dec(v_unused_4764_);
v_unused_4765_ = lean_ctor_get(v___y_4714_, 2);
lean_dec(v_unused_4765_);
v___x_4731_ = v___y_4714_;
v_isShared_4732_ = v_isSharedCheck_4763_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_inheritedTraceOptions_4729_);
lean_inc(v_cancelTk_x3f_4727_);
lean_inc(v_currMacroScope_4726_);
lean_inc(v_quotContext_4725_);
lean_inc(v_maxHeartbeats_4724_);
lean_inc(v_initHeartbeats_4723_);
lean_inc(v_openDecls_4722_);
lean_inc(v_currNamespace_4721_);
lean_inc(v_ref_4720_);
lean_inc(v_currRecDepth_4719_);
lean_inc(v_fileMap_4718_);
lean_inc(v_fileName_4717_);
lean_dec(v___y_4714_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4763_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4736_; 
v___x_4733_ = l_Lean_maxRecDepth;
v___x_4734_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__1(v_options_4692_, v___x_4733_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 4, v___x_4734_);
lean_ctor_set(v___x_4731_, 2, v_options_4692_);
v___x_4736_ = v___x_4731_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_fileName_4717_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v_fileMap_4718_);
lean_ctor_set(v_reuseFailAlloc_4762_, 2, v_options_4692_);
lean_ctor_set(v_reuseFailAlloc_4762_, 3, v_currRecDepth_4719_);
lean_ctor_set(v_reuseFailAlloc_4762_, 4, v___x_4734_);
lean_ctor_set(v_reuseFailAlloc_4762_, 5, v_ref_4720_);
lean_ctor_set(v_reuseFailAlloc_4762_, 6, v_currNamespace_4721_);
lean_ctor_set(v_reuseFailAlloc_4762_, 7, v_openDecls_4722_);
lean_ctor_set(v_reuseFailAlloc_4762_, 8, v_initHeartbeats_4723_);
lean_ctor_set(v_reuseFailAlloc_4762_, 9, v_maxHeartbeats_4724_);
lean_ctor_set(v_reuseFailAlloc_4762_, 10, v_quotContext_4725_);
lean_ctor_set(v_reuseFailAlloc_4762_, 11, v_currMacroScope_4726_);
lean_ctor_set(v_reuseFailAlloc_4762_, 12, v_cancelTk_x3f_4727_);
lean_ctor_set(v_reuseFailAlloc_4762_, 13, v_inheritedTraceOptions_4729_);
lean_ctor_set_uint8(v_reuseFailAlloc_4762_, sizeof(void*)*14 + 1, v_suppressElabErrors_4728_);
v___x_4736_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; 
lean_ctor_set_uint8(v___x_4736_, sizeof(void*)*14, v___x_4712_);
lean_inc(v___x_4716_);
lean_inc(v_name_4650_);
v___x_4737_ = lean_apply_7(v_act_4649_, v_name_4650_, v_constInfo_4651_, v___x_4679_, v___x_4716_, v___x_4736_, v___y_4715_, lean_box(0));
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v_ngen_4741_; lean_object* v_cache_4742_; lean_object* v_cache_4743_; lean_object* v___x_4745_; 
lean_dec(v_name_4650_);
lean_dec(v_modName_4645_);
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref(v___x_4737_);
v___x_4739_ = lean_st_ref_get(v___x_4716_);
lean_dec(v___x_4716_);
v___x_4740_ = lean_st_ref_get(v___x_4686_);
lean_dec(v___x_4686_);
v_ngen_4741_ = lean_ctor_get(v___x_4740_, 2);
lean_inc_ref(v_ngen_4741_);
v_cache_4742_ = lean_ctor_get(v___x_4740_, 5);
lean_inc_ref(v_cache_4742_);
lean_dec(v___x_4740_);
v_cache_4743_ = lean_ctor_get(v___x_4739_, 1);
lean_inc_ref(v_cache_4743_);
lean_dec(v___x_4739_);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 2, v_cache_4743_);
lean_ctor_set(v___x_4660_, 1, v_cache_4742_);
lean_ctor_set(v___x_4660_, 0, v_ngen_4741_);
v___x_4745_ = v___x_4660_;
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
v___x_4746_ = lean_st_ref_set(v_cacheRef_4647_, v___x_4745_);
v___x_4747_ = lean_array_get_size(v_a_4738_);
v___x_4748_ = lean_nat_dec_lt(v___x_4662_, v___x_4747_);
if (v___x_4748_ == 0)
{
lean_dec(v_a_4738_);
return v_tree_4648_;
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
return v_tree_4648_;
}
else
{
size_t v___x_4750_; size_t v___x_4751_; lean_object* v___x_4752_; 
v___x_4750_ = ((size_t)0ULL);
v___x_4751_ = lean_usize_of_nat(v___x_4747_);
v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4738_, v___x_4750_, v___x_4751_, v_tree_4648_);
lean_dec(v_a_4738_);
return v___x_4752_;
}
}
else
{
size_t v___x_4753_; size_t v___x_4754_; lean_object* v___x_4755_; 
v___x_4753_ = ((size_t)0ULL);
v___x_4754_ = lean_usize_of_nat(v___x_4747_);
v___x_4755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_a_4738_, v___x_4753_, v___x_4754_, v_tree_4648_);
lean_dec(v_a_4738_);
return v___x_4755_;
}
}
}
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
lean_dec(v___x_4716_);
lean_dec(v___x_4686_);
lean_del_object(v___x_4660_);
v_a_4757_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4757_);
lean_dec_ref(v___x_4737_);
v___x_4758_ = lean_st_ref_take(v_d_4646_);
v___x_4759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4759_, 0, v_modName_4645_);
lean_ctor_set(v___x_4759_, 1, v_name_4650_);
lean_ctor_set(v___x_4759_, 2, v_a_4757_);
v___x_4760_ = lean_array_push(v___x_4758_, v___x_4759_);
v___x_4761_ = lean_st_ref_set(v_d_4646_, v___x_4760_);
return v_tree_4648_;
}
}
}
}
v___jp_4766_:
{
if (v___y_4767_ == 0)
{
lean_object* v___x_4768_; lean_object* v_env_4769_; lean_object* v_nextMacroScope_4770_; lean_object* v_ngen_4771_; lean_object* v_auxDeclNGen_4772_; lean_object* v_traceState_4773_; lean_object* v_messages_4774_; lean_object* v_infoState_4775_; lean_object* v_snapshotTasks_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4786_; 
v___x_4768_ = lean_st_ref_take(v___x_4686_);
v_env_4769_ = lean_ctor_get(v___x_4768_, 0);
v_nextMacroScope_4770_ = lean_ctor_get(v___x_4768_, 1);
v_ngen_4771_ = lean_ctor_get(v___x_4768_, 2);
v_auxDeclNGen_4772_ = lean_ctor_get(v___x_4768_, 3);
v_traceState_4773_ = lean_ctor_get(v___x_4768_, 4);
v_messages_4774_ = lean_ctor_get(v___x_4768_, 6);
v_infoState_4775_ = lean_ctor_get(v___x_4768_, 7);
v_snapshotTasks_4776_ = lean_ctor_get(v___x_4768_, 8);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4786_ == 0)
{
lean_object* v_unused_4787_; 
v_unused_4787_ = lean_ctor_get(v___x_4768_, 5);
lean_dec(v_unused_4787_);
v___x_4778_ = v___x_4768_;
v_isShared_4779_ = v_isSharedCheck_4786_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_snapshotTasks_4776_);
lean_inc(v_infoState_4775_);
lean_inc(v_messages_4774_);
lean_inc(v_traceState_4773_);
lean_inc(v_auxDeclNGen_4772_);
lean_inc(v_ngen_4771_);
lean_inc(v_nextMacroScope_4770_);
lean_inc(v_env_4769_);
lean_dec(v___x_4768_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4786_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4783_; 
v___x_4780_ = l_Lean_Kernel_enableDiag(v_env_4769_, v___x_4712_);
v___x_4781_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__13);
if (v_isShared_4779_ == 0)
{
lean_ctor_set(v___x_4778_, 5, v___x_4781_);
lean_ctor_set(v___x_4778_, 0, v___x_4780_);
v___x_4783_ = v___x_4778_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4780_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_nextMacroScope_4770_);
lean_ctor_set(v_reuseFailAlloc_4785_, 2, v_ngen_4771_);
lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_auxDeclNGen_4772_);
lean_ctor_set(v_reuseFailAlloc_4785_, 4, v_traceState_4773_);
lean_ctor_set(v_reuseFailAlloc_4785_, 5, v___x_4781_);
lean_ctor_set(v_reuseFailAlloc_4785_, 6, v_messages_4774_);
lean_ctor_set(v_reuseFailAlloc_4785_, 7, v_infoState_4775_);
lean_ctor_set(v_reuseFailAlloc_4785_, 8, v_snapshotTasks_4776_);
v___x_4783_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
lean_object* v___x_4784_; 
v___x_4784_ = lean_st_ref_set(v___x_4686_, v___x_4783_);
lean_inc(v___x_4686_);
v___y_4714_ = v___x_4710_;
v___y_4715_ = v___x_4686_;
goto v___jp_4713_;
}
}
}
else
{
lean_inc(v___x_4686_);
v___y_4714_ = v___x_4710_;
v___y_4715_ = v___x_4686_;
goto v___jp_4713_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_constInfo_4651_);
lean_dec(v_name_4650_);
lean_dec_ref(v_act_4649_);
lean_dec(v_modName_4645_);
lean_dec_ref(v_env_4644_);
lean_dec_ref(v_cctx_4643_);
return v_tree_4648_;
}
}
else
{
lean_dec_ref(v_constInfo_4651_);
lean_dec(v_name_4650_);
lean_dec_ref(v_act_4649_);
lean_dec(v_modName_4645_);
lean_dec_ref(v_env_4644_);
lean_dec_ref(v_cctx_4643_);
return v_tree_4648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___boxed(lean_object* v_cctx_4793_, lean_object* v_env_4794_, lean_object* v_modName_4795_, lean_object* v_d_4796_, lean_object* v_cacheRef_4797_, lean_object* v_tree_4798_, lean_object* v_act_4799_, lean_object* v_name_4800_, lean_object* v_constInfo_4801_, lean_object* v_a_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4793_, v_env_4794_, v_modName_4795_, v_d_4796_, v_cacheRef_4797_, v_tree_4798_, v_act_4799_, v_name_4800_, v_constInfo_4801_);
lean_dec(v_cacheRef_4797_);
lean_dec(v_d_4796_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData(lean_object* v_00_u03b1_4804_, lean_object* v_cctx_4805_, lean_object* v_env_4806_, lean_object* v_modName_4807_, lean_object* v_d_4808_, lean_object* v_cacheRef_4809_, lean_object* v_tree_4810_, lean_object* v_act_4811_, lean_object* v_name_4812_, lean_object* v_constInfo_4813_){
_start:
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4805_, v_env_4806_, v_modName_4807_, v_d_4808_, v_cacheRef_4809_, v_tree_4810_, v_act_4811_, v_name_4812_, v_constInfo_4813_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_addConstImportData___boxed(lean_object* v_00_u03b1_4816_, lean_object* v_cctx_4817_, lean_object* v_env_4818_, lean_object* v_modName_4819_, lean_object* v_d_4820_, lean_object* v_cacheRef_4821_, lean_object* v_tree_4822_, lean_object* v_act_4823_, lean_object* v_name_4824_, lean_object* v_constInfo_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v_res_4827_; 
v_res_4827_ = l_Lean_Meta_LazyDiscrTree_addConstImportData(v_00_u03b1_4816_, v_cctx_4817_, v_env_4818_, v_modName_4819_, v_d_4820_, v_cacheRef_4821_, v_tree_4822_, v_act_4823_, v_name_4824_, v_constInfo_4825_);
lean_dec(v_cacheRef_4821_);
lean_dec(v_d_4820_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(lean_object* v_00_u03b1_4828_, lean_object* v_as_4829_, size_t v_i_4830_, size_t v_stop_4831_, lean_object* v_b_4832_){
_start:
{
lean_object* v___x_4833_; 
v___x_4833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___redArg(v_as_4829_, v_i_4830_, v_stop_4831_, v_b_4832_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2___boxed(lean_object* v_00_u03b1_4834_, lean_object* v_as_4835_, lean_object* v_i_4836_, lean_object* v_stop_4837_, lean_object* v_b_4838_){
_start:
{
size_t v_i_boxed_4839_; size_t v_stop_boxed_4840_; lean_object* v_res_4841_; 
v_i_boxed_4839_ = lean_unbox_usize(v_i_4836_);
lean_dec(v_i_4836_);
v_stop_boxed_4840_ = lean_unbox_usize(v_stop_4837_);
lean_dec(v_stop_4837_);
v_res_4841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__2(v_00_u03b1_4834_, v_as_4835_, v_i_boxed_4839_, v_stop_boxed_4840_, v_b_4838_);
lean_dec_ref(v_as_4835_);
return v_res_4841_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4844_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0));
v___x_4845_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_4846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
lean_ctor_set(v___x_4846_, 1, v___x_4844_);
return v___x_4846_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2(void){
_start:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4847_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__0));
v___x_4848_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1);
v___x_4849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
lean_ctor_set(v___x_4849_, 1, v___x_4847_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults(lean_object* v_00_u03b1_4850_){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__2);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(lean_object* v_x_4852_, lean_object* v_y_4853_){
_start:
{
lean_object* v_tree_4854_; lean_object* v_errors_4855_; lean_object* v_tree_4856_; lean_object* v_errors_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4866_; 
v_tree_4854_ = lean_ctor_get(v_x_4852_, 0);
lean_inc_ref(v_tree_4854_);
v_errors_4855_ = lean_ctor_get(v_x_4852_, 1);
lean_inc_ref(v_errors_4855_);
lean_dec_ref(v_x_4852_);
v_tree_4856_ = lean_ctor_get(v_y_4853_, 0);
v_errors_4857_ = lean_ctor_get(v_y_4853_, 1);
v_isSharedCheck_4866_ = !lean_is_exclusive(v_y_4853_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4859_ = v_y_4853_;
v_isShared_4860_ = v_isSharedCheck_4866_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_errors_4857_);
lean_inc(v_tree_4856_);
lean_dec(v_y_4853_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4866_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4864_; 
v___x_4861_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_append___redArg(v_tree_4854_, v_tree_4856_);
v___x_4862_ = l_Array_append___redArg(v_errors_4855_, v_errors_4857_);
lean_dec_ref(v_errors_4857_);
if (v_isShared_4860_ == 0)
{
lean_ctor_set(v___x_4859_, 1, v___x_4862_);
lean_ctor_set(v___x_4859_, 0, v___x_4861_);
v___x_4864_ = v___x_4859_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v___x_4861_);
lean_ctor_set(v_reuseFailAlloc_4865_, 1, v___x_4862_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_append(lean_object* v_00_u03b1_4867_, lean_object* v_x_4868_, lean_object* v_y_4869_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_x_4868_, v_y_4869_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_InitResults_instAppend(lean_object* v_00_u03b1_4872_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
return v___x_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg(lean_object* v_d_4874_, lean_object* v_tree_4875_){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4877_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_ImportData_new___closed__0));
v___x_4878_ = lean_st_ref_swap(v_d_4874_, v___x_4877_);
v___x_4879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4879_, 0, v_tree_4875_);
lean_ctor_set(v___x_4879_, 1, v___x_4878_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___redArg___boxed(lean_object* v_d_4880_, lean_object* v_tree_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4880_, v_tree_4881_);
lean_dec(v_d_4880_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat(lean_object* v_00_u03b1_4884_, lean_object* v_d_4885_, lean_object* v_tree_4886_){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4885_, v_tree_4886_);
return v___x_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_toFlat___boxed(lean_object* v_00_u03b1_4889_, lean_object* v_d_4890_, lean_object* v_tree_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_Lean_Meta_LazyDiscrTree_toFlat(v_00_u03b1_4889_, v_d_4890_, v_tree_4891_);
lean_dec(v_d_4890_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(lean_object* v_cctx_4894_, lean_object* v_env_4895_, lean_object* v_act_4896_, lean_object* v_d_4897_, lean_object* v_cacheRef_4898_, lean_object* v_tree_4899_, lean_object* v_mname_4900_, lean_object* v_mdata_4901_, lean_object* v_i_4902_){
_start:
{
lean_object* v_constants_4904_; lean_object* v___x_4905_; uint8_t v___x_4906_; 
v_constants_4904_ = lean_ctor_get(v_mdata_4901_, 2);
v___x_4905_ = lean_array_get_size(v_constants_4904_);
v___x_4906_ = lean_nat_dec_lt(v_i_4902_, v___x_4905_);
if (v___x_4906_ == 0)
{
lean_dec(v_i_4902_);
lean_dec(v_mname_4900_);
lean_dec_ref(v_act_4896_);
lean_dec_ref(v_env_4895_);
lean_dec_ref(v_cctx_4894_);
return v_tree_4899_;
}
else
{
lean_object* v_constInfo_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
v_constInfo_4907_ = lean_array_fget_borrowed(v_constants_4904_, v_i_4902_);
v___x_4908_ = l_Lean_ConstantInfo_name(v_constInfo_4907_);
lean_inc(v_constInfo_4907_);
lean_inc_ref(v_act_4896_);
lean_inc(v_mname_4900_);
lean_inc_ref(v_env_4895_);
lean_inc_ref(v_cctx_4894_);
v___x_4909_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_4894_, v_env_4895_, v_mname_4900_, v_d_4897_, v_cacheRef_4898_, v_tree_4899_, v_act_4896_, v___x_4908_, v_constInfo_4907_);
v___x_4910_ = lean_unsigned_to_nat(1u);
v___x_4911_ = lean_nat_add(v_i_4902_, v___x_4910_);
lean_dec(v_i_4902_);
v_tree_4899_ = v___x_4909_;
v_i_4902_ = v___x_4911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg___boxed(lean_object* v_cctx_4913_, lean_object* v_env_4914_, lean_object* v_act_4915_, lean_object* v_d_4916_, lean_object* v_cacheRef_4917_, lean_object* v_tree_4918_, lean_object* v_mname_4919_, lean_object* v_mdata_4920_, lean_object* v_i_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4913_, v_env_4914_, v_act_4915_, v_d_4916_, v_cacheRef_4917_, v_tree_4918_, v_mname_4919_, v_mdata_4920_, v_i_4921_);
lean_dec_ref(v_mdata_4920_);
lean_dec(v_cacheRef_4917_);
lean_dec(v_d_4916_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule(lean_object* v_00_u03b1_4924_, lean_object* v_cctx_4925_, lean_object* v_env_4926_, lean_object* v_act_4927_, lean_object* v_d_4928_, lean_object* v_cacheRef_4929_, lean_object* v_tree_4930_, lean_object* v_mname_4931_, lean_object* v_mdata_4932_, lean_object* v_i_4933_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4925_, v_env_4926_, v_act_4927_, v_d_4928_, v_cacheRef_4929_, v_tree_4930_, v_mname_4931_, v_mdata_4932_, v_i_4933_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_loadImportedModule___boxed(lean_object* v_00_u03b1_4936_, lean_object* v_cctx_4937_, lean_object* v_env_4938_, lean_object* v_act_4939_, lean_object* v_d_4940_, lean_object* v_cacheRef_4941_, lean_object* v_tree_4942_, lean_object* v_mname_4943_, lean_object* v_mdata_4944_, lean_object* v_i_4945_, lean_object* v_a_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule(v_00_u03b1_4936_, v_cctx_4937_, v_env_4938_, v_act_4939_, v_d_4940_, v_cacheRef_4941_, v_tree_4942_, v_mname_4943_, v_mdata_4944_, v_i_4945_);
lean_dec_ref(v_mdata_4944_);
lean_dec(v_cacheRef_4941_);
lean_dec(v_d_4940_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(lean_object* v_cctx_4948_, lean_object* v_env_4949_, lean_object* v_act_4950_, lean_object* v_d_4951_, lean_object* v_cacheRef_4952_, lean_object* v_tree_4953_, lean_object* v_start_4954_, lean_object* v_stop_4955_){
_start:
{
uint8_t v___x_4957_; 
v___x_4957_ = lean_nat_dec_lt(v_start_4954_, v_stop_4955_);
if (v___x_4957_ == 0)
{
lean_object* v___x_4958_; 
lean_dec(v_start_4954_);
lean_dec_ref(v_act_4950_);
lean_dec_ref(v_env_4949_);
lean_dec_ref(v_cctx_4948_);
v___x_4958_ = l_Lean_Meta_LazyDiscrTree_toFlat___redArg(v_d_4951_, v_tree_4953_);
return v___x_4958_;
}
else
{
lean_object* v___x_4959_; lean_object* v_moduleData_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v_mname_4963_; lean_object* v___x_4964_; lean_object* v_mdata_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4959_ = l_Lean_Environment_header(v_env_4949_);
v_moduleData_4960_ = lean_ctor_get(v___x_4959_, 6);
lean_inc_ref(v_moduleData_4960_);
v___x_4961_ = lean_box(0);
v___x_4962_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4959_);
v_mname_4963_ = lean_array_get(v___x_4961_, v___x_4962_, v_start_4954_);
lean_dec_ref(v___x_4962_);
v___x_4964_ = l_Lean_instInhabitedModuleData_default;
v_mdata_4965_ = lean_array_get(v___x_4964_, v_moduleData_4960_, v_start_4954_);
lean_dec_ref(v_moduleData_4960_);
v___x_4966_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_act_4950_);
lean_inc_ref(v_env_4949_);
lean_inc_ref(v_cctx_4948_);
v___x_4967_ = l_Lean_Meta_LazyDiscrTree_loadImportedModule___redArg(v_cctx_4948_, v_env_4949_, v_act_4950_, v_d_4951_, v_cacheRef_4952_, v_tree_4953_, v_mname_4963_, v_mdata_4965_, v___x_4966_);
lean_dec(v_mdata_4965_);
v___x_4968_ = lean_unsigned_to_nat(1u);
v___x_4969_ = lean_nat_add(v_start_4954_, v___x_4968_);
lean_dec(v_start_4954_);
v_tree_4953_ = v___x_4967_;
v_start_4954_ = v___x_4969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg___boxed(lean_object* v_cctx_4971_, lean_object* v_env_4972_, lean_object* v_act_4973_, lean_object* v_d_4974_, lean_object* v_cacheRef_4975_, lean_object* v_tree_4976_, lean_object* v_start_4977_, lean_object* v_stop_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4971_, v_env_4972_, v_act_4973_, v_d_4974_, v_cacheRef_4975_, v_tree_4976_, v_start_4977_, v_stop_4978_);
lean_dec(v_stop_4978_);
lean_dec(v_cacheRef_4975_);
lean_dec(v_d_4974_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(lean_object* v_00_u03b1_4981_, lean_object* v_cctx_4982_, lean_object* v_env_4983_, lean_object* v_act_4984_, lean_object* v_d_4985_, lean_object* v_cacheRef_4986_, lean_object* v_tree_4987_, lean_object* v_start_4988_, lean_object* v_stop_4989_){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_4982_, v_env_4983_, v_act_4984_, v_d_4985_, v_cacheRef_4986_, v_tree_4987_, v_start_4988_, v_stop_4989_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___boxed(lean_object* v_00_u03b1_4992_, lean_object* v_cctx_4993_, lean_object* v_env_4994_, lean_object* v_act_4995_, lean_object* v_d_4996_, lean_object* v_cacheRef_4997_, lean_object* v_tree_4998_, lean_object* v_start_4999_, lean_object* v_stop_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go(v_00_u03b1_4992_, v_cctx_4993_, v_env_4994_, v_act_4995_, v_d_4996_, v_cacheRef_4997_, v_tree_4998_, v_start_4999_, v_stop_5000_);
lean_dec(v_stop_5000_);
lean_dec(v_cacheRef_4997_);
lean_dec(v_d_4996_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(lean_object* v_cctx_5003_, lean_object* v_ngen_5004_, lean_object* v_env_5005_, lean_object* v_act_5006_, lean_object* v_start_5007_, lean_object* v_stop_5008_){
_start:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5010_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5004_);
v___x_5011_ = lean_st_mk_ref(v___x_5010_);
v___x_5012_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v___x_5013_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1);
v___x_5014_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq_go___redArg(v_cctx_5003_, v_env_5005_, v_act_5006_, v___x_5012_, v___x_5011_, v___x_5013_, v_start_5007_, v_stop_5008_);
lean_dec(v___x_5011_);
lean_dec(v___x_5012_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg___boxed(lean_object* v_cctx_5015_, lean_object* v_ngen_5016_, lean_object* v_env_5017_, lean_object* v_act_5018_, lean_object* v_start_5019_, lean_object* v_stop_5020_, lean_object* v_a_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5015_, v_ngen_5016_, v_env_5017_, v_act_5018_, v_start_5019_, v_stop_5020_);
lean_dec(v_stop_5020_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(lean_object* v_00_u03b1_5023_, lean_object* v_cctx_5024_, lean_object* v_ngen_5025_, lean_object* v_env_5026_, lean_object* v_act_5027_, lean_object* v_start_5028_, lean_object* v_stop_5029_){
_start:
{
lean_object* v___x_5031_; 
v___x_5031_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___redArg(v_cctx_5024_, v_ngen_5025_, v_env_5026_, v_act_5027_, v_start_5028_, v_stop_5029_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed(lean_object* v_00_u03b1_5032_, lean_object* v_cctx_5033_, lean_object* v_ngen_5034_, lean_object* v_env_5035_, lean_object* v_act_5036_, lean_object* v_start_5037_, lean_object* v_stop_5038_, lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq(v_00_u03b1_5032_, v_cctx_5033_, v_ngen_5034_, v_env_5035_, v_act_5036_, v_start_5037_, v_stop_5038_);
lean_dec(v_stop_5038_);
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0(lean_object* v_inst_5041_, lean_object* v_x1_5042_, lean_object* v_x2_5043_){
_start:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5044_ = lean_task_get_own(v_x2_5043_);
v___x_5045_ = lean_apply_2(v_inst_5041_, v_x1_5042_, v___x_5044_);
return v___x_5045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___redArg(lean_object* v_inst_5046_, lean_object* v_z_5047_, lean_object* v_tasks_5048_){
_start:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; uint8_t v___x_5052_; 
v___x_5049_ = lean_unsigned_to_nat(0u);
v___x_5050_ = lean_array_get_size(v_tasks_5048_);
v___x_5051_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___redArg___lam__1___closed__9));
v___x_5052_ = lean_nat_dec_lt(v___x_5049_, v___x_5050_);
if (v___x_5052_ == 0)
{
lean_dec_ref(v_tasks_5048_);
lean_dec(v_inst_5046_);
return v_z_5047_;
}
else
{
lean_object* v___f_5053_; uint8_t v___x_5054_; 
v___f_5053_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_combineGet___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5053_, 0, v_inst_5046_);
v___x_5054_ = lean_nat_dec_le(v___x_5050_, v___x_5050_);
if (v___x_5054_ == 0)
{
if (v___x_5052_ == 0)
{
lean_dec_ref(v___f_5053_);
lean_dec_ref(v_tasks_5048_);
return v_z_5047_;
}
else
{
size_t v___x_5055_; size_t v___x_5056_; lean_object* v___x_5057_; 
v___x_5055_ = ((size_t)0ULL);
v___x_5056_ = lean_usize_of_nat(v___x_5050_);
v___x_5057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5051_, v___f_5053_, v_tasks_5048_, v___x_5055_, v___x_5056_, v_z_5047_);
return v___x_5057_;
}
}
else
{
size_t v___x_5058_; size_t v___x_5059_; lean_object* v___x_5060_; 
v___x_5058_ = ((size_t)0ULL);
v___x_5059_ = lean_usize_of_nat(v___x_5050_);
v___x_5060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5051_, v___f_5053_, v_tasks_5048_, v___x_5058_, v___x_5059_, v_z_5047_);
return v___x_5060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet(lean_object* v_00_u03b1_5061_, lean_object* v_inst_5062_, lean_object* v_z_5063_, lean_object* v_tasks_5064_){
_start:
{
lean_object* v___x_5065_; 
v___x_5065_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v_inst_5062_, v_z_5063_, v_tasks_5064_);
return v___x_5065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0(lean_object* v_toPure_5066_, lean_object* v___x_5067_, lean_object* v_____r_5068_){
_start:
{
lean_object* v___x_5069_; 
v___x_5069_ = lean_apply_2(v_toPure_5066_, lean_box(0), v___x_5067_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1(lean_object* v_toPure_5070_, lean_object* v_setNGen_5071_, lean_object* v_toBind_5072_, lean_object* v_ngen_5073_){
_start:
{
lean_object* v_namePrefix_5074_; lean_object* v_idx_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5089_; 
v_namePrefix_5074_ = lean_ctor_get(v_ngen_5073_, 0);
v_idx_5075_ = lean_ctor_get(v_ngen_5073_, 1);
v_isSharedCheck_5089_ = !lean_is_exclusive(v_ngen_5073_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5077_ = v_ngen_5073_;
v_isShared_5078_ = v_isSharedCheck_5089_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_idx_5075_);
lean_inc(v_namePrefix_5074_);
lean_dec(v_ngen_5073_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5089_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5082_; 
lean_inc(v_idx_5075_);
lean_inc(v_namePrefix_5074_);
v___x_5079_ = l_Lean_Name_num___override(v_namePrefix_5074_, v_idx_5075_);
v___x_5080_ = lean_unsigned_to_nat(1u);
if (v_isShared_5078_ == 0)
{
lean_ctor_set(v___x_5077_, 1, v___x_5080_);
lean_ctor_set(v___x_5077_, 0, v___x_5079_);
v___x_5082_ = v___x_5077_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v___x_5079_);
lean_ctor_set(v_reuseFailAlloc_5088_, 1, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
lean_object* v___f_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___f_5083_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5083_, 0, v_toPure_5070_);
lean_closure_set(v___f_5083_, 1, v___x_5082_);
v___x_5084_ = lean_nat_add(v_idx_5075_, v___x_5080_);
lean_dec(v_idx_5075_);
v___x_5085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5085_, 0, v_namePrefix_5074_);
lean_ctor_set(v___x_5085_, 1, v___x_5084_);
v___x_5086_ = lean_apply_1(v_setNGen_5071_, v___x_5085_);
v___x_5087_ = lean_apply_4(v_toBind_5072_, lean_box(0), lean_box(0), v___x_5086_, v___f_5083_);
return v___x_5087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(lean_object* v_inst_5090_, lean_object* v_inst_5091_){
_start:
{
lean_object* v_toApplicative_5092_; lean_object* v_toBind_5093_; lean_object* v_getNGen_5094_; lean_object* v_setNGen_5095_; lean_object* v_toPure_5096_; lean_object* v___f_5097_; lean_object* v___x_5098_; 
v_toApplicative_5092_ = lean_ctor_get(v_inst_5090_, 0);
lean_inc_ref(v_toApplicative_5092_);
v_toBind_5093_ = lean_ctor_get(v_inst_5090_, 1);
lean_inc_n(v_toBind_5093_, 2);
lean_dec_ref(v_inst_5090_);
v_getNGen_5094_ = lean_ctor_get(v_inst_5091_, 0);
lean_inc(v_getNGen_5094_);
v_setNGen_5095_ = lean_ctor_get(v_inst_5091_, 1);
lean_inc(v_setNGen_5095_);
lean_dec_ref(v_inst_5091_);
v_toPure_5096_ = lean_ctor_get(v_toApplicative_5092_, 1);
lean_inc(v_toPure_5096_);
lean_dec_ref(v_toApplicative_5092_);
v___f_5097_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg___lam__1), 4, 3);
lean_closure_set(v___f_5097_, 0, v_toPure_5096_);
lean_closure_set(v___f_5097_, 1, v_setNGen_5095_);
lean_closure_set(v___f_5097_, 2, v_toBind_5093_);
v___x_5098_ = lean_apply_4(v_toBind_5093_, lean_box(0), lean_box(0), v_getNGen_5094_, v___f_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen(lean_object* v_M_5099_, lean_object* v_inst_5100_, lean_object* v_inst_5101_){
_start:
{
lean_object* v___x_5102_; 
v___x_5102_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___redArg(v_inst_5100_, v_inst_5101_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0(lean_object* v_cctx_5103_, lean_object* v_env_5104_, lean_object* v_mainModule_5105_, lean_object* v_d_5106_, lean_object* v_val_5107_, lean_object* v_act_5108_, lean_object* v_t_5109_, lean_object* v_n_5110_, lean_object* v_c_5111_){
_start:
{
lean_object* v___x_5113_; 
v___x_5113_ = l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg(v_cctx_5103_, v_env_5104_, v_mainModule_5105_, v_d_5106_, v_val_5107_, v_t_5109_, v_act_5108_, v_n_5110_, v_c_5111_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0___boxed(lean_object* v_cctx_5114_, lean_object* v_env_5115_, lean_object* v_mainModule_5116_, lean_object* v_d_5117_, lean_object* v_val_5118_, lean_object* v_act_5119_, lean_object* v_t_5120_, lean_object* v_n_5121_, lean_object* v_c_5122_, lean_object* v___y_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0(v_cctx_5114_, v_env_5115_, v_mainModule_5116_, v_d_5117_, v_val_5118_, v_act_5119_, v_t_5120_, v_n_5121_, v_c_5122_);
lean_dec(v_val_5118_);
lean_dec(v_d_5117_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(lean_object* v_f_5125_, lean_object* v_keys_5126_, lean_object* v_vals_5127_, lean_object* v_i_5128_, lean_object* v_acc_5129_){
_start:
{
lean_object* v___x_5131_; uint8_t v___x_5132_; 
v___x_5131_ = lean_array_get_size(v_keys_5126_);
v___x_5132_ = lean_nat_dec_lt(v_i_5128_, v___x_5131_);
if (v___x_5132_ == 0)
{
lean_dec(v_i_5128_);
lean_dec_ref(v_f_5125_);
return v_acc_5129_;
}
else
{
lean_object* v_k_5133_; lean_object* v_v_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; 
v_k_5133_ = lean_array_fget_borrowed(v_keys_5126_, v_i_5128_);
v_v_5134_ = lean_array_fget_borrowed(v_vals_5127_, v_i_5128_);
lean_inc_ref(v_f_5125_);
lean_inc(v_v_5134_);
lean_inc(v_k_5133_);
v___x_5135_ = lean_apply_4(v_f_5125_, v_acc_5129_, v_k_5133_, v_v_5134_, lean_box(0));
v___x_5136_ = lean_unsigned_to_nat(1u);
v___x_5137_ = lean_nat_add(v_i_5128_, v___x_5136_);
lean_dec(v_i_5128_);
v_i_5128_ = v___x_5137_;
v_acc_5129_ = v___x_5135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_5139_, lean_object* v_keys_5140_, lean_object* v_vals_5141_, lean_object* v_i_5142_, lean_object* v_acc_5143_, lean_object* v___y_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(v_f_5139_, v_keys_5140_, v_vals_5141_, v_i_5142_, v_acc_5143_);
lean_dec_ref(v_vals_5141_);
lean_dec_ref(v_keys_5140_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(lean_object* v_f_5146_, lean_object* v_x_5147_, lean_object* v_x_5148_){
_start:
{
if (lean_obj_tag(v_x_5147_) == 0)
{
lean_object* v_es_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; uint8_t v___x_5153_; 
v_es_5150_ = lean_ctor_get(v_x_5147_, 0);
v___x_5151_ = lean_unsigned_to_nat(0u);
v___x_5152_ = lean_array_get_size(v_es_5150_);
v___x_5153_ = lean_nat_dec_lt(v___x_5151_, v___x_5152_);
if (v___x_5153_ == 0)
{
lean_dec_ref(v_f_5146_);
return v_x_5148_;
}
else
{
uint8_t v___x_5154_; 
v___x_5154_ = lean_nat_dec_le(v___x_5152_, v___x_5152_);
if (v___x_5154_ == 0)
{
if (v___x_5153_ == 0)
{
lean_dec_ref(v_f_5146_);
return v_x_5148_;
}
else
{
size_t v___x_5155_; size_t v___x_5156_; lean_object* v___x_5157_; 
v___x_5155_ = ((size_t)0ULL);
v___x_5156_ = lean_usize_of_nat(v___x_5152_);
v___x_5157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5146_, v_es_5150_, v___x_5155_, v___x_5156_, v_x_5148_);
return v___x_5157_;
}
}
else
{
size_t v___x_5158_; size_t v___x_5159_; lean_object* v___x_5160_; 
v___x_5158_ = ((size_t)0ULL);
v___x_5159_ = lean_usize_of_nat(v___x_5152_);
v___x_5160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5146_, v_es_5150_, v___x_5158_, v___x_5159_, v_x_5148_);
return v___x_5160_;
}
}
}
else
{
lean_object* v_ks_5161_; lean_object* v_vs_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
v_ks_5161_ = lean_ctor_get(v_x_5147_, 0);
v_vs_5162_ = lean_ctor_get(v_x_5147_, 1);
v___x_5163_ = lean_unsigned_to_nat(0u);
v___x_5164_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(v_f_5146_, v_ks_5161_, v_vs_5162_, v___x_5163_, v_x_5148_);
return v___x_5164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(lean_object* v_f_5165_, lean_object* v_as_5166_, size_t v_i_5167_, size_t v_stop_5168_, lean_object* v_b_5169_){
_start:
{
lean_object* v_val_5172_; lean_object* v___y_5177_; uint8_t v___x_5178_; 
v___x_5178_ = lean_usize_dec_eq(v_i_5167_, v_stop_5168_);
if (v___x_5178_ == 0)
{
lean_object* v___x_5179_; 
v___x_5179_ = lean_array_uget_borrowed(v_as_5166_, v_i_5167_);
switch(lean_obj_tag(v___x_5179_))
{
case 0:
{
lean_object* v_key_5180_; lean_object* v_val_5181_; lean_object* v___x_5182_; 
v_key_5180_ = lean_ctor_get(v___x_5179_, 0);
v_val_5181_ = lean_ctor_get(v___x_5179_, 1);
lean_inc_ref(v_f_5165_);
lean_inc(v_val_5181_);
lean_inc(v_key_5180_);
v___x_5182_ = lean_apply_4(v_f_5165_, v_b_5169_, v_key_5180_, v_val_5181_, lean_box(0));
v___y_5177_ = v___x_5182_;
goto v___jp_5176_;
}
case 1:
{
lean_object* v_node_5183_; lean_object* v___x_5184_; 
v_node_5183_ = lean_ctor_get(v___x_5179_, 0);
lean_inc_ref(v_f_5165_);
v___x_5184_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5165_, v_node_5183_, v_b_5169_);
v___y_5177_ = v___x_5184_;
goto v___jp_5176_;
}
default: 
{
v_val_5172_ = v_b_5169_;
goto v___jp_5171_;
}
}
}
else
{
lean_dec_ref(v_f_5165_);
return v_b_5169_;
}
v___jp_5171_:
{
size_t v___x_5173_; size_t v___x_5174_; 
v___x_5173_ = ((size_t)1ULL);
v___x_5174_ = lean_usize_add(v_i_5167_, v___x_5173_);
v_i_5167_ = v___x_5174_;
v_b_5169_ = v_val_5172_;
goto _start;
}
v___jp_5176_:
{
v_val_5172_ = v___y_5177_;
goto v___jp_5171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_5185_, lean_object* v_as_5186_, lean_object* v_i_5187_, lean_object* v_stop_5188_, lean_object* v_b_5189_, lean_object* v___y_5190_){
_start:
{
size_t v_i_boxed_5191_; size_t v_stop_boxed_5192_; lean_object* v_res_5193_; 
v_i_boxed_5191_ = lean_unbox_usize(v_i_5187_);
lean_dec(v_i_5187_);
v_stop_boxed_5192_ = lean_unbox_usize(v_stop_5188_);
lean_dec(v_stop_5188_);
v_res_5193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5185_, v_as_5186_, v_i_boxed_5191_, v_stop_boxed_5192_, v_b_5189_);
lean_dec_ref(v_as_5186_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg___boxed(lean_object* v_f_5194_, lean_object* v_x_5195_, lean_object* v_x_5196_, lean_object* v___y_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5194_, v_x_5195_, v_x_5196_);
lean_dec_ref(v_x_5195_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(lean_object* v_cctx_5199_, lean_object* v_ngen_5200_, lean_object* v_env_5201_, lean_object* v_d_5202_, lean_object* v_act_5203_){
_start:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v_mainModule_5208_; lean_object* v___x_5209_; lean_object* v_map_u2082_5210_; lean_object* v___f_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; 
v___x_5205_ = l_Lean_Meta_LazyDiscrTree_Cache_empty(v_ngen_5200_);
v___x_5206_ = lean_st_mk_ref(v___x_5205_);
v___x_5207_ = l_Lean_Environment_header(v_env_5201_);
v_mainModule_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_mainModule_5208_);
lean_dec_ref(v___x_5207_);
lean_inc_ref(v_env_5201_);
v___x_5209_ = l_Lean_Environment_constants(v_env_5201_);
v_map_u2082_5210_ = lean_ctor_get(v___x_5209_, 1);
lean_inc_ref(v_map_u2082_5210_);
lean_dec_ref(v___x_5209_);
v___f_5211_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___lam__0___boxed), 10, 6);
lean_closure_set(v___f_5211_, 0, v_cctx_5199_);
lean_closure_set(v___f_5211_, 1, v_env_5201_);
lean_closure_set(v___f_5211_, 2, v_mainModule_5208_);
lean_closure_set(v___f_5211_, 3, v_d_5202_);
lean_closure_set(v___f_5211_, 4, v___x_5206_);
lean_closure_set(v___f_5211_, 5, v_act_5203_);
v___x_5212_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedInitResults___closed__1);
v___x_5213_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v___f_5211_, v_map_u2082_5210_, v___x_5212_);
lean_dec_ref(v_map_u2082_5210_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg___boxed(lean_object* v_cctx_5214_, lean_object* v_ngen_5215_, lean_object* v_env_5216_, lean_object* v_d_5217_, lean_object* v_act_5218_, lean_object* v_a_5219_){
_start:
{
lean_object* v_res_5220_; 
v_res_5220_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5214_, v_ngen_5215_, v_env_5216_, v_d_5217_, v_act_5218_);
return v_res_5220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(lean_object* v_00_u03b1_5221_, lean_object* v_cctx_5222_, lean_object* v_ngen_5223_, lean_object* v_env_5224_, lean_object* v_d_5225_, lean_object* v_act_5226_){
_start:
{
lean_object* v___x_5228_; 
v___x_5228_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_cctx_5222_, v_ngen_5223_, v_env_5224_, v_d_5225_, v_act_5226_);
return v___x_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___boxed(lean_object* v_00_u03b1_5229_, lean_object* v_cctx_5230_, lean_object* v_ngen_5231_, lean_object* v_env_5232_, lean_object* v_d_5233_, lean_object* v_act_5234_, lean_object* v_a_5235_){
_start:
{
lean_object* v_res_5236_; 
v_res_5236_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree(v_00_u03b1_5229_, v_cctx_5230_, v_ngen_5231_, v_env_5232_, v_d_5233_, v_act_5234_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(lean_object* v_map_5237_, lean_object* v_f_5238_, lean_object* v_init_5239_){
_start:
{
lean_object* v___x_5241_; 
v___x_5241_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5238_, v_map_5237_, v_init_5239_);
return v___x_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg___boxed(lean_object* v_map_5242_, lean_object* v_f_5243_, lean_object* v_init_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___redArg(v_map_5242_, v_f_5243_, v_init_5244_);
lean_dec_ref(v_map_5242_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(lean_object* v_00_u03c3_5247_, lean_object* v_00_u03b2_5248_, lean_object* v_map_5249_, lean_object* v_f_5250_, lean_object* v_init_5251_){
_start:
{
lean_object* v___x_5253_; 
v___x_5253_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5250_, v_map_5249_, v_init_5251_);
return v___x_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0___boxed(lean_object* v_00_u03c3_5254_, lean_object* v_00_u03b2_5255_, lean_object* v_map_5256_, lean_object* v_f_5257_, lean_object* v_init_5258_, lean_object* v___y_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0(v_00_u03c3_5254_, v_00_u03b2_5255_, v_map_5256_, v_f_5257_, v_init_5258_);
lean_dec_ref(v_map_5256_);
return v_res_5260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0(lean_object* v_00_u03c3_5261_, lean_object* v_00_u03b1_5262_, lean_object* v_00_u03b2_5263_, lean_object* v_f_5264_, lean_object* v_x_5265_, lean_object* v_x_5266_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___redArg(v_f_5264_, v_x_5265_, v_x_5266_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0___boxed(lean_object* v_00_u03c3_5269_, lean_object* v_00_u03b1_5270_, lean_object* v_00_u03b2_5271_, lean_object* v_f_5272_, lean_object* v_x_5273_, lean_object* v_x_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0(v_00_u03c3_5269_, v_00_u03b1_5270_, v_00_u03b2_5271_, v_f_5272_, v_x_5273_, v_x_5274_);
lean_dec_ref(v_x_5273_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5277_, lean_object* v_00_u03b2_5278_, lean_object* v_00_u03c3_5279_, lean_object* v_f_5280_, lean_object* v_as_5281_, size_t v_i_5282_, size_t v_stop_5283_, lean_object* v_b_5284_){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___redArg(v_f_5280_, v_as_5281_, v_i_5282_, v_stop_5283_, v_b_5284_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5287_, lean_object* v_00_u03b2_5288_, lean_object* v_00_u03c3_5289_, lean_object* v_f_5290_, lean_object* v_as_5291_, lean_object* v_i_5292_, lean_object* v_stop_5293_, lean_object* v_b_5294_, lean_object* v___y_5295_){
_start:
{
size_t v_i_boxed_5296_; size_t v_stop_boxed_5297_; lean_object* v_res_5298_; 
v_i_boxed_5296_ = lean_unbox_usize(v_i_5292_);
lean_dec(v_i_5292_);
v_stop_boxed_5297_ = lean_unbox_usize(v_stop_5293_);
lean_dec(v_stop_5293_);
v_res_5298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__1(v_00_u03b1_5287_, v_00_u03b2_5288_, v_00_u03c3_5289_, v_f_5290_, v_as_5291_, v_i_boxed_5296_, v_stop_boxed_5297_, v_b_5294_);
lean_dec_ref(v_as_5291_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2(lean_object* v_00_u03c3_5299_, lean_object* v_00_u03b1_5300_, lean_object* v_00_u03b2_5301_, lean_object* v_f_5302_, lean_object* v_keys_5303_, lean_object* v_vals_5304_, lean_object* v_heq_5305_, lean_object* v_i_5306_, lean_object* v_acc_5307_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___redArg(v_f_5302_, v_keys_5303_, v_vals_5304_, v_i_5306_, v_acc_5307_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03c3_5310_, lean_object* v_00_u03b1_5311_, lean_object* v_00_u03b2_5312_, lean_object* v_f_5313_, lean_object* v_keys_5314_, lean_object* v_vals_5315_, lean_object* v_heq_5316_, lean_object* v_i_5317_, lean_object* v_acc_5318_, lean_object* v___y_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree_spec__0_spec__0_spec__2(v_00_u03c3_5310_, v_00_u03b1_5311_, v_00_u03b2_5312_, v_f_5313_, v_keys_5314_, v_vals_5315_, v_heq_5316_, v_i_5317_, v_acc_5318_);
lean_dec_ref(v_vals_5315_);
lean_dec_ref(v_keys_5314_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(lean_object* v_x_5321_, lean_object* v_x_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_){
_start:
{
if (lean_obj_tag(v_x_5322_) == 0)
{
lean_object* v___x_5328_; 
v___x_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5328_, 0, v_x_5321_);
return v___x_5328_;
}
else
{
lean_object* v_head_5329_; lean_object* v_tail_5330_; lean_object* v___x_5331_; 
v_head_5329_ = lean_ctor_get(v_x_5322_, 0);
lean_inc(v_head_5329_);
v_tail_5330_ = lean_ctor_get(v_x_5322_, 1);
lean_inc(v_tail_5330_);
lean_dec_ref(v_x_5322_);
v___x_5331_ = l_Lean_Meta_LazyDiscrTree_dropKey___redArg(v_x_5321_, v_head_5329_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_object* v_a_5332_; 
v_a_5332_ = lean_ctor_get(v___x_5331_, 0);
lean_inc(v_a_5332_);
lean_dec_ref(v___x_5331_);
v_x_5321_ = v_a_5332_;
v_x_5322_ = v_tail_5330_;
goto _start;
}
else
{
lean_dec(v_tail_5330_);
return v___x_5331_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg___boxed(lean_object* v_x_5334_, lean_object* v_x_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_){
_start:
{
lean_object* v_res_5341_; 
v_res_5341_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5334_, v_x_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(lean_object* v_t_5342_, lean_object* v_keys_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_){
_start:
{
lean_object* v___x_5349_; 
v___x_5349_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5342_, v_keys_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_);
return v___x_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___redArg___boxed(lean_object* v_t_5350_, lean_object* v_keys_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_){
_start:
{
lean_object* v_res_5357_; 
v_res_5357_ = l_Lean_Meta_LazyDiscrTree_dropKeys___redArg(v_t_5350_, v_keys_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_);
lean_dec(v_a_5355_);
lean_dec_ref(v_a_5354_);
lean_dec(v_a_5353_);
lean_dec_ref(v_a_5352_);
return v_res_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys(lean_object* v_00_u03b1_5358_, lean_object* v_t_5359_, lean_object* v_keys_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_){
_start:
{
lean_object* v___x_5366_; 
v___x_5366_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_t_5359_, v_keys_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_);
return v___x_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_dropKeys___boxed(lean_object* v_00_u03b1_5367_, lean_object* v_t_5368_, lean_object* v_keys_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l_Lean_Meta_LazyDiscrTree_dropKeys(v_00_u03b1_5367_, v_t_5368_, v_keys_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_);
lean_dec(v_a_5373_);
lean_dec_ref(v_a_5372_);
lean_dec(v_a_5371_);
lean_dec_ref(v_a_5370_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(lean_object* v_00_u03b1_5376_, lean_object* v_x_5377_, lean_object* v_x_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_){
_start:
{
lean_object* v___x_5384_; 
v___x_5384_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_x_5377_, v_x_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
return v___x_5384_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___boxed(lean_object* v_00_u03b1_5385_, lean_object* v_x_5386_, lean_object* v_x_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0(v_00_u03b1_5385_, v_x_5386_, v_x_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(lean_object* v_as_5394_, size_t v_sz_5395_, size_t v_i_5396_, lean_object* v_b_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_){
_start:
{
uint8_t v___x_5404_; 
v___x_5404_ = lean_usize_dec_lt(v_i_5396_, v_sz_5395_);
if (v___x_5404_ == 0)
{
lean_object* v___x_5405_; 
v___x_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5405_, 0, v_b_5397_);
return v___x_5405_;
}
else
{
lean_object* v_a_5406_; lean_object* v___x_5407_; 
v_a_5406_ = lean_array_uget_borrowed(v_as_5394_, v_i_5396_);
v___x_5407_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5406_, v_b_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_);
if (lean_obj_tag(v___x_5407_) == 0)
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5420_; 
v_a_5408_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5420_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5410_ = v___x_5407_;
v_isShared_5411_ = v_isSharedCheck_5420_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5407_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5420_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
if (lean_obj_tag(v_a_5408_) == 0)
{
lean_object* v_a_5412_; lean_object* v___x_5414_; 
v_a_5412_ = lean_ctor_get(v_a_5408_, 0);
lean_inc(v_a_5412_);
lean_dec_ref(v_a_5408_);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 0, v_a_5412_);
v___x_5414_ = v___x_5410_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_a_5412_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
else
{
lean_object* v_a_5416_; size_t v___x_5417_; size_t v___x_5418_; 
lean_del_object(v___x_5410_);
v_a_5416_ = lean_ctor_get(v_a_5408_, 0);
lean_inc(v_a_5416_);
lean_dec_ref(v_a_5408_);
v___x_5417_ = ((size_t)1ULL);
v___x_5418_ = lean_usize_add(v_i_5396_, v___x_5417_);
v_i_5396_ = v___x_5418_;
v_b_5397_ = v_a_5416_;
goto _start;
}
}
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
v_a_5421_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5423_ = v___x_5407_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5407_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5426_; 
if (v_isShared_5424_ == 0)
{
v___x_5426_ = v___x_5423_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(lean_object* v_next_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_){
_start:
{
lean_object* v___x_5436_; uint8_t v___x_5437_; 
v___x_5436_ = lean_unsigned_to_nat(0u);
v___x_5437_ = lean_nat_dec_eq(v_next_5429_, v___x_5436_);
if (v___x_5437_ == 0)
{
lean_object* v___x_5438_; 
v___x_5438_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5429_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v_snd_5440_; lean_object* v_fst_5441_; lean_object* v_fst_5442_; lean_object* v_snd_5443_; lean_object* v___x_5444_; 
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
lean_inc(v_a_5439_);
lean_dec_ref(v___x_5438_);
v_snd_5440_ = lean_ctor_get(v_a_5439_, 1);
lean_inc(v_snd_5440_);
v_fst_5441_ = lean_ctor_get(v_a_5439_, 0);
lean_inc(v_fst_5441_);
lean_dec(v_a_5439_);
v_fst_5442_ = lean_ctor_get(v_snd_5440_, 0);
lean_inc(v_fst_5442_);
v_snd_5443_ = lean_ctor_get(v_snd_5440_, 1);
lean_inc(v_snd_5443_);
lean_dec(v_snd_5440_);
v___x_5444_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_fst_5442_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; lean_object* v_buckets_5446_; lean_object* v___x_5447_; size_t v_sz_5448_; size_t v___x_5449_; lean_object* v___x_5450_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
lean_inc(v_a_5445_);
lean_dec_ref(v___x_5444_);
v_buckets_5446_ = lean_ctor_get(v_snd_5443_, 1);
v___x_5447_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v_sz_5448_ = lean_array_size(v_buckets_5446_);
v___x_5449_ = ((size_t)0ULL);
v___x_5450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_buckets_5446_, v_sz_5448_, v___x_5449_, v___x_5447_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_);
if (lean_obj_tag(v___x_5450_) == 0)
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5464_; 
v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
v_isSharedCheck_5464_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5464_ == 0)
{
v___x_5453_ = v___x_5450_;
v_isShared_5454_ = v_isSharedCheck_5464_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5450_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5464_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5462_; 
v___x_5455_ = lean_st_ref_take(v_a_5430_);
v___x_5456_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5456_, 0, v___x_5447_);
lean_ctor_set(v___x_5456_, 1, v_fst_5442_);
lean_ctor_set(v___x_5456_, 2, v_snd_5443_);
lean_ctor_set(v___x_5456_, 3, v___x_5447_);
v___x_5457_ = lean_array_set(v___x_5455_, v_next_5429_, v___x_5456_);
v___x_5458_ = lean_st_ref_set(v_a_5430_, v___x_5457_);
v___x_5459_ = l_Array_append___redArg(v_fst_5441_, v_a_5445_);
lean_dec(v_a_5445_);
v___x_5460_ = l_Array_append___redArg(v___x_5459_, v_a_5451_);
lean_dec(v_a_5451_);
if (v_isShared_5454_ == 0)
{
lean_ctor_set(v___x_5453_, 0, v___x_5460_);
v___x_5462_ = v___x_5453_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5460_);
v___x_5462_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
return v___x_5462_;
}
}
}
else
{
lean_dec(v_a_5445_);
lean_dec(v_snd_5443_);
lean_dec(v_fst_5442_);
lean_dec(v_fst_5441_);
return v___x_5450_;
}
}
else
{
lean_dec(v_snd_5443_);
lean_dec(v_fst_5442_);
lean_dec(v_fst_5441_);
return v___x_5444_;
}
}
else
{
lean_object* v_a_5465_; lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5472_; 
v_a_5465_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5467_ = v___x_5438_;
v_isShared_5468_ = v_isSharedCheck_5472_;
goto v_resetjp_5466_;
}
else
{
lean_inc(v_a_5465_);
lean_dec(v___x_5438_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5472_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
lean_object* v___x_5470_; 
if (v_isShared_5468_ == 0)
{
v___x_5470_ = v___x_5467_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_a_5465_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
}
else
{
lean_object* v___x_5473_; lean_object* v___x_5474_; 
v___x_5473_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5473_);
return v___x_5474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
if (lean_obj_tag(v_a_5475_) == 0)
{
lean_object* v___x_5483_; lean_object* v___x_5484_; 
v___x_5483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5483_, 0, v_a_5476_);
v___x_5484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5483_);
return v___x_5484_;
}
else
{
lean_object* v_value_5485_; lean_object* v_tail_5486_; lean_object* v___x_5487_; 
v_value_5485_ = lean_ctor_get(v_a_5475_, 1);
v_tail_5486_ = lean_ctor_get(v_a_5475_, 2);
v___x_5487_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_value_5485_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v_a_5488_; lean_object* v___x_5489_; 
v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_a_5488_);
lean_dec_ref(v___x_5487_);
v___x_5489_ = l_Array_append___redArg(v_a_5476_, v_a_5488_);
lean_dec(v_a_5488_);
v_a_5475_ = v_tail_5486_;
v_a_5476_ = v___x_5489_;
goto _start;
}
else
{
lean_object* v_a_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5498_; 
lean_dec_ref(v_a_5476_);
v_a_5491_ = lean_ctor_get(v___x_5487_, 0);
v_isSharedCheck_5498_ = !lean_is_exclusive(v___x_5487_);
if (v_isSharedCheck_5498_ == 0)
{
v___x_5493_ = v___x_5487_;
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_a_5491_);
lean_dec(v___x_5487_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5496_; 
if (v_isShared_5494_ == 0)
{
v___x_5496_ = v___x_5493_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_a_5491_);
v___x_5496_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
return v___x_5496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg___boxed(lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_){
_start:
{
lean_object* v_res_5507_; 
v_res_5507_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5499_, v_a_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_);
lean_dec(v___y_5505_);
lean_dec_ref(v___y_5504_);
lean_dec(v___y_5503_);
lean_dec_ref(v___y_5502_);
lean_dec(v___y_5501_);
lean_dec(v_a_5499_);
return v_res_5507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg___boxed(lean_object* v_as_5508_, lean_object* v_sz_5509_, lean_object* v_i_5510_, lean_object* v_b_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_){
_start:
{
size_t v_sz_boxed_5518_; size_t v_i_boxed_5519_; lean_object* v_res_5520_; 
v_sz_boxed_5518_ = lean_unbox_usize(v_sz_5509_);
lean_dec(v_sz_5509_);
v_i_boxed_5519_ = lean_unbox_usize(v_i_5510_);
lean_dec(v_i_5510_);
v_res_5520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5508_, v_sz_boxed_5518_, v_i_boxed_5519_, v_b_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_);
lean_dec(v___y_5516_);
lean_dec_ref(v___y_5515_);
lean_dec(v___y_5514_);
lean_dec_ref(v___y_5513_);
lean_dec(v___y_5512_);
lean_dec_ref(v_as_5508_);
return v_res_5520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg___boxed(lean_object* v_next_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_){
_start:
{
lean_object* v_res_5528_; 
v_res_5528_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5521_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_);
lean_dec(v_a_5526_);
lean_dec_ref(v_a_5525_);
lean_dec(v_a_5524_);
lean_dec_ref(v_a_5523_);
lean_dec(v_a_5522_);
lean_dec(v_next_5521_);
return v_res_5528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(lean_object* v_00_u03b1_5529_, lean_object* v_next_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
lean_object* v___x_5537_; 
v___x_5537_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
return v___x_5537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___boxed(lean_object* v_00_u03b1_5538_, lean_object* v_next_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_){
_start:
{
lean_object* v_res_5546_; 
v_res_5546_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux(v_00_u03b1_5538_, v_next_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_);
lean_dec(v_a_5544_);
lean_dec_ref(v_a_5543_);
lean_dec(v_a_5542_);
lean_dec_ref(v_a_5541_);
lean_dec(v_a_5540_);
lean_dec(v_next_5539_);
return v_res_5546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(lean_object* v_00_u03b1_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_){
_start:
{
lean_object* v___x_5556_; 
v___x_5556_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___redArg(v_a_5548_, v_a_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
return v___x_5556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0___boxed(lean_object* v_00_u03b1_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_){
_start:
{
lean_object* v_res_5566_; 
v_res_5566_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__0(v_00_u03b1_5557_, v_a_5558_, v_a_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
lean_dec(v___y_5564_);
lean_dec_ref(v___y_5563_);
lean_dec(v___y_5562_);
lean_dec_ref(v___y_5561_);
lean_dec(v___y_5560_);
lean_dec(v_a_5558_);
return v_res_5566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(lean_object* v_00_u03b1_5567_, lean_object* v_as_5568_, size_t v_sz_5569_, size_t v_i_5570_, lean_object* v_b_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_){
_start:
{
lean_object* v___x_5578_; 
v___x_5578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___redArg(v_as_5568_, v_sz_5569_, v_i_5570_, v_b_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_);
return v___x_5578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1___boxed(lean_object* v_00_u03b1_5579_, lean_object* v_as_5580_, lean_object* v_sz_5581_, lean_object* v_i_5582_, lean_object* v_b_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_){
_start:
{
size_t v_sz_boxed_5590_; size_t v_i_boxed_5591_; lean_object* v_res_5592_; 
v_sz_boxed_5590_ = lean_unbox_usize(v_sz_5581_);
lean_dec(v_sz_5581_);
v_i_boxed_5591_ = lean_unbox_usize(v_i_5582_);
lean_dec(v_i_5582_);
v_res_5592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LazyDiscrTree_collectSubtreeAux_spec__1(v_00_u03b1_5579_, v_as_5580_, v_sz_boxed_5590_, v_i_boxed_5591_, v_b_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v___y_5584_);
lean_dec_ref(v_as_5580_);
return v_res_5592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(lean_object* v_next_5593_, lean_object* v_rest_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_){
_start:
{
lean_object* v___x_5601_; uint8_t v___x_5602_; 
v___x_5601_ = lean_unsigned_to_nat(0u);
v___x_5602_ = lean_nat_dec_eq(v_next_5593_, v___x_5601_);
if (v___x_5602_ == 0)
{
lean_object* v___x_5603_; 
v___x_5603_ = l_Lean_Meta_LazyDiscrTree_evalNode___redArg(v_next_5593_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_, v_a_5599_);
if (lean_obj_tag(v___x_5603_) == 0)
{
lean_object* v_a_5604_; lean_object* v_snd_5605_; 
v_a_5604_ = lean_ctor_get(v___x_5603_, 0);
lean_inc(v_a_5604_);
lean_dec_ref(v___x_5603_);
v_snd_5605_ = lean_ctor_get(v_a_5604_, 1);
lean_inc(v_snd_5605_);
lean_dec(v_a_5604_);
if (lean_obj_tag(v_rest_5594_) == 0)
{
lean_object* v___x_5606_; 
lean_dec(v_snd_5605_);
v___x_5606_ = l_Lean_Meta_LazyDiscrTree_collectSubtreeAux___redArg(v_next_5593_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_, v_a_5599_);
lean_dec(v_next_5593_);
return v___x_5606_;
}
else
{
lean_object* v_fst_5607_; lean_object* v_snd_5608_; lean_object* v_head_5609_; lean_object* v_tail_5610_; lean_object* v___x_5611_; uint8_t v___x_5612_; 
lean_dec(v_next_5593_);
v_fst_5607_ = lean_ctor_get(v_snd_5605_, 0);
lean_inc(v_fst_5607_);
v_snd_5608_ = lean_ctor_get(v_snd_5605_, 1);
lean_inc(v_snd_5608_);
lean_dec(v_snd_5605_);
v_head_5609_ = lean_ctor_get(v_rest_5594_, 0);
v_tail_5610_ = lean_ctor_get(v_rest_5594_, 1);
v___x_5611_ = lean_box(3);
v___x_5612_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_head_5609_, v___x_5611_);
if (v___x_5612_ == 0)
{
lean_object* v___x_5613_; 
lean_dec(v_fst_5607_);
v___x_5613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_snd_5608_, v_head_5609_, v___x_5601_);
lean_dec(v_snd_5608_);
v_next_5593_ = v___x_5613_;
v_rest_5594_ = v_tail_5610_;
goto _start;
}
else
{
lean_dec(v_snd_5608_);
v_next_5593_ = v_fst_5607_;
v_rest_5594_ = v_tail_5610_;
goto _start;
}
}
}
else
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec(v_next_5593_);
v_a_5616_ = lean_ctor_get(v___x_5603_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5603_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5603_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5603_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5616_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
else
{
lean_object* v___x_5624_; lean_object* v___x_5625_; 
lean_dec(v_next_5593_);
v___x_5624_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5624_);
return v___x_5625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg___boxed(lean_object* v_next_5626_, lean_object* v_rest_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_){
_start:
{
lean_object* v_res_5634_; 
v_res_5634_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5626_, v_rest_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_);
lean_dec(v_a_5632_);
lean_dec_ref(v_a_5631_);
lean_dec(v_a_5630_);
lean_dec_ref(v_a_5629_);
lean_dec(v_a_5628_);
lean_dec(v_rest_5627_);
return v_res_5634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux(lean_object* v_00_u03b1_5635_, lean_object* v_next_5636_, lean_object* v_rest_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_){
_start:
{
lean_object* v___x_5644_; 
v___x_5644_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux___redArg(v_next_5636_, v_rest_5637_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_);
return v___x_5644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed(lean_object* v_00_u03b1_5645_, lean_object* v_next_5646_, lean_object* v_rest_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_){
_start:
{
lean_object* v_res_5654_; 
v_res_5654_ = l_Lean_Meta_LazyDiscrTree_extractKeyAux(v_00_u03b1_5645_, v_next_5646_, v_rest_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_);
lean_dec(v_a_5652_);
lean_dec_ref(v_a_5651_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
lean_dec(v_a_5648_);
lean_dec(v_rest_5647_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg(lean_object* v_t_5655_, lean_object* v_path_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_){
_start:
{
if (lean_obj_tag(v_path_5656_) == 0)
{
lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; 
v___x_5662_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set(v___x_5663_, 1, v_t_5655_);
v___x_5664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5663_);
return v___x_5664_;
}
else
{
lean_object* v_head_5665_; lean_object* v_tail_5666_; lean_object* v_roots_5667_; lean_object* v___x_5668_; lean_object* v_idx_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; 
v_head_5665_ = lean_ctor_get(v_path_5656_, 0);
lean_inc(v_head_5665_);
v_tail_5666_ = lean_ctor_get(v_path_5656_, 1);
lean_inc(v_tail_5666_);
lean_dec_ref(v_path_5656_);
v_roots_5667_ = lean_ctor_get(v_t_5655_, 1);
v___x_5668_ = lean_unsigned_to_nat(0u);
v_idx_5669_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_LazyDiscrTree_dropKeyAux_spec__0___redArg(v_roots_5667_, v_head_5665_, v___x_5668_);
lean_dec(v_head_5665_);
v___x_5670_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_extractKeyAux___boxed), 9, 3);
lean_closure_set(v___x_5670_, 0, lean_box(0));
lean_closure_set(v___x_5670_, 1, v_idx_5669_);
lean_closure_set(v___x_5670_, 2, v_tail_5666_);
v___x_5671_ = l_Lean_Meta_LazyDiscrTree_runMatch___redArg(v_t_5655_, v___x_5670_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_);
return v___x_5671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___redArg___boxed(lean_object* v_t_5672_, lean_object* v_path_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v_res_5679_; 
v_res_5679_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5672_, v_path_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_);
lean_dec(v_a_5677_);
lean_dec_ref(v_a_5676_);
lean_dec(v_a_5675_);
lean_dec_ref(v_a_5674_);
return v_res_5679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey(lean_object* v_00_u03b1_5680_, lean_object* v_t_5681_, lean_object* v_path_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_){
_start:
{
lean_object* v___x_5688_; 
v___x_5688_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_t_5681_, v_path_5682_, v_a_5683_, v_a_5684_, v_a_5685_, v_a_5686_);
return v___x_5688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKey___boxed(lean_object* v_00_u03b1_5689_, lean_object* v_t_5690_, lean_object* v_path_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_){
_start:
{
lean_object* v_res_5697_; 
v_res_5697_ = l_Lean_Meta_LazyDiscrTree_extractKey(v_00_u03b1_5689_, v_t_5690_, v_path_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_);
lean_dec(v_a_5695_);
lean_dec_ref(v_a_5694_);
lean_dec(v_a_5693_);
lean_dec_ref(v_a_5692_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(lean_object* v_as_x27_5698_, lean_object* v_b_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_){
_start:
{
if (lean_obj_tag(v_as_x27_5698_) == 0)
{
lean_object* v___x_5705_; 
v___x_5705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5705_, 0, v_b_5699_);
return v___x_5705_;
}
else
{
lean_object* v_head_5706_; lean_object* v_tail_5707_; lean_object* v_fst_5708_; lean_object* v_snd_5709_; lean_object* v___x_5710_; 
v_head_5706_ = lean_ctor_get(v_as_x27_5698_, 0);
lean_inc(v_head_5706_);
v_tail_5707_ = lean_ctor_get(v_as_x27_5698_, 1);
lean_inc(v_tail_5707_);
lean_dec_ref(v_as_x27_5698_);
v_fst_5708_ = lean_ctor_get(v_b_5699_, 0);
lean_inc(v_fst_5708_);
v_snd_5709_ = lean_ctor_get(v_b_5699_, 1);
lean_inc(v_snd_5709_);
lean_dec_ref(v_b_5699_);
v___x_5710_ = l_Lean_Meta_LazyDiscrTree_extractKey___redArg(v_snd_5709_, v_head_5706_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_);
if (lean_obj_tag(v___x_5710_) == 0)
{
lean_object* v_a_5711_; lean_object* v_fst_5712_; lean_object* v_snd_5713_; lean_object* v___x_5715_; uint8_t v_isShared_5716_; uint8_t v_isSharedCheck_5722_; 
v_a_5711_ = lean_ctor_get(v___x_5710_, 0);
lean_inc(v_a_5711_);
lean_dec_ref(v___x_5710_);
v_fst_5712_ = lean_ctor_get(v_a_5711_, 0);
v_snd_5713_ = lean_ctor_get(v_a_5711_, 1);
v_isSharedCheck_5722_ = !lean_is_exclusive(v_a_5711_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5715_ = v_a_5711_;
v_isShared_5716_ = v_isSharedCheck_5722_;
goto v_resetjp_5714_;
}
else
{
lean_inc(v_snd_5713_);
lean_inc(v_fst_5712_);
lean_dec(v_a_5711_);
v___x_5715_ = lean_box(0);
v_isShared_5716_ = v_isSharedCheck_5722_;
goto v_resetjp_5714_;
}
v_resetjp_5714_:
{
lean_object* v___x_5717_; lean_object* v___x_5719_; 
v___x_5717_ = l_Array_append___redArg(v_fst_5708_, v_fst_5712_);
lean_dec(v_fst_5712_);
if (v_isShared_5716_ == 0)
{
lean_ctor_set(v___x_5715_, 0, v___x_5717_);
v___x_5719_ = v___x_5715_;
goto v_reusejp_5718_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v___x_5717_);
lean_ctor_set(v_reuseFailAlloc_5721_, 1, v_snd_5713_);
v___x_5719_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5718_;
}
v_reusejp_5718_:
{
v_as_x27_5698_ = v_tail_5707_;
v_b_5699_ = v___x_5719_;
goto _start;
}
}
}
else
{
lean_dec(v_fst_5708_);
lean_dec(v_tail_5707_);
return v___x_5710_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg___boxed(lean_object* v_as_x27_5723_, lean_object* v_b_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_){
_start:
{
lean_object* v_res_5730_; 
v_res_5730_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5723_, v_b_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_);
lean_dec(v___y_5728_);
lean_dec_ref(v___y_5727_);
lean_dec(v___y_5726_);
lean_dec_ref(v___y_5725_);
return v_res_5730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(lean_object* v_t_5731_, lean_object* v_keys_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_){
_start:
{
lean_object* v_allExtracted_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; 
v_allExtracted_5738_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___x_5739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5739_, 0, v_allExtracted_5738_);
lean_ctor_set(v___x_5739_, 1, v_t_5731_);
v___x_5740_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_keys_5732_, v___x_5739_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_);
if (lean_obj_tag(v___x_5740_) == 0)
{
lean_object* v_a_5741_; lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5757_; 
v_a_5741_ = lean_ctor_get(v___x_5740_, 0);
v_isSharedCheck_5757_ = !lean_is_exclusive(v___x_5740_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5743_ = v___x_5740_;
v_isShared_5744_ = v_isSharedCheck_5757_;
goto v_resetjp_5742_;
}
else
{
lean_inc(v_a_5741_);
lean_dec(v___x_5740_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5757_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v_fst_5745_; lean_object* v_snd_5746_; lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5756_; 
v_fst_5745_ = lean_ctor_get(v_a_5741_, 0);
v_snd_5746_ = lean_ctor_get(v_a_5741_, 1);
v_isSharedCheck_5756_ = !lean_is_exclusive(v_a_5741_);
if (v_isSharedCheck_5756_ == 0)
{
v___x_5748_ = v_a_5741_;
v_isShared_5749_ = v_isSharedCheck_5756_;
goto v_resetjp_5747_;
}
else
{
lean_inc(v_snd_5746_);
lean_inc(v_fst_5745_);
lean_dec(v_a_5741_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5756_;
goto v_resetjp_5747_;
}
v_resetjp_5747_:
{
lean_object* v___x_5751_; 
if (v_isShared_5749_ == 0)
{
v___x_5751_ = v___x_5748_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_fst_5745_);
lean_ctor_set(v_reuseFailAlloc_5755_, 1, v_snd_5746_);
v___x_5751_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
lean_object* v___x_5753_; 
if (v_isShared_5744_ == 0)
{
lean_ctor_set(v___x_5743_, 0, v___x_5751_);
v___x_5753_ = v___x_5743_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5751_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
else
{
return v___x_5740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___redArg___boxed(lean_object* v_t_5758_, lean_object* v_keys_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5758_, v_keys_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_);
lean_dec(v_a_5763_);
lean_dec_ref(v_a_5762_);
lean_dec(v_a_5761_);
lean_dec_ref(v_a_5760_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys(lean_object* v_00_u03b1_5766_, lean_object* v_t_5767_, lean_object* v_keys_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_){
_start:
{
lean_object* v___x_5774_; 
v___x_5774_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_t_5767_, v_keys_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_);
return v___x_5774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_extractKeys___boxed(lean_object* v_00_u03b1_5775_, lean_object* v_t_5776_, lean_object* v_keys_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_){
_start:
{
lean_object* v_res_5783_; 
v_res_5783_ = l_Lean_Meta_LazyDiscrTree_extractKeys(v_00_u03b1_5775_, v_t_5776_, v_keys_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_);
lean_dec(v_a_5781_);
lean_dec_ref(v_a_5780_);
lean_dec(v_a_5779_);
lean_dec_ref(v_a_5778_);
return v_res_5783_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(lean_object* v_00_u03b1_5784_, lean_object* v_as_5785_, lean_object* v_as_x27_5786_, lean_object* v_b_5787_, lean_object* v_a_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_){
_start:
{
lean_object* v___x_5794_; 
v___x_5794_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___redArg(v_as_x27_5786_, v_b_5787_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_);
return v___x_5794_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0___boxed(lean_object* v_00_u03b1_5795_, lean_object* v_as_5796_, lean_object* v_as_x27_5797_, lean_object* v_b_5798_, lean_object* v_a_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_){
_start:
{
lean_object* v_res_5805_; 
v_res_5805_ = l_List_forIn_x27_loop___at___00Lean_Meta_LazyDiscrTree_extractKeys_spec__0(v_00_u03b1_5795_, v_as_5796_, v_as_x27_5797_, v_b_5798_, v_a_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
lean_dec(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v___y_5801_);
lean_dec_ref(v___y_5800_);
lean_dec(v_as_5796_);
return v_res_5805_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1(void){
_start:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5807_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__0));
v___x_5808_ = l_Lean_stringToMessageData(v___x_5807_);
return v___x_5808_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3(void){
_start:
{
lean_object* v___x_5810_; lean_object* v___x_5811_; 
v___x_5810_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__2));
v___x_5811_ = l_Lean_stringToMessageData(v___x_5810_);
return v___x_5811_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5(void){
_start:
{
lean_object* v___x_5813_; lean_object* v___x_5814_; 
v___x_5813_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__4));
v___x_5814_ = l_Lean_stringToMessageData(v___x_5813_);
return v___x_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(lean_object* v_inst_5815_, lean_object* v_inst_5816_, lean_object* v_inst_5817_, lean_object* v_inst_5818_, lean_object* v_f_5819_){
_start:
{
lean_object* v_module_5820_; lean_object* v_const_5821_; lean_object* v_exception_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; 
v_module_5820_ = lean_ctor_get(v_f_5819_, 0);
lean_inc(v_module_5820_);
v_const_5821_ = lean_ctor_get(v_f_5819_, 1);
lean_inc(v_const_5821_);
v_exception_5822_ = lean_ctor_get(v_f_5819_, 2);
lean_inc_ref(v_exception_5822_);
lean_dec_ref(v_f_5819_);
v___x_5823_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_5824_ = l_Lean_MessageData_ofName(v_const_5821_);
v___x_5825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5825_, 0, v___x_5823_);
lean_ctor_set(v___x_5825_, 1, v___x_5824_);
v___x_5826_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_5827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5827_, 0, v___x_5825_);
lean_ctor_set(v___x_5827_, 1, v___x_5826_);
v___x_5828_ = l_Lean_MessageData_ofName(v_module_5820_);
v___x_5829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5829_, 0, v___x_5827_);
lean_ctor_set(v___x_5829_, 1, v___x_5828_);
v___x_5830_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_5831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5831_, 0, v___x_5829_);
lean_ctor_set(v___x_5831_, 1, v___x_5830_);
v___x_5832_ = l_Lean_Exception_toMessageData(v_exception_5822_);
v___x_5833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5833_, 0, v___x_5831_);
lean_ctor_set(v___x_5833_, 1, v___x_5832_);
v___x_5834_ = l_Lean_logError___redArg(v_inst_5815_, v_inst_5816_, v_inst_5817_, v_inst_5818_, v___x_5833_);
return v___x_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure(lean_object* v_m_5835_, lean_object* v_inst_5836_, lean_object* v_inst_5837_, lean_object* v_inst_5838_, lean_object* v_inst_5839_, lean_object* v_f_5840_){
_start:
{
lean_object* v___x_5841_; 
v___x_5841_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5836_, v_inst_5837_, v_inst_5838_, v_inst_5839_, v_f_5840_);
return v___x_5841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0(lean_object* v_toApplicative_5842_, lean_object* v_tasks_5843_, lean_object* v_t_5844_){
_start:
{
lean_object* v_toPure_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; 
v_toPure_5845_ = lean_ctor_get(v_toApplicative_5842_, 1);
lean_inc(v_toPure_5845_);
lean_dec_ref(v_toApplicative_5842_);
v___x_5846_ = lean_array_push(v_tasks_5843_, v_t_5844_);
v___x_5847_ = lean_apply_2(v_toPure_5845_, lean_box(0), v___x_5846_);
return v___x_5847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(lean_object* v_inst_5848_, lean_object* v_inst_5849_, lean_object* v_cctx_5850_, lean_object* v_env_5851_, lean_object* v_act_5852_, lean_object* v_constantsPerTask_5853_, lean_object* v_n_5854_, lean_object* v_ngen_5855_, lean_object* v_tasks_5856_, lean_object* v_start_5857_, lean_object* v_cnt_5858_, lean_object* v_idx_5859_){
_start:
{
lean_object* v___x_5860_; lean_object* v_moduleData_5861_; lean_object* v___x_5862_; uint8_t v___x_5863_; 
v___x_5860_ = l_Lean_Environment_header(v_env_5851_);
v_moduleData_5861_ = lean_ctor_get(v___x_5860_, 6);
lean_inc_ref(v_moduleData_5861_);
lean_dec_ref(v___x_5860_);
v___x_5862_ = lean_array_get_size(v_moduleData_5861_);
v___x_5863_ = lean_nat_dec_lt(v_idx_5859_, v___x_5862_);
if (v___x_5863_ == 0)
{
uint8_t v___x_5864_; 
lean_dec_ref(v_moduleData_5861_);
lean_dec(v_idx_5859_);
lean_dec(v_cnt_5858_);
lean_dec(v_constantsPerTask_5853_);
v___x_5864_ = lean_nat_dec_lt(v_start_5857_, v_n_5854_);
if (v___x_5864_ == 0)
{
lean_object* v_toApplicative_5865_; lean_object* v_toPure_5866_; lean_object* v___x_5867_; 
lean_dec(v_start_5857_);
lean_dec_ref(v_ngen_5855_);
lean_dec(v_n_5854_);
lean_dec_ref(v_act_5852_);
lean_dec_ref(v_env_5851_);
lean_dec_ref(v_cctx_5850_);
lean_dec(v_inst_5849_);
v_toApplicative_5865_ = lean_ctor_get(v_inst_5848_, 0);
lean_inc_ref(v_toApplicative_5865_);
lean_dec_ref(v_inst_5848_);
v_toPure_5866_ = lean_ctor_get(v_toApplicative_5865_, 1);
lean_inc(v_toPure_5866_);
lean_dec_ref(v_toApplicative_5865_);
v___x_5867_ = lean_apply_2(v_toPure_5866_, lean_box(0), v_tasks_5856_);
return v___x_5867_;
}
else
{
lean_object* v_namePrefix_5868_; lean_object* v_idx_5869_; lean_object* v___x_5871_; uint8_t v_isShared_5872_; uint8_t v_isSharedCheck_5886_; 
v_namePrefix_5868_ = lean_ctor_get(v_ngen_5855_, 0);
v_idx_5869_ = lean_ctor_get(v_ngen_5855_, 1);
v_isSharedCheck_5886_ = !lean_is_exclusive(v_ngen_5855_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5871_ = v_ngen_5855_;
v_isShared_5872_ = v_isSharedCheck_5886_;
goto v_resetjp_5870_;
}
else
{
lean_inc(v_idx_5869_);
lean_inc(v_namePrefix_5868_);
lean_dec(v_ngen_5855_);
v___x_5871_ = lean_box(0);
v_isShared_5872_ = v_isSharedCheck_5886_;
goto v_resetjp_5870_;
}
v_resetjp_5870_:
{
lean_object* v_toApplicative_5873_; lean_object* v_toBind_5874_; lean_object* v___f_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5879_; 
v_toApplicative_5873_ = lean_ctor_get(v_inst_5848_, 0);
lean_inc_ref(v_toApplicative_5873_);
v_toBind_5874_ = lean_ctor_get(v_inst_5848_, 1);
lean_inc(v_toBind_5874_);
lean_dec_ref(v_inst_5848_);
v___f_5875_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_5875_, 0, v_toApplicative_5873_);
lean_closure_set(v___f_5875_, 1, v_tasks_5856_);
v___x_5876_ = l_Lean_Name_num___override(v_namePrefix_5868_, v_idx_5869_);
v___x_5877_ = lean_unsigned_to_nat(1u);
if (v_isShared_5872_ == 0)
{
lean_ctor_set(v___x_5871_, 1, v___x_5877_);
lean_ctor_set(v___x_5871_, 0, v___x_5876_);
v___x_5879_ = v___x_5871_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v___x_5876_);
lean_ctor_set(v_reuseFailAlloc_5885_, 1, v___x_5877_);
v___x_5879_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; 
v___x_5880_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5880_, 0, lean_box(0));
lean_closure_set(v___x_5880_, 1, v_cctx_5850_);
lean_closure_set(v___x_5880_, 2, v___x_5879_);
lean_closure_set(v___x_5880_, 3, v_env_5851_);
lean_closure_set(v___x_5880_, 4, v_act_5852_);
lean_closure_set(v___x_5880_, 5, v_start_5857_);
lean_closure_set(v___x_5880_, 6, v_n_5854_);
v___x_5881_ = lean_unsigned_to_nat(0u);
v___x_5882_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5882_, 0, lean_box(0));
lean_closure_set(v___x_5882_, 1, v___x_5880_);
lean_closure_set(v___x_5882_, 2, v___x_5881_);
v___x_5883_ = lean_apply_2(v_inst_5849_, lean_box(0), v___x_5882_);
v___x_5884_ = lean_apply_4(v_toBind_5874_, lean_box(0), lean_box(0), v___x_5883_, v___f_5875_);
return v___x_5884_;
}
}
}
}
else
{
lean_object* v_mdata_5887_; lean_object* v_constants_5888_; lean_object* v___x_5889_; lean_object* v_cnt_5890_; uint8_t v___x_5891_; 
v_mdata_5887_ = lean_array_fget(v_moduleData_5861_, v_idx_5859_);
lean_dec_ref(v_moduleData_5861_);
v_constants_5888_ = lean_ctor_get(v_mdata_5887_, 2);
lean_inc_ref(v_constants_5888_);
lean_dec(v_mdata_5887_);
v___x_5889_ = lean_array_get_size(v_constants_5888_);
lean_dec_ref(v_constants_5888_);
v_cnt_5890_ = lean_nat_add(v_cnt_5858_, v___x_5889_);
lean_dec(v_cnt_5858_);
v___x_5891_ = lean_nat_dec_lt(v_constantsPerTask_5853_, v_cnt_5890_);
if (v___x_5891_ == 0)
{
lean_object* v___x_5892_; lean_object* v___x_5893_; 
v___x_5892_ = lean_unsigned_to_nat(1u);
v___x_5893_ = lean_nat_add(v_idx_5859_, v___x_5892_);
lean_dec(v_idx_5859_);
v_cnt_5858_ = v_cnt_5890_;
v_idx_5859_ = v___x_5893_;
goto _start;
}
else
{
lean_object* v_namePrefix_5895_; lean_object* v_idx_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5915_; 
lean_dec(v_cnt_5890_);
v_namePrefix_5895_ = lean_ctor_get(v_ngen_5855_, 0);
v_idx_5896_ = lean_ctor_get(v_ngen_5855_, 1);
v_isSharedCheck_5915_ = !lean_is_exclusive(v_ngen_5855_);
if (v_isSharedCheck_5915_ == 0)
{
v___x_5898_ = v_ngen_5855_;
v_isShared_5899_ = v_isSharedCheck_5915_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_idx_5896_);
lean_inc(v_namePrefix_5895_);
lean_dec(v_ngen_5855_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5915_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v_toBind_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5904_; 
v_toBind_5900_ = lean_ctor_get(v_inst_5848_, 1);
lean_inc(v_toBind_5900_);
lean_inc(v_idx_5896_);
lean_inc(v_namePrefix_5895_);
v___x_5901_ = l_Lean_Name_num___override(v_namePrefix_5895_, v_idx_5896_);
v___x_5902_ = lean_unsigned_to_nat(1u);
if (v_isShared_5899_ == 0)
{
lean_ctor_set(v___x_5898_, 1, v___x_5902_);
lean_ctor_set(v___x_5898_, 0, v___x_5901_);
v___x_5904_ = v___x_5898_;
goto v_reusejp_5903_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v___x_5901_);
lean_ctor_set(v_reuseFailAlloc_5914_, 1, v___x_5902_);
v___x_5904_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5903_;
}
v_reusejp_5903_:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___f_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5905_ = lean_nat_add(v_idx_5896_, v___x_5902_);
lean_dec(v_idx_5896_);
v___x_5906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5906_, 0, v_namePrefix_5895_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v___x_5907_ = lean_nat_add(v_idx_5859_, v___x_5902_);
lean_dec(v_idx_5859_);
lean_inc(v___x_5907_);
lean_inc_ref(v_act_5852_);
lean_inc_ref(v_env_5851_);
lean_inc_ref(v_cctx_5850_);
lean_inc(v_inst_5849_);
v___f_5908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1), 11, 10);
lean_closure_set(v___f_5908_, 0, v_tasks_5856_);
lean_closure_set(v___f_5908_, 1, v_inst_5848_);
lean_closure_set(v___f_5908_, 2, v_inst_5849_);
lean_closure_set(v___f_5908_, 3, v_cctx_5850_);
lean_closure_set(v___f_5908_, 4, v_env_5851_);
lean_closure_set(v___f_5908_, 5, v_act_5852_);
lean_closure_set(v___f_5908_, 6, v_constantsPerTask_5853_);
lean_closure_set(v___f_5908_, 7, v_n_5854_);
lean_closure_set(v___f_5908_, 8, v___x_5906_);
lean_closure_set(v___f_5908_, 9, v___x_5907_);
v___x_5909_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_5909_, 0, lean_box(0));
lean_closure_set(v___x_5909_, 1, v_cctx_5850_);
lean_closure_set(v___x_5909_, 2, v___x_5904_);
lean_closure_set(v___x_5909_, 3, v_env_5851_);
lean_closure_set(v___x_5909_, 4, v_act_5852_);
lean_closure_set(v___x_5909_, 5, v_start_5857_);
lean_closure_set(v___x_5909_, 6, v___x_5907_);
v___x_5910_ = lean_unsigned_to_nat(0u);
v___x_5911_ = lean_alloc_closure((void*)(l_BaseIO_asTask___boxed), 4, 3);
lean_closure_set(v___x_5911_, 0, lean_box(0));
lean_closure_set(v___x_5911_, 1, v___x_5909_);
lean_closure_set(v___x_5911_, 2, v___x_5910_);
v___x_5912_ = lean_apply_2(v_inst_5849_, lean_box(0), v___x_5911_);
v___x_5913_ = lean_apply_4(v_toBind_5900_, lean_box(0), lean_box(0), v___x_5912_, v___f_5908_);
return v___x_5913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg___lam__1(lean_object* v_tasks_5916_, lean_object* v_inst_5917_, lean_object* v_inst_5918_, lean_object* v_cctx_5919_, lean_object* v_env_5920_, lean_object* v_act_5921_, lean_object* v_constantsPerTask_5922_, lean_object* v_n_5923_, lean_object* v___x_5924_, lean_object* v___x_5925_, lean_object* v_t_5926_){
_start:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5927_ = lean_array_push(v_tasks_5916_, v_t_5926_);
v___x_5928_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_5925_);
v___x_5929_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5917_, v_inst_5918_, v_cctx_5919_, v_env_5920_, v_act_5921_, v_constantsPerTask_5922_, v_n_5923_, v___x_5924_, v___x_5927_, v___x_5925_, v___x_5928_, v___x_5925_);
return v___x_5929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go(lean_object* v_m_5930_, lean_object* v_00_u03b1_5931_, lean_object* v_inst_5932_, lean_object* v_inst_5933_, lean_object* v_cctx_5934_, lean_object* v_env_5935_, lean_object* v_act_5936_, lean_object* v_constantsPerTask_5937_, lean_object* v_n_5938_, lean_object* v_ngen_5939_, lean_object* v_tasks_5940_, lean_object* v_start_5941_, lean_object* v_cnt_5942_, lean_object* v_idx_5943_){
_start:
{
lean_object* v___x_5944_; 
v___x_5944_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_5932_, v_inst_5933_, v_cctx_5934_, v_env_5935_, v_act_5936_, v_constantsPerTask_5937_, v_n_5938_, v_ngen_5939_, v_tasks_5940_, v_start_5941_, v_cnt_5942_, v_idx_5943_);
return v___x_5944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter___redArg(lean_object* v_x_5945_, lean_object* v_h__1_5946_){
_start:
{
lean_object* v_fst_5947_; lean_object* v_snd_5948_; lean_object* v___x_5949_; 
v_fst_5947_ = lean_ctor_get(v_x_5945_, 0);
lean_inc(v_fst_5947_);
v_snd_5948_ = lean_ctor_get(v_x_5945_, 1);
lean_inc(v_snd_5948_);
lean_dec_ref(v_x_5945_);
v___x_5949_ = lean_apply_2(v_h__1_5946_, v_fst_5947_, v_snd_5948_);
return v___x_5949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_getChildNgen_match__1_splitter(lean_object* v_motive_5950_, lean_object* v_x_5951_, lean_object* v_h__1_5952_){
_start:
{
lean_object* v_fst_5953_; lean_object* v_snd_5954_; lean_object* v___x_5955_; 
v_fst_5953_ = lean_ctor_get(v_x_5951_, 0);
lean_inc(v_fst_5953_);
v_snd_5954_ = lean_ctor_get(v_x_5951_, 1);
lean_inc(v_snd_5954_);
lean_dec_ref(v_x_5951_);
v___x_5955_ = lean_apply_2(v_h__1_5952_, v_fst_5953_, v_snd_5954_);
return v___x_5955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0(lean_object* v_inst_5956_, lean_object* v_inst_5957_, lean_object* v_inst_5958_, lean_object* v_inst_5959_, lean_object* v_x_5960_, lean_object* v___y_5961_){
_start:
{
lean_object* v___x_5962_; 
v___x_5962_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg(v_inst_5956_, v_inst_5957_, v_inst_5958_, v_inst_5959_, v___y_5961_);
return v___x_5962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1(lean_object* v_r_5963_, lean_object* v_toPure_5964_, lean_object* v_____r_5965_){
_start:
{
lean_object* v_tree_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; 
v_tree_5966_ = lean_ctor_get(v_r_5963_, 0);
lean_inc_ref(v_tree_5966_);
lean_dec_ref(v_r_5963_);
v___x_5967_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_5966_);
v___x_5968_ = lean_apply_2(v_toPure_5964_, lean_box(0), v___x_5967_);
return v___x_5968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2(lean_object* v___x_5969_, lean_object* v___x_5970_, lean_object* v_toPure_5971_, lean_object* v_toBind_5972_, lean_object* v_inst_5973_, lean_object* v___f_5974_, lean_object* v_tasks_5975_){
_start:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v_r_5981_; lean_object* v_errors_5982_; lean_object* v___f_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; uint8_t v___x_5986_; 
v___x_5976_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__1);
lean_inc(v___x_5969_);
v___x_5977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5969_);
lean_ctor_set(v___x_5977_, 1, v___x_5976_);
v___x_5978_ = lean_mk_empty_array_with_capacity(v___x_5969_);
lean_inc_ref(v___x_5978_);
v___x_5979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5977_);
lean_ctor_set(v___x_5979_, 1, v___x_5978_);
v___x_5980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5980_, 0, v___x_5979_);
lean_ctor_set(v___x_5980_, 1, v___x_5978_);
v_r_5981_ = l_Lean_Meta_LazyDiscrTree_combineGet___redArg(v___x_5970_, v___x_5980_, v_tasks_5975_);
v_errors_5982_ = lean_ctor_get(v_r_5981_, 1);
lean_inc_ref(v_errors_5982_);
lean_inc(v_toPure_5971_);
v___f_5983_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__1), 3, 2);
lean_closure_set(v___f_5983_, 0, v_r_5981_);
lean_closure_set(v___f_5983_, 1, v_toPure_5971_);
v___x_5984_ = lean_array_get_size(v_errors_5982_);
v___x_5985_ = lean_box(0);
v___x_5986_ = lean_nat_dec_lt(v___x_5969_, v___x_5984_);
lean_dec(v___x_5969_);
if (v___x_5986_ == 0)
{
lean_object* v___x_5987_; lean_object* v___x_5988_; 
lean_dec_ref(v_errors_5982_);
lean_dec(v___f_5974_);
lean_dec_ref(v_inst_5973_);
v___x_5987_ = lean_apply_2(v_toPure_5971_, lean_box(0), v___x_5985_);
v___x_5988_ = lean_apply_4(v_toBind_5972_, lean_box(0), lean_box(0), v___x_5987_, v___f_5983_);
return v___x_5988_;
}
else
{
uint8_t v___x_5989_; 
v___x_5989_ = lean_nat_dec_le(v___x_5984_, v___x_5984_);
if (v___x_5989_ == 0)
{
if (v___x_5986_ == 0)
{
lean_object* v___x_5990_; lean_object* v___x_5991_; 
lean_dec_ref(v_errors_5982_);
lean_dec(v___f_5974_);
lean_dec_ref(v_inst_5973_);
v___x_5990_ = lean_apply_2(v_toPure_5971_, lean_box(0), v___x_5985_);
v___x_5991_ = lean_apply_4(v_toBind_5972_, lean_box(0), lean_box(0), v___x_5990_, v___f_5983_);
return v___x_5991_;
}
else
{
size_t v___x_5992_; size_t v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; 
lean_dec(v_toPure_5971_);
v___x_5992_ = ((size_t)0ULL);
v___x_5993_ = lean_usize_of_nat(v___x_5984_);
v___x_5994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5973_, v___f_5974_, v_errors_5982_, v___x_5992_, v___x_5993_, v___x_5985_);
v___x_5995_ = lean_apply_4(v_toBind_5972_, lean_box(0), lean_box(0), v___x_5994_, v___f_5983_);
return v___x_5995_;
}
}
else
{
size_t v___x_5996_; size_t v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; 
lean_dec(v_toPure_5971_);
v___x_5996_ = ((size_t)0ULL);
v___x_5997_ = lean_usize_of_nat(v___x_5984_);
v___x_5998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5973_, v___f_5974_, v_errors_5982_, v___x_5996_, v___x_5997_, v___x_5985_);
v___x_5999_ = lean_apply_4(v_toBind_5972_, lean_box(0), lean_box(0), v___x_5998_, v___f_5983_);
return v___x_5999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(lean_object* v_inst_6002_, lean_object* v_inst_6003_, lean_object* v_inst_6004_, lean_object* v_inst_6005_, lean_object* v_inst_6006_, lean_object* v_cctx_6007_, lean_object* v_ngen_6008_, lean_object* v_env_6009_, lean_object* v_act_6010_, lean_object* v_constantsPerTask_6011_){
_start:
{
lean_object* v___x_6012_; lean_object* v_moduleData_6013_; lean_object* v_toApplicative_6014_; lean_object* v_toBind_6015_; lean_object* v_n_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v_toPure_6020_; lean_object* v___f_6021_; lean_object* v___x_6022_; lean_object* v___f_6023_; lean_object* v___x_6024_; 
v___x_6012_ = l_Lean_Environment_header(v_env_6009_);
v_moduleData_6013_ = lean_ctor_get(v___x_6012_, 6);
lean_inc_ref(v_moduleData_6013_);
lean_dec_ref(v___x_6012_);
v_toApplicative_6014_ = lean_ctor_get(v_inst_6002_, 0);
v_toBind_6015_ = lean_ctor_get(v_inst_6002_, 1);
lean_inc_n(v_toBind_6015_, 2);
v_n_6016_ = lean_array_get_size(v_moduleData_6013_);
lean_dec_ref(v_moduleData_6013_);
v___x_6017_ = lean_unsigned_to_nat(0u);
v___x_6018_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
lean_inc_ref_n(v_inst_6002_, 2);
v___x_6019_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___redArg(v_inst_6002_, v_inst_6006_, v_cctx_6007_, v_env_6009_, v_act_6010_, v_constantsPerTask_6011_, v_n_6016_, v_ngen_6008_, v___x_6018_, v___x_6017_, v___x_6017_, v___x_6017_);
v_toPure_6020_ = lean_ctor_get(v_toApplicative_6014_, 1);
lean_inc(v_toPure_6020_);
v___f_6021_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__0), 6, 4);
lean_closure_set(v___f_6021_, 0, v_inst_6002_);
lean_closure_set(v___f_6021_, 1, v_inst_6003_);
lean_closure_set(v___f_6021_, 2, v_inst_6004_);
lean_closure_set(v___f_6021_, 3, v_inst_6005_);
v___x_6022_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_InitResults_instAppend___closed__0));
v___f_6023_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___lam__2), 7, 6);
lean_closure_set(v___f_6023_, 0, v___x_6017_);
lean_closure_set(v___f_6023_, 1, v___x_6022_);
lean_closure_set(v___f_6023_, 2, v_toPure_6020_);
lean_closure_set(v___f_6023_, 3, v_toBind_6015_);
lean_closure_set(v___f_6023_, 4, v_inst_6002_);
lean_closure_set(v___f_6023_, 5, v___f_6021_);
v___x_6024_ = lean_apply_4(v_toBind_6015_, lean_box(0), lean_box(0), v___x_6019_, v___f_6023_);
return v___x_6024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree(lean_object* v_m_6025_, lean_object* v_00_u03b1_6026_, lean_object* v_inst_6027_, lean_object* v_inst_6028_, lean_object* v_inst_6029_, lean_object* v_inst_6030_, lean_object* v_inst_6031_, lean_object* v_cctx_6032_, lean_object* v_ngen_6033_, lean_object* v_env_6034_, lean_object* v_act_6035_, lean_object* v_constantsPerTask_6036_){
_start:
{
lean_object* v___x_6037_; 
v___x_6037_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg(v_inst_6027_, v_inst_6028_, v_inst_6029_, v_inst_6030_, v_inst_6031_, v_cctx_6032_, v_ngen_6033_, v_env_6034_, v_act_6035_, v_constantsPerTask_6036_);
return v___x_6037_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0(void){
_start:
{
lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6038_ = lean_box(0);
v___x_6039_ = lean_unsigned_to_nat(16u);
v___x_6040_ = lean_mk_array(v___x_6039_, v___x_6038_);
return v___x_6040_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1(void){
_start:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; 
v___x_6041_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__0);
v___x_6042_ = lean_unsigned_to_nat(0u);
v___x_6043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6042_);
lean_ctor_set(v___x_6043_, 1, v___x_6041_);
return v___x_6043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createTreeCtx(lean_object* v_ctx_6044_){
_start:
{
lean_object* v_fileName_6045_; lean_object* v_fileMap_6046_; lean_object* v_options_6047_; lean_object* v_maxRecDepth_6048_; lean_object* v_ref_6049_; lean_object* v___x_6051_; uint8_t v_isShared_6052_; uint8_t v_isSharedCheck_6064_; 
v_fileName_6045_ = lean_ctor_get(v_ctx_6044_, 0);
v_fileMap_6046_ = lean_ctor_get(v_ctx_6044_, 1);
v_options_6047_ = lean_ctor_get(v_ctx_6044_, 2);
v_maxRecDepth_6048_ = lean_ctor_get(v_ctx_6044_, 4);
v_ref_6049_ = lean_ctor_get(v_ctx_6044_, 5);
v_isSharedCheck_6064_ = !lean_is_exclusive(v_ctx_6044_);
if (v_isSharedCheck_6064_ == 0)
{
lean_object* v_unused_6065_; lean_object* v_unused_6066_; lean_object* v_unused_6067_; lean_object* v_unused_6068_; lean_object* v_unused_6069_; lean_object* v_unused_6070_; lean_object* v_unused_6071_; lean_object* v_unused_6072_; lean_object* v_unused_6073_; 
v_unused_6065_ = lean_ctor_get(v_ctx_6044_, 13);
lean_dec(v_unused_6065_);
v_unused_6066_ = lean_ctor_get(v_ctx_6044_, 12);
lean_dec(v_unused_6066_);
v_unused_6067_ = lean_ctor_get(v_ctx_6044_, 11);
lean_dec(v_unused_6067_);
v_unused_6068_ = lean_ctor_get(v_ctx_6044_, 10);
lean_dec(v_unused_6068_);
v_unused_6069_ = lean_ctor_get(v_ctx_6044_, 9);
lean_dec(v_unused_6069_);
v_unused_6070_ = lean_ctor_get(v_ctx_6044_, 8);
lean_dec(v_unused_6070_);
v_unused_6071_ = lean_ctor_get(v_ctx_6044_, 7);
lean_dec(v_unused_6071_);
v_unused_6072_ = lean_ctor_get(v_ctx_6044_, 6);
lean_dec(v_unused_6072_);
v_unused_6073_ = lean_ctor_get(v_ctx_6044_, 3);
lean_dec(v_unused_6073_);
v___x_6051_ = v_ctx_6044_;
v_isShared_6052_ = v_isSharedCheck_6064_;
goto v_resetjp_6050_;
}
else
{
lean_inc(v_ref_6049_);
lean_inc(v_maxRecDepth_6048_);
lean_inc(v_options_6047_);
lean_inc(v_fileMap_6046_);
lean_inc(v_fileName_6045_);
lean_dec(v_ctx_6044_);
v___x_6051_ = lean_box(0);
v_isShared_6052_ = v_isSharedCheck_6064_;
goto v_resetjp_6050_;
}
v_resetjp_6050_:
{
lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; uint8_t v___x_6057_; lean_object* v___x_6058_; uint8_t v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6062_; 
v___x_6053_ = lean_unsigned_to_nat(0u);
v___x_6054_ = lean_box(0);
v___x_6055_ = lean_box(0);
v___x_6056_ = l_Lean_firstFrontendMacroScope;
v___x_6057_ = l_Lean_getDiag(v_options_6047_);
v___x_6058_ = lean_box(0);
v___x_6059_ = 0;
v___x_6060_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1, &l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createTreeCtx___closed__1);
if (v_isShared_6052_ == 0)
{
lean_ctor_set(v___x_6051_, 13, v___x_6060_);
lean_ctor_set(v___x_6051_, 12, v___x_6058_);
lean_ctor_set(v___x_6051_, 11, v___x_6056_);
lean_ctor_set(v___x_6051_, 10, v___x_6054_);
lean_ctor_set(v___x_6051_, 9, v___x_6053_);
lean_ctor_set(v___x_6051_, 8, v___x_6053_);
lean_ctor_set(v___x_6051_, 7, v___x_6055_);
lean_ctor_set(v___x_6051_, 6, v___x_6054_);
lean_ctor_set(v___x_6051_, 3, v___x_6053_);
v___x_6062_ = v___x_6051_;
goto v_reusejp_6061_;
}
else
{
lean_object* v_reuseFailAlloc_6063_; 
v_reuseFailAlloc_6063_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_6063_, 0, v_fileName_6045_);
lean_ctor_set(v_reuseFailAlloc_6063_, 1, v_fileMap_6046_);
lean_ctor_set(v_reuseFailAlloc_6063_, 2, v_options_6047_);
lean_ctor_set(v_reuseFailAlloc_6063_, 3, v___x_6053_);
lean_ctor_set(v_reuseFailAlloc_6063_, 4, v_maxRecDepth_6048_);
lean_ctor_set(v_reuseFailAlloc_6063_, 5, v_ref_6049_);
lean_ctor_set(v_reuseFailAlloc_6063_, 6, v___x_6054_);
lean_ctor_set(v_reuseFailAlloc_6063_, 7, v___x_6055_);
lean_ctor_set(v_reuseFailAlloc_6063_, 8, v___x_6053_);
lean_ctor_set(v_reuseFailAlloc_6063_, 9, v___x_6053_);
lean_ctor_set(v_reuseFailAlloc_6063_, 10, v___x_6054_);
lean_ctor_set(v_reuseFailAlloc_6063_, 11, v___x_6056_);
lean_ctor_set(v_reuseFailAlloc_6063_, 12, v___x_6058_);
lean_ctor_set(v_reuseFailAlloc_6063_, 13, v___x_6060_);
v___x_6062_ = v_reuseFailAlloc_6063_;
goto v_reusejp_6061_;
}
v_reusejp_6061_:
{
lean_ctor_set_uint8(v___x_6062_, sizeof(void*)*14, v___x_6057_);
lean_ctor_set_uint8(v___x_6062_, sizeof(void*)*14 + 1, v___x_6059_);
return v___x_6062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(lean_object* v_category_6074_, lean_object* v_opts_6075_, lean_object* v_act_6076_, lean_object* v_decl_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_){
_start:
{
lean_object* v___x_6083_; lean_object* v___x_6084_; 
lean_inc(v___y_6081_);
lean_inc_ref(v___y_6080_);
lean_inc(v___y_6079_);
lean_inc_ref(v___y_6078_);
v___x_6083_ = lean_apply_4(v_act_6076_, v___y_6078_, v___y_6079_, v___y_6080_, v___y_6081_);
v___x_6084_ = l_Lean_profileitIOUnsafe___redArg(v_category_6074_, v_opts_6075_, v___x_6083_, v_decl_6077_);
return v___x_6084_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg___boxed(lean_object* v_category_6085_, lean_object* v_opts_6086_, lean_object* v_act_6087_, lean_object* v_decl_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_){
_start:
{
lean_object* v_res_6094_; 
v_res_6094_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6085_, v_opts_6086_, v_act_6087_, v_decl_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
lean_dec_ref(v_opts_6086_);
lean_dec_ref(v_category_6085_);
return v_res_6094_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(lean_object* v_00_u03b1_6095_, lean_object* v_category_6096_, lean_object* v_opts_6097_, lean_object* v_act_6098_, lean_object* v_decl_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_){
_start:
{
lean_object* v___x_6105_; 
v___x_6105_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v_category_6096_, v_opts_6097_, v_act_6098_, v_decl_6099_, v___y_6100_, v___y_6101_, v___y_6102_, v___y_6103_);
return v___x_6105_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___boxed(lean_object* v_00_u03b1_6106_, lean_object* v_category_6107_, lean_object* v_opts_6108_, lean_object* v_act_6109_, lean_object* v_decl_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_){
_start:
{
lean_object* v_res_6116_; 
v_res_6116_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1(v_00_u03b1_6106_, v_category_6107_, v_opts_6108_, v_act_6109_, v_decl_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___y_6111_);
lean_dec_ref(v_opts_6108_);
lean_dec_ref(v_category_6107_);
return v_res_6116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(lean_object* v_cctx_6117_, lean_object* v_env_6118_, lean_object* v_act_6119_, lean_object* v_constantsPerTask_6120_, lean_object* v_n_6121_, lean_object* v_ngen_6122_, lean_object* v_tasks_6123_, lean_object* v_start_6124_, lean_object* v_cnt_6125_, lean_object* v_idx_6126_){
_start:
{
lean_object* v___x_6128_; lean_object* v_moduleData_6129_; lean_object* v___x_6130_; uint8_t v___x_6131_; 
v___x_6128_ = l_Lean_Environment_header(v_env_6118_);
v_moduleData_6129_ = lean_ctor_get(v___x_6128_, 6);
lean_inc_ref(v_moduleData_6129_);
lean_dec_ref(v___x_6128_);
v___x_6130_ = lean_array_get_size(v_moduleData_6129_);
v___x_6131_ = lean_nat_dec_lt(v_idx_6126_, v___x_6130_);
if (v___x_6131_ == 0)
{
uint8_t v___x_6132_; 
lean_dec_ref(v_moduleData_6129_);
lean_dec(v_idx_6126_);
lean_dec(v_cnt_6125_);
v___x_6132_ = lean_nat_dec_lt(v_start_6124_, v_n_6121_);
if (v___x_6132_ == 0)
{
lean_object* v___x_6133_; 
lean_dec(v_start_6124_);
lean_dec_ref(v_ngen_6122_);
lean_dec(v_n_6121_);
lean_dec_ref(v_act_6119_);
lean_dec_ref(v_env_6118_);
lean_dec_ref(v_cctx_6117_);
v___x_6133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6133_, 0, v_tasks_6123_);
return v___x_6133_;
}
else
{
lean_object* v_namePrefix_6134_; lean_object* v_idx_6135_; lean_object* v___x_6137_; uint8_t v_isShared_6138_; uint8_t v_isSharedCheck_6149_; 
v_namePrefix_6134_ = lean_ctor_get(v_ngen_6122_, 0);
v_idx_6135_ = lean_ctor_get(v_ngen_6122_, 1);
v_isSharedCheck_6149_ = !lean_is_exclusive(v_ngen_6122_);
if (v_isSharedCheck_6149_ == 0)
{
v___x_6137_ = v_ngen_6122_;
v_isShared_6138_ = v_isSharedCheck_6149_;
goto v_resetjp_6136_;
}
else
{
lean_inc(v_idx_6135_);
lean_inc(v_namePrefix_6134_);
lean_dec(v_ngen_6122_);
v___x_6137_ = lean_box(0);
v_isShared_6138_ = v_isSharedCheck_6149_;
goto v_resetjp_6136_;
}
v_resetjp_6136_:
{
lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6142_; 
v___x_6139_ = l_Lean_Name_num___override(v_namePrefix_6134_, v_idx_6135_);
v___x_6140_ = lean_unsigned_to_nat(1u);
if (v_isShared_6138_ == 0)
{
lean_ctor_set(v___x_6137_, 1, v___x_6140_);
lean_ctor_set(v___x_6137_, 0, v___x_6139_);
v___x_6142_ = v___x_6137_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6148_; 
v_reuseFailAlloc_6148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6148_, 0, v___x_6139_);
lean_ctor_set(v_reuseFailAlloc_6148_, 1, v___x_6140_);
v___x_6142_ = v_reuseFailAlloc_6148_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; 
v___x_6143_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6143_, 0, lean_box(0));
lean_closure_set(v___x_6143_, 1, v_cctx_6117_);
lean_closure_set(v___x_6143_, 2, v___x_6142_);
lean_closure_set(v___x_6143_, 3, v_env_6118_);
lean_closure_set(v___x_6143_, 4, v_act_6119_);
lean_closure_set(v___x_6143_, 5, v_start_6124_);
lean_closure_set(v___x_6143_, 6, v_n_6121_);
v___x_6144_ = lean_unsigned_to_nat(0u);
v___x_6145_ = lean_io_as_task(v___x_6143_, v___x_6144_);
v___x_6146_ = lean_array_push(v_tasks_6123_, v___x_6145_);
v___x_6147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6146_);
return v___x_6147_;
}
}
}
}
else
{
lean_object* v_mdata_6150_; lean_object* v_constants_6151_; lean_object* v___x_6152_; lean_object* v_cnt_6153_; uint8_t v___x_6154_; 
v_mdata_6150_ = lean_array_fget(v_moduleData_6129_, v_idx_6126_);
lean_dec_ref(v_moduleData_6129_);
v_constants_6151_ = lean_ctor_get(v_mdata_6150_, 2);
lean_inc_ref(v_constants_6151_);
lean_dec(v_mdata_6150_);
v___x_6152_ = lean_array_get_size(v_constants_6151_);
lean_dec_ref(v_constants_6151_);
v_cnt_6153_ = lean_nat_add(v_cnt_6125_, v___x_6152_);
lean_dec(v_cnt_6125_);
v___x_6154_ = lean_nat_dec_lt(v_constantsPerTask_6120_, v_cnt_6153_);
if (v___x_6154_ == 0)
{
lean_object* v___x_6155_; lean_object* v___x_6156_; 
v___x_6155_ = lean_unsigned_to_nat(1u);
v___x_6156_ = lean_nat_add(v_idx_6126_, v___x_6155_);
lean_dec(v_idx_6126_);
v_cnt_6125_ = v_cnt_6153_;
v_idx_6126_ = v___x_6156_;
goto _start;
}
else
{
lean_object* v_namePrefix_6158_; lean_object* v_idx_6159_; lean_object* v___x_6161_; uint8_t v_isShared_6162_; uint8_t v_isSharedCheck_6176_; 
lean_dec(v_cnt_6153_);
v_namePrefix_6158_ = lean_ctor_get(v_ngen_6122_, 0);
v_idx_6159_ = lean_ctor_get(v_ngen_6122_, 1);
v_isSharedCheck_6176_ = !lean_is_exclusive(v_ngen_6122_);
if (v_isSharedCheck_6176_ == 0)
{
v___x_6161_ = v_ngen_6122_;
v_isShared_6162_ = v_isSharedCheck_6176_;
goto v_resetjp_6160_;
}
else
{
lean_inc(v_idx_6159_);
lean_inc(v_namePrefix_6158_);
lean_dec(v_ngen_6122_);
v___x_6161_ = lean_box(0);
v_isShared_6162_ = v_isSharedCheck_6176_;
goto v_resetjp_6160_;
}
v_resetjp_6160_:
{
lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6166_; 
lean_inc(v_idx_6159_);
lean_inc(v_namePrefix_6158_);
v___x_6163_ = l_Lean_Name_num___override(v_namePrefix_6158_, v_idx_6159_);
v___x_6164_ = lean_unsigned_to_nat(1u);
if (v_isShared_6162_ == 0)
{
lean_ctor_set(v___x_6161_, 1, v___x_6164_);
lean_ctor_set(v___x_6161_, 0, v___x_6163_);
v___x_6166_ = v___x_6161_;
goto v_reusejp_6165_;
}
else
{
lean_object* v_reuseFailAlloc_6175_; 
v_reuseFailAlloc_6175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6175_, 0, v___x_6163_);
lean_ctor_set(v_reuseFailAlloc_6175_, 1, v___x_6164_);
v___x_6166_ = v_reuseFailAlloc_6175_;
goto v_reusejp_6165_;
}
v_reusejp_6165_:
{
lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6167_ = lean_nat_add(v_idx_6126_, v___x_6164_);
lean_dec(v_idx_6126_);
lean_inc_n(v___x_6167_, 2);
lean_inc_ref(v_act_6119_);
lean_inc_ref(v_env_6118_);
lean_inc_ref(v_cctx_6117_);
v___x_6168_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createImportedEnvironmentSeq___boxed), 8, 7);
lean_closure_set(v___x_6168_, 0, lean_box(0));
lean_closure_set(v___x_6168_, 1, v_cctx_6117_);
lean_closure_set(v___x_6168_, 2, v___x_6166_);
lean_closure_set(v___x_6168_, 3, v_env_6118_);
lean_closure_set(v___x_6168_, 4, v_act_6119_);
lean_closure_set(v___x_6168_, 5, v_start_6124_);
lean_closure_set(v___x_6168_, 6, v___x_6167_);
v___x_6169_ = lean_unsigned_to_nat(0u);
v___x_6170_ = lean_io_as_task(v___x_6168_, v___x_6169_);
v___x_6171_ = lean_nat_add(v_idx_6159_, v___x_6164_);
lean_dec(v_idx_6159_);
v___x_6172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6172_, 0, v_namePrefix_6158_);
lean_ctor_set(v___x_6172_, 1, v___x_6171_);
v___x_6173_ = lean_array_push(v_tasks_6123_, v___x_6170_);
v_ngen_6122_ = v___x_6172_;
v_tasks_6123_ = v___x_6173_;
v_start_6124_ = v___x_6167_;
v_cnt_6125_ = v___x_6169_;
v_idx_6126_ = v___x_6167_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg___boxed(lean_object* v_cctx_6177_, lean_object* v_env_6178_, lean_object* v_act_6179_, lean_object* v_constantsPerTask_6180_, lean_object* v_n_6181_, lean_object* v_ngen_6182_, lean_object* v_tasks_6183_, lean_object* v_start_6184_, lean_object* v_cnt_6185_, lean_object* v_idx_6186_, lean_object* v___y_6187_){
_start:
{
lean_object* v_res_6188_; 
v_res_6188_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6177_, v_env_6178_, v_act_6179_, v_constantsPerTask_6180_, v_n_6181_, v_ngen_6182_, v_tasks_6183_, v_start_6184_, v_cnt_6185_, v_idx_6186_);
lean_dec(v_constantsPerTask_6180_);
return v_res_6188_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(uint8_t v___y_6197_, uint8_t v_suppressElabErrors_6198_, lean_object* v_x_6199_){
_start:
{
if (lean_obj_tag(v_x_6199_) == 1)
{
lean_object* v_pre_6200_; 
v_pre_6200_ = lean_ctor_get(v_x_6199_, 0);
switch(lean_obj_tag(v_pre_6200_))
{
case 1:
{
lean_object* v_pre_6201_; 
v_pre_6201_ = lean_ctor_get(v_pre_6200_, 0);
switch(lean_obj_tag(v_pre_6201_))
{
case 0:
{
lean_object* v_str_6202_; lean_object* v_str_6203_; lean_object* v___x_6204_; uint8_t v___x_6205_; 
v_str_6202_ = lean_ctor_get(v_x_6199_, 1);
v_str_6203_ = lean_ctor_get(v_pre_6200_, 1);
v___x_6204_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__0));
v___x_6205_ = lean_string_dec_eq(v_str_6203_, v___x_6204_);
if (v___x_6205_ == 0)
{
lean_object* v___x_6206_; uint8_t v___x_6207_; 
v___x_6206_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__1));
v___x_6207_ = lean_string_dec_eq(v_str_6203_, v___x_6206_);
if (v___x_6207_ == 0)
{
return v___y_6197_;
}
else
{
lean_object* v___x_6208_; uint8_t v___x_6209_; 
v___x_6208_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__2));
v___x_6209_ = lean_string_dec_eq(v_str_6202_, v___x_6208_);
if (v___x_6209_ == 0)
{
return v___y_6197_;
}
else
{
return v_suppressElabErrors_6198_;
}
}
}
else
{
lean_object* v___x_6210_; uint8_t v___x_6211_; 
v___x_6210_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__3));
v___x_6211_ = lean_string_dec_eq(v_str_6202_, v___x_6210_);
if (v___x_6211_ == 0)
{
return v___y_6197_;
}
else
{
return v_suppressElabErrors_6198_;
}
}
}
case 1:
{
lean_object* v_pre_6212_; 
v_pre_6212_ = lean_ctor_get(v_pre_6201_, 0);
if (lean_obj_tag(v_pre_6212_) == 0)
{
lean_object* v_str_6213_; lean_object* v_str_6214_; lean_object* v_str_6215_; lean_object* v___x_6216_; uint8_t v___x_6217_; 
v_str_6213_ = lean_ctor_get(v_x_6199_, 1);
v_str_6214_ = lean_ctor_get(v_pre_6200_, 1);
v_str_6215_ = lean_ctor_get(v_pre_6201_, 1);
v___x_6216_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__4));
v___x_6217_ = lean_string_dec_eq(v_str_6215_, v___x_6216_);
if (v___x_6217_ == 0)
{
return v___y_6197_;
}
else
{
lean_object* v___x_6218_; uint8_t v___x_6219_; 
v___x_6218_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__5));
v___x_6219_ = lean_string_dec_eq(v_str_6214_, v___x_6218_);
if (v___x_6219_ == 0)
{
return v___y_6197_;
}
else
{
lean_object* v___x_6220_; uint8_t v___x_6221_; 
v___x_6220_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__6));
v___x_6221_ = lean_string_dec_eq(v_str_6213_, v___x_6220_);
if (v___x_6221_ == 0)
{
return v___y_6197_;
}
else
{
return v_suppressElabErrors_6198_;
}
}
}
}
else
{
return v___y_6197_;
}
}
default: 
{
return v___y_6197_;
}
}
}
case 0:
{
lean_object* v_str_6222_; lean_object* v___x_6223_; uint8_t v___x_6224_; 
v_str_6222_ = lean_ctor_get(v_x_6199_, 1);
v___x_6223_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___closed__7));
v___x_6224_ = lean_string_dec_eq(v_str_6222_, v___x_6223_);
if (v___x_6224_ == 0)
{
return v___y_6197_;
}
else
{
return v_suppressElabErrors_6198_;
}
}
default: 
{
return v___y_6197_;
}
}
}
else
{
return v___y_6197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v___y_6225_, lean_object* v_suppressElabErrors_6226_, lean_object* v_x_6227_){
_start:
{
uint8_t v___y_8412__boxed_6228_; uint8_t v_suppressElabErrors_boxed_6229_; uint8_t v_res_6230_; lean_object* v_r_6231_; 
v___y_8412__boxed_6228_ = lean_unbox(v___y_6225_);
v_suppressElabErrors_boxed_6229_ = lean_unbox(v_suppressElabErrors_6226_);
v_res_6230_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0(v___y_8412__boxed_6228_, v_suppressElabErrors_boxed_6229_, v_x_6227_);
lean_dec(v_x_6227_);
v_r_6231_ = lean_box(v_res_6230_);
return v_r_6231_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_ref_6233_, lean_object* v_msgData_6234_, uint8_t v_severity_6235_, uint8_t v_isSilent_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_){
_start:
{
lean_object* v___y_6243_; lean_object* v___y_6244_; uint8_t v___y_6245_; lean_object* v___y_6246_; uint8_t v___y_6247_; lean_object* v___y_6248_; lean_object* v___y_6249_; lean_object* v___y_6250_; lean_object* v___y_6251_; lean_object* v___y_6279_; lean_object* v___y_6280_; lean_object* v___y_6281_; uint8_t v___y_6282_; lean_object* v___y_6283_; uint8_t v___y_6284_; uint8_t v___y_6285_; lean_object* v___y_6286_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6306_; uint8_t v___y_6307_; uint8_t v___y_6308_; uint8_t v___y_6309_; lean_object* v___y_6310_; lean_object* v___y_6311_; lean_object* v___y_6315_; lean_object* v___y_6316_; lean_object* v___y_6317_; uint8_t v___y_6318_; lean_object* v___y_6319_; uint8_t v___y_6320_; uint8_t v___y_6321_; uint8_t v___x_6326_; lean_object* v___y_6328_; lean_object* v___y_6329_; lean_object* v___y_6330_; lean_object* v___y_6331_; uint8_t v___y_6332_; uint8_t v___y_6333_; uint8_t v___y_6334_; uint8_t v___y_6336_; uint8_t v___x_6351_; 
v___x_6326_ = 2;
v___x_6351_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6235_, v___x_6326_);
if (v___x_6351_ == 0)
{
v___y_6336_ = v___x_6351_;
goto v___jp_6335_;
}
else
{
uint8_t v___x_6352_; 
lean_inc_ref(v_msgData_6234_);
v___x_6352_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6234_);
v___y_6336_ = v___x_6352_;
goto v___jp_6335_;
}
v___jp_6242_:
{
lean_object* v___x_6252_; lean_object* v_currNamespace_6253_; lean_object* v_openDecls_6254_; lean_object* v_env_6255_; lean_object* v_nextMacroScope_6256_; lean_object* v_ngen_6257_; lean_object* v_auxDeclNGen_6258_; lean_object* v_traceState_6259_; lean_object* v_cache_6260_; lean_object* v_messages_6261_; lean_object* v_infoState_6262_; lean_object* v_snapshotTasks_6263_; lean_object* v___x_6265_; uint8_t v_isShared_6266_; uint8_t v_isSharedCheck_6277_; 
v___x_6252_ = lean_st_ref_take(v___y_6251_);
v_currNamespace_6253_ = lean_ctor_get(v___y_6250_, 6);
v_openDecls_6254_ = lean_ctor_get(v___y_6250_, 7);
v_env_6255_ = lean_ctor_get(v___x_6252_, 0);
v_nextMacroScope_6256_ = lean_ctor_get(v___x_6252_, 1);
v_ngen_6257_ = lean_ctor_get(v___x_6252_, 2);
v_auxDeclNGen_6258_ = lean_ctor_get(v___x_6252_, 3);
v_traceState_6259_ = lean_ctor_get(v___x_6252_, 4);
v_cache_6260_ = lean_ctor_get(v___x_6252_, 5);
v_messages_6261_ = lean_ctor_get(v___x_6252_, 6);
v_infoState_6262_ = lean_ctor_get(v___x_6252_, 7);
v_snapshotTasks_6263_ = lean_ctor_get(v___x_6252_, 8);
v_isSharedCheck_6277_ = !lean_is_exclusive(v___x_6252_);
if (v_isSharedCheck_6277_ == 0)
{
v___x_6265_ = v___x_6252_;
v_isShared_6266_ = v_isSharedCheck_6277_;
goto v_resetjp_6264_;
}
else
{
lean_inc(v_snapshotTasks_6263_);
lean_inc(v_infoState_6262_);
lean_inc(v_messages_6261_);
lean_inc(v_cache_6260_);
lean_inc(v_traceState_6259_);
lean_inc(v_auxDeclNGen_6258_);
lean_inc(v_ngen_6257_);
lean_inc(v_nextMacroScope_6256_);
lean_inc(v_env_6255_);
lean_dec(v___x_6252_);
v___x_6265_ = lean_box(0);
v_isShared_6266_ = v_isSharedCheck_6277_;
goto v_resetjp_6264_;
}
v_resetjp_6264_:
{
lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6272_; 
lean_inc(v_openDecls_6254_);
lean_inc(v_currNamespace_6253_);
v___x_6267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6267_, 0, v_currNamespace_6253_);
lean_ctor_set(v___x_6267_, 1, v_openDecls_6254_);
v___x_6268_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6268_, 0, v___x_6267_);
lean_ctor_set(v___x_6268_, 1, v___y_6248_);
lean_inc_ref(v___y_6246_);
lean_inc_ref(v___y_6243_);
v___x_6269_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6269_, 0, v___y_6243_);
lean_ctor_set(v___x_6269_, 1, v___y_6244_);
lean_ctor_set(v___x_6269_, 2, v___y_6249_);
lean_ctor_set(v___x_6269_, 3, v___y_6246_);
lean_ctor_set(v___x_6269_, 4, v___x_6268_);
lean_ctor_set_uint8(v___x_6269_, sizeof(void*)*5, v___y_6245_);
lean_ctor_set_uint8(v___x_6269_, sizeof(void*)*5 + 1, v___y_6247_);
lean_ctor_set_uint8(v___x_6269_, sizeof(void*)*5 + 2, v_isSilent_6236_);
v___x_6270_ = l_Lean_MessageLog_add(v___x_6269_, v_messages_6261_);
if (v_isShared_6266_ == 0)
{
lean_ctor_set(v___x_6265_, 6, v___x_6270_);
v___x_6272_ = v___x_6265_;
goto v_reusejp_6271_;
}
else
{
lean_object* v_reuseFailAlloc_6276_; 
v_reuseFailAlloc_6276_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_env_6255_);
lean_ctor_set(v_reuseFailAlloc_6276_, 1, v_nextMacroScope_6256_);
lean_ctor_set(v_reuseFailAlloc_6276_, 2, v_ngen_6257_);
lean_ctor_set(v_reuseFailAlloc_6276_, 3, v_auxDeclNGen_6258_);
lean_ctor_set(v_reuseFailAlloc_6276_, 4, v_traceState_6259_);
lean_ctor_set(v_reuseFailAlloc_6276_, 5, v_cache_6260_);
lean_ctor_set(v_reuseFailAlloc_6276_, 6, v___x_6270_);
lean_ctor_set(v_reuseFailAlloc_6276_, 7, v_infoState_6262_);
lean_ctor_set(v_reuseFailAlloc_6276_, 8, v_snapshotTasks_6263_);
v___x_6272_ = v_reuseFailAlloc_6276_;
goto v_reusejp_6271_;
}
v_reusejp_6271_:
{
lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; 
v___x_6273_ = lean_st_ref_set(v___y_6251_, v___x_6272_);
v___x_6274_ = lean_box(0);
v___x_6275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6275_, 0, v___x_6274_);
return v___x_6275_;
}
}
}
v___jp_6278_:
{
lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v_a_6289_; lean_object* v___x_6291_; uint8_t v_isShared_6292_; uint8_t v_isSharedCheck_6302_; 
v___x_6287_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6234_);
v___x_6288_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LazyDiscrTree_pushArgs_spec__0_spec__0(v___x_6287_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_);
v_a_6289_ = lean_ctor_get(v___x_6288_, 0);
v_isSharedCheck_6302_ = !lean_is_exclusive(v___x_6288_);
if (v_isSharedCheck_6302_ == 0)
{
v___x_6291_ = v___x_6288_;
v_isShared_6292_ = v_isSharedCheck_6302_;
goto v_resetjp_6290_;
}
else
{
lean_inc(v_a_6289_);
lean_dec(v___x_6288_);
v___x_6291_ = lean_box(0);
v_isShared_6292_ = v_isSharedCheck_6302_;
goto v_resetjp_6290_;
}
v_resetjp_6290_:
{
lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; 
lean_inc_ref_n(v___y_6283_, 2);
v___x_6293_ = l_Lean_FileMap_toPosition(v___y_6283_, v___y_6281_);
lean_dec(v___y_6281_);
v___x_6294_ = l_Lean_FileMap_toPosition(v___y_6283_, v___y_6286_);
lean_dec(v___y_6286_);
v___x_6295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6295_, 0, v___x_6294_);
v___x_6296_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6284_ == 0)
{
lean_del_object(v___x_6291_);
lean_dec_ref(v___y_6279_);
v___y_6243_ = v___y_6280_;
v___y_6244_ = v___x_6293_;
v___y_6245_ = v___y_6282_;
v___y_6246_ = v___x_6296_;
v___y_6247_ = v___y_6285_;
v___y_6248_ = v_a_6289_;
v___y_6249_ = v___x_6295_;
v___y_6250_ = v___y_6239_;
v___y_6251_ = v___y_6240_;
goto v___jp_6242_;
}
else
{
uint8_t v___x_6297_; 
lean_inc(v_a_6289_);
v___x_6297_ = l_Lean_MessageData_hasTag(v___y_6279_, v_a_6289_);
if (v___x_6297_ == 0)
{
lean_object* v___x_6298_; lean_object* v___x_6300_; 
lean_dec_ref(v___x_6295_);
lean_dec_ref(v___x_6293_);
lean_dec(v_a_6289_);
v___x_6298_ = lean_box(0);
if (v_isShared_6292_ == 0)
{
lean_ctor_set(v___x_6291_, 0, v___x_6298_);
v___x_6300_ = v___x_6291_;
goto v_reusejp_6299_;
}
else
{
lean_object* v_reuseFailAlloc_6301_; 
v_reuseFailAlloc_6301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6301_, 0, v___x_6298_);
v___x_6300_ = v_reuseFailAlloc_6301_;
goto v_reusejp_6299_;
}
v_reusejp_6299_:
{
return v___x_6300_;
}
}
else
{
lean_del_object(v___x_6291_);
v___y_6243_ = v___y_6280_;
v___y_6244_ = v___x_6293_;
v___y_6245_ = v___y_6282_;
v___y_6246_ = v___x_6296_;
v___y_6247_ = v___y_6285_;
v___y_6248_ = v_a_6289_;
v___y_6249_ = v___x_6295_;
v___y_6250_ = v___y_6239_;
v___y_6251_ = v___y_6240_;
goto v___jp_6242_;
}
}
}
}
v___jp_6303_:
{
lean_object* v___x_6312_; 
v___x_6312_ = l_Lean_Syntax_getTailPos_x3f(v___y_6310_, v___y_6307_);
lean_dec(v___y_6310_);
if (lean_obj_tag(v___x_6312_) == 0)
{
lean_inc(v___y_6311_);
v___y_6279_ = v___y_6304_;
v___y_6280_ = v___y_6305_;
v___y_6281_ = v___y_6311_;
v___y_6282_ = v___y_6307_;
v___y_6283_ = v___y_6306_;
v___y_6284_ = v___y_6308_;
v___y_6285_ = v___y_6309_;
v___y_6286_ = v___y_6311_;
goto v___jp_6278_;
}
else
{
lean_object* v_val_6313_; 
v_val_6313_ = lean_ctor_get(v___x_6312_, 0);
lean_inc(v_val_6313_);
lean_dec_ref(v___x_6312_);
v___y_6279_ = v___y_6304_;
v___y_6280_ = v___y_6305_;
v___y_6281_ = v___y_6311_;
v___y_6282_ = v___y_6307_;
v___y_6283_ = v___y_6306_;
v___y_6284_ = v___y_6308_;
v___y_6285_ = v___y_6309_;
v___y_6286_ = v_val_6313_;
goto v___jp_6278_;
}
}
v___jp_6314_:
{
lean_object* v_ref_6322_; lean_object* v___x_6323_; 
v_ref_6322_ = l_Lean_replaceRef(v_ref_6233_, v___y_6317_);
v___x_6323_ = l_Lean_Syntax_getPos_x3f(v_ref_6322_, v___y_6318_);
if (lean_obj_tag(v___x_6323_) == 0)
{
lean_object* v___x_6324_; 
v___x_6324_ = lean_unsigned_to_nat(0u);
v___y_6304_ = v___y_6315_;
v___y_6305_ = v___y_6316_;
v___y_6306_ = v___y_6319_;
v___y_6307_ = v___y_6318_;
v___y_6308_ = v___y_6320_;
v___y_6309_ = v___y_6321_;
v___y_6310_ = v_ref_6322_;
v___y_6311_ = v___x_6324_;
goto v___jp_6303_;
}
else
{
lean_object* v_val_6325_; 
v_val_6325_ = lean_ctor_get(v___x_6323_, 0);
lean_inc(v_val_6325_);
lean_dec_ref(v___x_6323_);
v___y_6304_ = v___y_6315_;
v___y_6305_ = v___y_6316_;
v___y_6306_ = v___y_6319_;
v___y_6307_ = v___y_6318_;
v___y_6308_ = v___y_6320_;
v___y_6309_ = v___y_6321_;
v___y_6310_ = v_ref_6322_;
v___y_6311_ = v_val_6325_;
goto v___jp_6303_;
}
}
v___jp_6327_:
{
if (v___y_6334_ == 0)
{
v___y_6315_ = v___y_6328_;
v___y_6316_ = v___y_6329_;
v___y_6317_ = v___y_6330_;
v___y_6318_ = v___y_6333_;
v___y_6319_ = v___y_6331_;
v___y_6320_ = v___y_6332_;
v___y_6321_ = v_severity_6235_;
goto v___jp_6314_;
}
else
{
v___y_6315_ = v___y_6328_;
v___y_6316_ = v___y_6329_;
v___y_6317_ = v___y_6330_;
v___y_6318_ = v___y_6333_;
v___y_6319_ = v___y_6331_;
v___y_6320_ = v___y_6332_;
v___y_6321_ = v___x_6326_;
goto v___jp_6314_;
}
}
v___jp_6335_:
{
if (v___y_6336_ == 0)
{
lean_object* v_fileName_6337_; lean_object* v_fileMap_6338_; lean_object* v_options_6339_; lean_object* v_ref_6340_; uint8_t v_suppressElabErrors_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___f_6344_; uint8_t v___x_6345_; uint8_t v___x_6346_; 
v_fileName_6337_ = lean_ctor_get(v___y_6239_, 0);
v_fileMap_6338_ = lean_ctor_get(v___y_6239_, 1);
v_options_6339_ = lean_ctor_get(v___y_6239_, 2);
v_ref_6340_ = lean_ctor_get(v___y_6239_, 5);
v_suppressElabErrors_6341_ = lean_ctor_get_uint8(v___y_6239_, sizeof(void*)*14 + 1);
v___x_6342_ = lean_box(v___y_6336_);
v___x_6343_ = lean_box(v_suppressElabErrors_6341_);
v___f_6344_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6344_, 0, v___x_6342_);
lean_closure_set(v___f_6344_, 1, v___x_6343_);
v___x_6345_ = 1;
v___x_6346_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6235_, v___x_6345_);
if (v___x_6346_ == 0)
{
v___y_6328_ = v___f_6344_;
v___y_6329_ = v_fileName_6337_;
v___y_6330_ = v_ref_6340_;
v___y_6331_ = v_fileMap_6338_;
v___y_6332_ = v_suppressElabErrors_6341_;
v___y_6333_ = v___y_6336_;
v___y_6334_ = v___x_6346_;
goto v___jp_6327_;
}
else
{
lean_object* v___x_6347_; uint8_t v___x_6348_; 
v___x_6347_ = l_Lean_warningAsError;
v___x_6348_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_6339_, v___x_6347_);
v___y_6328_ = v___f_6344_;
v___y_6329_ = v_fileName_6337_;
v___y_6330_ = v_ref_6340_;
v___y_6331_ = v_fileMap_6338_;
v___y_6332_ = v_suppressElabErrors_6341_;
v___y_6333_ = v___y_6336_;
v___y_6334_ = v___x_6348_;
goto v___jp_6327_;
}
}
else
{
lean_object* v___x_6349_; lean_object* v___x_6350_; 
lean_dec_ref(v_msgData_6234_);
v___x_6349_ = lean_box(0);
v___x_6350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6350_, 0, v___x_6349_);
return v___x_6350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___boxed(lean_object* v_ref_6353_, lean_object* v_msgData_6354_, lean_object* v_severity_6355_, lean_object* v_isSilent_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_){
_start:
{
uint8_t v_severity_boxed_6362_; uint8_t v_isSilent_boxed_6363_; lean_object* v_res_6364_; 
v_severity_boxed_6362_ = lean_unbox(v_severity_6355_);
v_isSilent_boxed_6363_ = lean_unbox(v_isSilent_6356_);
v_res_6364_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6353_, v_msgData_6354_, v_severity_boxed_6362_, v_isSilent_boxed_6363_, v___y_6357_, v___y_6358_, v___y_6359_, v___y_6360_);
lean_dec(v___y_6360_);
lean_dec_ref(v___y_6359_);
lean_dec(v___y_6358_);
lean_dec_ref(v___y_6357_);
lean_dec(v_ref_6353_);
return v_res_6364_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_6365_, uint8_t v_severity_6366_, uint8_t v_isSilent_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_){
_start:
{
lean_object* v_ref_6373_; lean_object* v___x_6374_; 
v_ref_6373_ = lean_ctor_get(v___y_6370_, 5);
v___x_6374_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7(v_ref_6373_, v_msgData_6365_, v_severity_6366_, v_isSilent_6367_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_);
return v___x_6374_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_6375_, lean_object* v_severity_6376_, lean_object* v_isSilent_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_){
_start:
{
uint8_t v_severity_boxed_6383_; uint8_t v_isSilent_boxed_6384_; lean_object* v_res_6385_; 
v_severity_boxed_6383_ = lean_unbox(v_severity_6376_);
v_isSilent_boxed_6384_ = lean_unbox(v_isSilent_6377_);
v_res_6385_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6375_, v_severity_boxed_6383_, v_isSilent_boxed_6384_, v___y_6378_, v___y_6379_, v___y_6380_, v___y_6381_);
lean_dec(v___y_6381_);
lean_dec_ref(v___y_6380_);
lean_dec(v___y_6379_);
lean_dec_ref(v___y_6378_);
return v_res_6385_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(lean_object* v_msgData_6386_, lean_object* v___y_6387_, lean_object* v___y_6388_, lean_object* v___y_6389_, lean_object* v___y_6390_){
_start:
{
uint8_t v___x_6392_; uint8_t v___x_6393_; lean_object* v___x_6394_; 
v___x_6392_ = 2;
v___x_6393_ = 0;
v___x_6394_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3(v_msgData_6386_, v___x_6392_, v___x_6393_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_);
return v___x_6394_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_6395_, lean_object* v___y_6396_, lean_object* v___y_6397_, lean_object* v___y_6398_, lean_object* v___y_6399_, lean_object* v___y_6400_){
_start:
{
lean_object* v_res_6401_; 
v_res_6401_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v_msgData_6395_, v___y_6396_, v___y_6397_, v___y_6398_, v___y_6399_);
lean_dec(v___y_6399_);
lean_dec_ref(v___y_6398_);
lean_dec(v___y_6397_);
lean_dec_ref(v___y_6396_);
return v_res_6401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(lean_object* v_f_6402_, lean_object* v___y_6403_, lean_object* v___y_6404_, lean_object* v___y_6405_, lean_object* v___y_6406_){
_start:
{
lean_object* v_module_6408_; lean_object* v_const_6409_; lean_object* v_exception_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; 
v_module_6408_ = lean_ctor_get(v_f_6402_, 0);
lean_inc(v_module_6408_);
v_const_6409_ = lean_ctor_get(v_f_6402_, 1);
lean_inc(v_const_6409_);
v_exception_6410_ = lean_ctor_get(v_f_6402_, 2);
lean_inc_ref(v_exception_6410_);
lean_dec_ref(v_f_6402_);
v___x_6411_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_6412_ = l_Lean_MessageData_ofName(v_const_6409_);
v___x_6413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6413_, 0, v___x_6411_);
lean_ctor_set(v___x_6413_, 1, v___x_6412_);
v___x_6414_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_6415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6415_, 0, v___x_6413_);
lean_ctor_set(v___x_6415_, 1, v___x_6414_);
v___x_6416_ = l_Lean_MessageData_ofName(v_module_6408_);
v___x_6417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6417_, 0, v___x_6415_);
lean_ctor_set(v___x_6417_, 1, v___x_6416_);
v___x_6418_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_6419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6419_, 0, v___x_6417_);
lean_ctor_set(v___x_6419_, 1, v___x_6418_);
v___x_6420_ = l_Lean_Exception_toMessageData(v_exception_6410_);
v___x_6421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6421_, 0, v___x_6419_);
lean_ctor_set(v___x_6421_, 1, v___x_6420_);
v___x_6422_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2(v___x_6421_, v___y_6403_, v___y_6404_, v___y_6405_, v___y_6406_);
return v___x_6422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0___boxed(lean_object* v_f_6423_, lean_object* v___y_6424_, lean_object* v___y_6425_, lean_object* v___y_6426_, lean_object* v___y_6427_, lean_object* v___y_6428_){
_start:
{
lean_object* v_res_6429_; 
v_res_6429_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v_f_6423_, v___y_6424_, v___y_6425_, v___y_6426_, v___y_6427_);
lean_dec(v___y_6427_);
lean_dec_ref(v___y_6426_);
lean_dec(v___y_6425_);
lean_dec_ref(v___y_6424_);
return v_res_6429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(lean_object* v_as_6430_, size_t v_i_6431_, size_t v_stop_6432_, lean_object* v_b_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_){
_start:
{
uint8_t v___x_6439_; 
v___x_6439_ = lean_usize_dec_eq(v_i_6431_, v_stop_6432_);
if (v___x_6439_ == 0)
{
lean_object* v___x_6440_; lean_object* v___x_6441_; 
v___x_6440_ = lean_array_uget_borrowed(v_as_6430_, v_i_6431_);
lean_inc(v___x_6440_);
v___x_6441_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0(v___x_6440_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_);
if (lean_obj_tag(v___x_6441_) == 0)
{
lean_object* v_a_6442_; size_t v___x_6443_; size_t v___x_6444_; 
v_a_6442_ = lean_ctor_get(v___x_6441_, 0);
lean_inc(v_a_6442_);
lean_dec_ref(v___x_6441_);
v___x_6443_ = ((size_t)1ULL);
v___x_6444_ = lean_usize_add(v_i_6431_, v___x_6443_);
v_i_6431_ = v___x_6444_;
v_b_6433_ = v_a_6442_;
goto _start;
}
else
{
return v___x_6441_;
}
}
else
{
lean_object* v___x_6446_; 
v___x_6446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6446_, 0, v_b_6433_);
return v___x_6446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3___boxed(lean_object* v_as_6447_, lean_object* v_i_6448_, lean_object* v_stop_6449_, lean_object* v_b_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_){
_start:
{
size_t v_i_boxed_6456_; size_t v_stop_boxed_6457_; lean_object* v_res_6458_; 
v_i_boxed_6456_ = lean_unbox_usize(v_i_6448_);
lean_dec(v_i_6448_);
v_stop_boxed_6457_ = lean_unbox_usize(v_stop_6449_);
lean_dec(v_stop_6449_);
v_res_6458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_as_6447_, v_i_boxed_6456_, v_stop_boxed_6457_, v_b_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
lean_dec(v___y_6454_);
lean_dec_ref(v___y_6453_);
lean_dec(v___y_6452_);
lean_dec_ref(v___y_6451_);
lean_dec_ref(v_as_6447_);
return v_res_6458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(lean_object* v_as_6459_, size_t v_i_6460_, size_t v_stop_6461_, lean_object* v_b_6462_){
_start:
{
uint8_t v___x_6463_; 
v___x_6463_ = lean_usize_dec_eq(v_i_6460_, v_stop_6461_);
if (v___x_6463_ == 0)
{
lean_object* v___x_6464_; lean_object* v___x_6465_; lean_object* v___x_6466_; size_t v___x_6467_; size_t v___x_6468_; 
v___x_6464_ = lean_array_uget_borrowed(v_as_6459_, v_i_6460_);
lean_inc(v___x_6464_);
v___x_6465_ = lean_task_get_own(v___x_6464_);
v___x_6466_ = l_Lean_Meta_LazyDiscrTree_InitResults_append___redArg(v_b_6462_, v___x_6465_);
v___x_6467_ = ((size_t)1ULL);
v___x_6468_ = lean_usize_add(v_i_6460_, v___x_6467_);
v_i_6460_ = v___x_6468_;
v_b_6462_ = v___x_6466_;
goto _start;
}
else
{
return v_b_6462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_as_6470_, lean_object* v_i_6471_, lean_object* v_stop_6472_, lean_object* v_b_6473_){
_start:
{
size_t v_i_boxed_6474_; size_t v_stop_boxed_6475_; lean_object* v_res_6476_; 
v_i_boxed_6474_ = lean_unbox_usize(v_i_6471_);
lean_dec(v_i_6471_);
v_stop_boxed_6475_ = lean_unbox_usize(v_stop_6472_);
lean_dec(v_stop_6472_);
v_res_6476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6470_, v_i_boxed_6474_, v_stop_boxed_6475_, v_b_6473_);
lean_dec_ref(v_as_6470_);
return v_res_6476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(lean_object* v_z_6477_, lean_object* v_tasks_6478_){
_start:
{
lean_object* v___x_6479_; lean_object* v___x_6480_; uint8_t v___x_6481_; 
v___x_6479_ = lean_unsigned_to_nat(0u);
v___x_6480_ = lean_array_get_size(v_tasks_6478_);
v___x_6481_ = lean_nat_dec_lt(v___x_6479_, v___x_6480_);
if (v___x_6481_ == 0)
{
return v_z_6477_;
}
else
{
uint8_t v___x_6482_; 
v___x_6482_ = lean_nat_dec_le(v___x_6480_, v___x_6480_);
if (v___x_6482_ == 0)
{
if (v___x_6481_ == 0)
{
return v_z_6477_;
}
else
{
size_t v___x_6483_; size_t v___x_6484_; lean_object* v___x_6485_; 
v___x_6483_ = ((size_t)0ULL);
v___x_6484_ = lean_usize_of_nat(v___x_6480_);
v___x_6485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6478_, v___x_6483_, v___x_6484_, v_z_6477_);
return v___x_6485_;
}
}
else
{
size_t v___x_6486_; size_t v___x_6487_; lean_object* v___x_6488_; 
v___x_6486_ = ((size_t)0ULL);
v___x_6487_ = lean_usize_of_nat(v___x_6480_);
v___x_6488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_tasks_6478_, v___x_6486_, v___x_6487_, v_z_6477_);
return v___x_6488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg___boxed(lean_object* v_z_6489_, lean_object* v_tasks_6490_){
_start:
{
lean_object* v_res_6491_; 
v_res_6491_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6489_, v_tasks_6490_);
lean_dec_ref(v_tasks_6490_);
return v_res_6491_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; 
v___x_6492_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6493_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2, &l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_instInhabitedTrie_default___closed__2);
v___x_6494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6494_, 0, v___x_6493_);
lean_ctor_set(v___x_6494_, 1, v___x_6492_);
return v___x_6494_;
}
}
static lean_object* _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6495_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6496_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__0);
v___x_6497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6497_, 0, v___x_6496_);
lean_ctor_set(v___x_6497_, 1, v___x_6495_);
return v___x_6497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(lean_object* v_cctx_6498_, lean_object* v_ngen_6499_, lean_object* v_env_6500_, lean_object* v_act_6501_, lean_object* v_constantsPerTask_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_){
_start:
{
lean_object* v___x_6508_; lean_object* v_moduleData_6509_; lean_object* v_n_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; lean_object* v_a_6514_; lean_object* v___x_6516_; uint8_t v_isShared_6517_; uint8_t v_isSharedCheck_6556_; 
v___x_6508_ = l_Lean_Environment_header(v_env_6500_);
v_moduleData_6509_ = lean_ctor_get(v___x_6508_, 6);
lean_inc_ref(v_moduleData_6509_);
lean_dec_ref(v___x_6508_);
v_n_6510_ = lean_array_get_size(v_moduleData_6509_);
lean_dec_ref(v_moduleData_6509_);
v___x_6511_ = lean_unsigned_to_nat(0u);
v___x_6512_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___redArg___closed__0));
v___x_6513_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6498_, v_env_6500_, v_act_6501_, v_constantsPerTask_6502_, v_n_6510_, v_ngen_6499_, v___x_6512_, v___x_6511_, v___x_6511_, v___x_6511_);
v_a_6514_ = lean_ctor_get(v___x_6513_, 0);
v_isSharedCheck_6556_ = !lean_is_exclusive(v___x_6513_);
if (v_isSharedCheck_6556_ == 0)
{
v___x_6516_ = v___x_6513_;
v_isShared_6517_ = v_isSharedCheck_6556_;
goto v_resetjp_6515_;
}
else
{
lean_inc(v_a_6514_);
lean_dec(v___x_6513_);
v___x_6516_ = lean_box(0);
v_isShared_6517_ = v_isSharedCheck_6556_;
goto v_resetjp_6515_;
}
v_resetjp_6515_:
{
lean_object* v___x_6518_; lean_object* v_r_6519_; lean_object* v_tree_6526_; lean_object* v_errors_6527_; lean_object* v___x_6528_; uint8_t v___x_6529_; 
v___x_6518_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___closed__1);
v_r_6519_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v___x_6518_, v_a_6514_);
lean_dec(v_a_6514_);
v_tree_6526_ = lean_ctor_get(v_r_6519_, 0);
lean_inc_ref(v_tree_6526_);
v_errors_6527_ = lean_ctor_get(v_r_6519_, 1);
lean_inc_ref(v_errors_6527_);
v___x_6528_ = lean_array_get_size(v_errors_6527_);
v___x_6529_ = lean_nat_dec_lt(v___x_6511_, v___x_6528_);
if (v___x_6529_ == 0)
{
lean_object* v___x_6530_; lean_object* v___x_6531_; 
lean_dec_ref(v_errors_6527_);
lean_dec_ref(v_r_6519_);
lean_del_object(v___x_6516_);
v___x_6530_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6526_);
v___x_6531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6531_, 0, v___x_6530_);
return v___x_6531_;
}
else
{
lean_object* v___x_6532_; uint8_t v___x_6533_; 
lean_dec_ref(v_tree_6526_);
v___x_6532_ = lean_box(0);
v___x_6533_ = lean_nat_dec_le(v___x_6528_, v___x_6528_);
if (v___x_6533_ == 0)
{
if (v___x_6529_ == 0)
{
lean_dec_ref(v_errors_6527_);
goto v___jp_6520_;
}
else
{
size_t v___x_6534_; size_t v___x_6535_; lean_object* v___x_6536_; 
v___x_6534_ = ((size_t)0ULL);
v___x_6535_ = lean_usize_of_nat(v___x_6528_);
v___x_6536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6527_, v___x_6534_, v___x_6535_, v___x_6532_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_);
lean_dec_ref(v_errors_6527_);
if (lean_obj_tag(v___x_6536_) == 0)
{
lean_dec_ref(v___x_6536_);
goto v___jp_6520_;
}
else
{
lean_object* v_a_6537_; lean_object* v___x_6539_; uint8_t v_isShared_6540_; uint8_t v_isSharedCheck_6544_; 
lean_dec_ref(v_r_6519_);
lean_del_object(v___x_6516_);
v_a_6537_ = lean_ctor_get(v___x_6536_, 0);
v_isSharedCheck_6544_ = !lean_is_exclusive(v___x_6536_);
if (v_isSharedCheck_6544_ == 0)
{
v___x_6539_ = v___x_6536_;
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
else
{
lean_inc(v_a_6537_);
lean_dec(v___x_6536_);
v___x_6539_ = lean_box(0);
v_isShared_6540_ = v_isSharedCheck_6544_;
goto v_resetjp_6538_;
}
v_resetjp_6538_:
{
lean_object* v___x_6542_; 
if (v_isShared_6540_ == 0)
{
v___x_6542_ = v___x_6539_;
goto v_reusejp_6541_;
}
else
{
lean_object* v_reuseFailAlloc_6543_; 
v_reuseFailAlloc_6543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_a_6537_);
v___x_6542_ = v_reuseFailAlloc_6543_;
goto v_reusejp_6541_;
}
v_reusejp_6541_:
{
return v___x_6542_;
}
}
}
}
}
else
{
size_t v___x_6545_; size_t v___x_6546_; lean_object* v___x_6547_; 
v___x_6545_ = ((size_t)0ULL);
v___x_6546_ = lean_usize_of_nat(v___x_6528_);
v___x_6547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__3(v_errors_6527_, v___x_6545_, v___x_6546_, v___x_6532_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_);
lean_dec_ref(v_errors_6527_);
if (lean_obj_tag(v___x_6547_) == 0)
{
lean_dec_ref(v___x_6547_);
goto v___jp_6520_;
}
else
{
lean_object* v_a_6548_; lean_object* v___x_6550_; uint8_t v_isShared_6551_; uint8_t v_isSharedCheck_6555_; 
lean_dec_ref(v_r_6519_);
lean_del_object(v___x_6516_);
v_a_6548_ = lean_ctor_get(v___x_6547_, 0);
v_isSharedCheck_6555_ = !lean_is_exclusive(v___x_6547_);
if (v_isSharedCheck_6555_ == 0)
{
v___x_6550_ = v___x_6547_;
v_isShared_6551_ = v_isSharedCheck_6555_;
goto v_resetjp_6549_;
}
else
{
lean_inc(v_a_6548_);
lean_dec(v___x_6547_);
v___x_6550_ = lean_box(0);
v_isShared_6551_ = v_isSharedCheck_6555_;
goto v_resetjp_6549_;
}
v_resetjp_6549_:
{
lean_object* v___x_6553_; 
if (v_isShared_6551_ == 0)
{
v___x_6553_ = v___x_6550_;
goto v_reusejp_6552_;
}
else
{
lean_object* v_reuseFailAlloc_6554_; 
v_reuseFailAlloc_6554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6554_, 0, v_a_6548_);
v___x_6553_ = v_reuseFailAlloc_6554_;
goto v_reusejp_6552_;
}
v_reusejp_6552_:
{
return v___x_6553_;
}
}
}
}
}
v___jp_6520_:
{
lean_object* v_tree_6521_; lean_object* v___x_6522_; lean_object* v___x_6524_; 
v_tree_6521_ = lean_ctor_get(v_r_6519_, 0);
lean_inc_ref(v_tree_6521_);
lean_dec_ref(v_r_6519_);
v___x_6522_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v_tree_6521_);
if (v_isShared_6517_ == 0)
{
lean_ctor_set(v___x_6516_, 0, v___x_6522_);
v___x_6524_ = v___x_6516_;
goto v_reusejp_6523_;
}
else
{
lean_object* v_reuseFailAlloc_6525_; 
v_reuseFailAlloc_6525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6525_, 0, v___x_6522_);
v___x_6524_ = v_reuseFailAlloc_6525_;
goto v_reusejp_6523_;
}
v_reusejp_6523_:
{
return v___x_6524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg___boxed(lean_object* v_cctx_6557_, lean_object* v_ngen_6558_, lean_object* v_env_6559_, lean_object* v_act_6560_, lean_object* v_constantsPerTask_6561_, lean_object* v___y_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_, lean_object* v___y_6565_, lean_object* v___y_6566_){
_start:
{
lean_object* v_res_6567_; 
v_res_6567_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6557_, v_ngen_6558_, v_env_6559_, v_act_6560_, v_constantsPerTask_6561_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_);
lean_dec(v___y_6565_);
lean_dec_ref(v___y_6564_);
lean_dec(v___y_6563_);
lean_dec_ref(v___y_6562_);
lean_dec(v_constantsPerTask_6561_);
return v_res_6567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(lean_object* v_a_6568_, lean_object* v___x_6569_, lean_object* v_addEntry_6570_, lean_object* v_constantsPerTask_6571_, lean_object* v_droppedEntriesRef_6572_, lean_object* v_droppedKeys_6573_, lean_object* v___y_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_, lean_object* v___y_6577_){
_start:
{
lean_object* v___x_6579_; lean_object* v_env_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; 
v___x_6579_ = lean_st_ref_get(v___y_6577_);
v_env_6580_ = lean_ctor_get(v___x_6579_, 0);
lean_inc_ref(v_env_6580_);
lean_dec(v___x_6579_);
lean_inc_ref(v_a_6568_);
v___x_6581_ = l_Lean_Meta_LazyDiscrTree_createTreeCtx(v_a_6568_);
v___x_6582_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v___x_6581_, v___x_6569_, v_env_6580_, v_addEntry_6570_, v_constantsPerTask_6571_, v___y_6574_, v___y_6575_, v___y_6576_, v___y_6577_);
if (lean_obj_tag(v___x_6582_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_6572_) == 1)
{
lean_object* v_a_6583_; lean_object* v_val_6584_; lean_object* v___x_6586_; uint8_t v_isShared_6587_; uint8_t v_isSharedCheck_6617_; 
v_a_6583_ = lean_ctor_get(v___x_6582_, 0);
lean_inc(v_a_6583_);
lean_dec_ref(v___x_6582_);
v_val_6584_ = lean_ctor_get(v_droppedEntriesRef_6572_, 0);
v_isSharedCheck_6617_ = !lean_is_exclusive(v_droppedEntriesRef_6572_);
if (v_isSharedCheck_6617_ == 0)
{
v___x_6586_ = v_droppedEntriesRef_6572_;
v_isShared_6587_ = v_isSharedCheck_6617_;
goto v_resetjp_6585_;
}
else
{
lean_inc(v_val_6584_);
lean_dec(v_droppedEntriesRef_6572_);
v___x_6586_ = lean_box(0);
v_isShared_6587_ = v_isSharedCheck_6617_;
goto v_resetjp_6585_;
}
v_resetjp_6585_:
{
lean_object* v___x_6588_; 
v___x_6588_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_6583_, v_droppedKeys_6573_, v___y_6574_, v___y_6575_, v___y_6576_, v___y_6577_);
if (lean_obj_tag(v___x_6588_) == 0)
{
lean_object* v_a_6589_; lean_object* v___x_6591_; uint8_t v_isShared_6592_; uint8_t v_isSharedCheck_6608_; 
v_a_6589_ = lean_ctor_get(v___x_6588_, 0);
v_isSharedCheck_6608_ = !lean_is_exclusive(v___x_6588_);
if (v_isSharedCheck_6608_ == 0)
{
v___x_6591_ = v___x_6588_;
v_isShared_6592_ = v_isSharedCheck_6608_;
goto v_resetjp_6590_;
}
else
{
lean_inc(v_a_6589_);
lean_dec(v___x_6588_);
v___x_6591_ = lean_box(0);
v_isShared_6592_ = v_isSharedCheck_6608_;
goto v_resetjp_6590_;
}
v_resetjp_6590_:
{
lean_object* v_fst_6593_; lean_object* v_snd_6594_; lean_object* v___x_6595_; lean_object* v___y_6597_; 
v_fst_6593_ = lean_ctor_get(v_a_6589_, 0);
lean_inc(v_fst_6593_);
v_snd_6594_ = lean_ctor_get(v_a_6589_, 1);
lean_inc(v_snd_6594_);
lean_dec(v_a_6589_);
v___x_6595_ = lean_st_ref_get(v_val_6584_);
if (lean_obj_tag(v___x_6595_) == 0)
{
lean_object* v___x_6606_; 
v___x_6606_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_6597_ = v___x_6606_;
goto v___jp_6596_;
}
else
{
lean_object* v_val_6607_; 
v_val_6607_ = lean_ctor_get(v___x_6595_, 0);
lean_inc(v_val_6607_);
lean_dec_ref(v___x_6595_);
v___y_6597_ = v_val_6607_;
goto v___jp_6596_;
}
v___jp_6596_:
{
lean_object* v___x_6598_; lean_object* v___x_6600_; 
v___x_6598_ = l_Array_append___redArg(v___y_6597_, v_fst_6593_);
lean_dec(v_fst_6593_);
if (v_isShared_6587_ == 0)
{
lean_ctor_set(v___x_6586_, 0, v___x_6598_);
v___x_6600_ = v___x_6586_;
goto v_reusejp_6599_;
}
else
{
lean_object* v_reuseFailAlloc_6605_; 
v_reuseFailAlloc_6605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6605_, 0, v___x_6598_);
v___x_6600_ = v_reuseFailAlloc_6605_;
goto v_reusejp_6599_;
}
v_reusejp_6599_:
{
lean_object* v___x_6601_; lean_object* v___x_6603_; 
v___x_6601_ = lean_st_ref_set(v_val_6584_, v___x_6600_);
lean_dec(v_val_6584_);
if (v_isShared_6592_ == 0)
{
lean_ctor_set(v___x_6591_, 0, v_snd_6594_);
v___x_6603_ = v___x_6591_;
goto v_reusejp_6602_;
}
else
{
lean_object* v_reuseFailAlloc_6604_; 
v_reuseFailAlloc_6604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6604_, 0, v_snd_6594_);
v___x_6603_ = v_reuseFailAlloc_6604_;
goto v_reusejp_6602_;
}
v_reusejp_6602_:
{
return v___x_6603_;
}
}
}
}
}
else
{
lean_object* v_a_6609_; lean_object* v___x_6611_; uint8_t v_isShared_6612_; uint8_t v_isSharedCheck_6616_; 
lean_del_object(v___x_6586_);
lean_dec(v_val_6584_);
v_a_6609_ = lean_ctor_get(v___x_6588_, 0);
v_isSharedCheck_6616_ = !lean_is_exclusive(v___x_6588_);
if (v_isSharedCheck_6616_ == 0)
{
v___x_6611_ = v___x_6588_;
v_isShared_6612_ = v_isSharedCheck_6616_;
goto v_resetjp_6610_;
}
else
{
lean_inc(v_a_6609_);
lean_dec(v___x_6588_);
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
}
else
{
lean_object* v_a_6618_; lean_object* v___x_6619_; 
lean_dec(v_droppedEntriesRef_6572_);
v_a_6618_ = lean_ctor_get(v___x_6582_, 0);
lean_inc(v_a_6618_);
lean_dec_ref(v___x_6582_);
v___x_6619_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_6618_, v_droppedKeys_6573_, v___y_6574_, v___y_6575_, v___y_6576_, v___y_6577_);
return v___x_6619_;
}
}
else
{
lean_dec(v_droppedKeys_6573_);
lean_dec(v_droppedEntriesRef_6572_);
return v___x_6582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed(lean_object* v_a_6620_, lean_object* v___x_6621_, lean_object* v_addEntry_6622_, lean_object* v_constantsPerTask_6623_, lean_object* v_droppedEntriesRef_6624_, lean_object* v_droppedKeys_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_){
_start:
{
lean_object* v_res_6631_; 
v_res_6631_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0(v_a_6620_, v___x_6621_, v_addEntry_6622_, v_constantsPerTask_6623_, v_droppedEntriesRef_6624_, v_droppedKeys_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_);
lean_dec(v___y_6629_);
lean_dec_ref(v___y_6628_);
lean_dec(v___y_6627_);
lean_dec_ref(v___y_6626_);
lean_dec(v_constantsPerTask_6623_);
lean_dec_ref(v_a_6620_);
return v_res_6631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(lean_object* v_ext_6633_, lean_object* v_addEntry_6634_, lean_object* v_droppedKeys_6635_, lean_object* v_constantsPerTask_6636_, lean_object* v_droppedEntriesRef_6637_, lean_object* v_ty_6638_, lean_object* v_a_6639_, lean_object* v_a_6640_, lean_object* v_a_6641_, lean_object* v_a_6642_){
_start:
{
lean_object* v___x_6644_; lean_object* v_ngen_6645_; lean_object* v_namePrefix_6646_; lean_object* v_idx_6647_; lean_object* v___x_6649_; uint8_t v_isShared_6650_; uint8_t v_isSharedCheck_6721_; 
v___x_6644_ = lean_st_ref_get(v_a_6642_);
v_ngen_6645_ = lean_ctor_get(v___x_6644_, 2);
lean_inc_ref(v_ngen_6645_);
lean_dec(v___x_6644_);
v_namePrefix_6646_ = lean_ctor_get(v_ngen_6645_, 0);
v_idx_6647_ = lean_ctor_get(v_ngen_6645_, 1);
v_isSharedCheck_6721_ = !lean_is_exclusive(v_ngen_6645_);
if (v_isSharedCheck_6721_ == 0)
{
v___x_6649_ = v_ngen_6645_;
v_isShared_6650_ = v_isSharedCheck_6721_;
goto v_resetjp_6648_;
}
else
{
lean_inc(v_idx_6647_);
lean_inc(v_namePrefix_6646_);
lean_dec(v_ngen_6645_);
v___x_6649_ = lean_box(0);
v_isShared_6650_ = v_isSharedCheck_6721_;
goto v_resetjp_6648_;
}
v_resetjp_6648_:
{
lean_object* v___x_6651_; lean_object* v_env_6652_; lean_object* v_nextMacroScope_6653_; lean_object* v_auxDeclNGen_6654_; lean_object* v_traceState_6655_; lean_object* v_cache_6656_; lean_object* v_messages_6657_; lean_object* v_infoState_6658_; lean_object* v_snapshotTasks_6659_; lean_object* v___x_6661_; uint8_t v_isShared_6662_; uint8_t v_isSharedCheck_6719_; 
v___x_6651_ = lean_st_ref_take(v_a_6642_);
v_env_6652_ = lean_ctor_get(v___x_6651_, 0);
v_nextMacroScope_6653_ = lean_ctor_get(v___x_6651_, 1);
v_auxDeclNGen_6654_ = lean_ctor_get(v___x_6651_, 3);
v_traceState_6655_ = lean_ctor_get(v___x_6651_, 4);
v_cache_6656_ = lean_ctor_get(v___x_6651_, 5);
v_messages_6657_ = lean_ctor_get(v___x_6651_, 6);
v_infoState_6658_ = lean_ctor_get(v___x_6651_, 7);
v_snapshotTasks_6659_ = lean_ctor_get(v___x_6651_, 8);
v_isSharedCheck_6719_ = !lean_is_exclusive(v___x_6651_);
if (v_isSharedCheck_6719_ == 0)
{
lean_object* v_unused_6720_; 
v_unused_6720_ = lean_ctor_get(v___x_6651_, 2);
lean_dec(v_unused_6720_);
v___x_6661_ = v___x_6651_;
v_isShared_6662_ = v_isSharedCheck_6719_;
goto v_resetjp_6660_;
}
else
{
lean_inc(v_snapshotTasks_6659_);
lean_inc(v_infoState_6658_);
lean_inc(v_messages_6657_);
lean_inc(v_cache_6656_);
lean_inc(v_traceState_6655_);
lean_inc(v_auxDeclNGen_6654_);
lean_inc(v_nextMacroScope_6653_);
lean_inc(v_env_6652_);
lean_dec(v___x_6651_);
v___x_6661_ = lean_box(0);
v_isShared_6662_ = v_isSharedCheck_6719_;
goto v_resetjp_6660_;
}
v_resetjp_6660_:
{
lean_object* v___x_6663_; lean_object* v___x_6664_; lean_object* v___x_6665_; lean_object* v___x_6667_; 
lean_inc(v_idx_6647_);
lean_inc(v_namePrefix_6646_);
v___x_6663_ = l_Lean_Name_num___override(v_namePrefix_6646_, v_idx_6647_);
v___x_6664_ = lean_unsigned_to_nat(1u);
v___x_6665_ = lean_nat_add(v_idx_6647_, v___x_6664_);
lean_dec(v_idx_6647_);
if (v_isShared_6650_ == 0)
{
lean_ctor_set(v___x_6649_, 1, v___x_6665_);
v___x_6667_ = v___x_6649_;
goto v_reusejp_6666_;
}
else
{
lean_object* v_reuseFailAlloc_6718_; 
v_reuseFailAlloc_6718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6718_, 0, v_namePrefix_6646_);
lean_ctor_set(v_reuseFailAlloc_6718_, 1, v___x_6665_);
v___x_6667_ = v_reuseFailAlloc_6718_;
goto v_reusejp_6666_;
}
v_reusejp_6666_:
{
lean_object* v___x_6669_; 
if (v_isShared_6662_ == 0)
{
lean_ctor_set(v___x_6661_, 2, v___x_6667_);
v___x_6669_ = v___x_6661_;
goto v_reusejp_6668_;
}
else
{
lean_object* v_reuseFailAlloc_6717_; 
v_reuseFailAlloc_6717_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6717_, 0, v_env_6652_);
lean_ctor_set(v_reuseFailAlloc_6717_, 1, v_nextMacroScope_6653_);
lean_ctor_set(v_reuseFailAlloc_6717_, 2, v___x_6667_);
lean_ctor_set(v_reuseFailAlloc_6717_, 3, v_auxDeclNGen_6654_);
lean_ctor_set(v_reuseFailAlloc_6717_, 4, v_traceState_6655_);
lean_ctor_set(v_reuseFailAlloc_6717_, 5, v_cache_6656_);
lean_ctor_set(v_reuseFailAlloc_6717_, 6, v_messages_6657_);
lean_ctor_set(v_reuseFailAlloc_6717_, 7, v_infoState_6658_);
lean_ctor_set(v_reuseFailAlloc_6717_, 8, v_snapshotTasks_6659_);
v___x_6669_ = v_reuseFailAlloc_6717_;
goto v_reusejp_6668_;
}
v_reusejp_6668_:
{
lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; lean_object* v_env_6674_; lean_object* v_asyncMode_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v_a_6679_; lean_object* v___x_6701_; 
v___x_6670_ = lean_st_ref_set(v_a_6642_, v___x_6669_);
v___x_6671_ = lean_box(0);
v___x_6672_ = lean_st_mk_ref(v___x_6671_);
v___x_6673_ = lean_st_ref_get(v_a_6642_);
v_env_6674_ = lean_ctor_get(v___x_6673_, 0);
lean_inc_ref(v_env_6674_);
lean_dec(v___x_6673_);
v_asyncMode_6675_ = lean_ctor_get(v_ext_6633_, 2);
v___x_6676_ = lean_box(0);
v___x_6677_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_6672_, v_ext_6633_, v_env_6674_, v_asyncMode_6675_, v___x_6676_);
lean_dec(v___x_6672_);
v___x_6701_ = lean_st_ref_get(v___x_6677_);
if (lean_obj_tag(v___x_6701_) == 0)
{
lean_object* v_options_6702_; lean_object* v___x_6703_; lean_object* v___f_6704_; lean_object* v___x_6705_; lean_object* v___x_6706_; 
v_options_6702_ = lean_ctor_get(v_a_6641_, 2);
v___x_6703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6703_, 0, v___x_6663_);
lean_ctor_set(v___x_6703_, 1, v___x_6664_);
lean_inc_ref(v_a_6641_);
v___f_6704_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_6704_, 0, v_a_6641_);
lean_closure_set(v___f_6704_, 1, v___x_6703_);
lean_closure_set(v___f_6704_, 2, v_addEntry_6634_);
lean_closure_set(v___f_6704_, 3, v_constantsPerTask_6636_);
lean_closure_set(v___f_6704_, 4, v_droppedEntriesRef_6637_);
lean_closure_set(v___f_6704_, 5, v_droppedKeys_6635_);
v___x_6705_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___closed__0));
v___x_6706_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_6705_, v_options_6702_, v___f_6704_, v___x_6676_, v_a_6639_, v_a_6640_, v_a_6641_, v_a_6642_);
if (lean_obj_tag(v___x_6706_) == 0)
{
lean_object* v_a_6707_; 
v_a_6707_ = lean_ctor_get(v___x_6706_, 0);
lean_inc(v_a_6707_);
lean_dec_ref(v___x_6706_);
v_a_6679_ = v_a_6707_;
goto v___jp_6678_;
}
else
{
lean_object* v_a_6708_; lean_object* v___x_6710_; uint8_t v_isShared_6711_; uint8_t v_isSharedCheck_6715_; 
lean_dec(v___x_6677_);
lean_dec_ref(v_ty_6638_);
v_a_6708_ = lean_ctor_get(v___x_6706_, 0);
v_isSharedCheck_6715_ = !lean_is_exclusive(v___x_6706_);
if (v_isSharedCheck_6715_ == 0)
{
v___x_6710_ = v___x_6706_;
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
else
{
lean_inc(v_a_6708_);
lean_dec(v___x_6706_);
v___x_6710_ = lean_box(0);
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
v_resetjp_6709_:
{
lean_object* v___x_6713_; 
if (v_isShared_6711_ == 0)
{
v___x_6713_ = v___x_6710_;
goto v_reusejp_6712_;
}
else
{
lean_object* v_reuseFailAlloc_6714_; 
v_reuseFailAlloc_6714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_a_6708_);
v___x_6713_ = v_reuseFailAlloc_6714_;
goto v_reusejp_6712_;
}
v_reusejp_6712_:
{
return v___x_6713_;
}
}
}
}
else
{
lean_object* v_val_6716_; 
lean_dec(v___x_6663_);
lean_dec(v_droppedEntriesRef_6637_);
lean_dec(v_constantsPerTask_6636_);
lean_dec(v_droppedKeys_6635_);
lean_dec_ref(v_addEntry_6634_);
v_val_6716_ = lean_ctor_get(v___x_6701_, 0);
lean_inc(v_val_6716_);
lean_dec_ref(v___x_6701_);
v_a_6679_ = v_val_6716_;
goto v___jp_6678_;
}
v___jp_6678_:
{
lean_object* v___x_6680_; 
v___x_6680_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v_a_6679_, v_ty_6638_, v_a_6639_, v_a_6640_, v_a_6641_, v_a_6642_);
if (lean_obj_tag(v___x_6680_) == 0)
{
lean_object* v_a_6681_; lean_object* v___x_6683_; uint8_t v_isShared_6684_; uint8_t v_isSharedCheck_6692_; 
v_a_6681_ = lean_ctor_get(v___x_6680_, 0);
v_isSharedCheck_6692_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6692_ == 0)
{
v___x_6683_ = v___x_6680_;
v_isShared_6684_ = v_isSharedCheck_6692_;
goto v_resetjp_6682_;
}
else
{
lean_inc(v_a_6681_);
lean_dec(v___x_6680_);
v___x_6683_ = lean_box(0);
v_isShared_6684_ = v_isSharedCheck_6692_;
goto v_resetjp_6682_;
}
v_resetjp_6682_:
{
lean_object* v_fst_6685_; lean_object* v_snd_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6690_; 
v_fst_6685_ = lean_ctor_get(v_a_6681_, 0);
lean_inc(v_fst_6685_);
v_snd_6686_ = lean_ctor_get(v_a_6681_, 1);
lean_inc(v_snd_6686_);
lean_dec(v_a_6681_);
v___x_6687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6687_, 0, v_snd_6686_);
v___x_6688_ = lean_st_ref_set(v___x_6677_, v___x_6687_);
lean_dec(v___x_6677_);
if (v_isShared_6684_ == 0)
{
lean_ctor_set(v___x_6683_, 0, v_fst_6685_);
v___x_6690_ = v___x_6683_;
goto v_reusejp_6689_;
}
else
{
lean_object* v_reuseFailAlloc_6691_; 
v_reuseFailAlloc_6691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6691_, 0, v_fst_6685_);
v___x_6690_ = v_reuseFailAlloc_6691_;
goto v_reusejp_6689_;
}
v_reusejp_6689_:
{
return v___x_6690_;
}
}
}
else
{
lean_object* v_a_6693_; lean_object* v___x_6695_; uint8_t v_isShared_6696_; uint8_t v_isSharedCheck_6700_; 
lean_dec(v___x_6677_);
v_a_6693_ = lean_ctor_get(v___x_6680_, 0);
v_isSharedCheck_6700_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6700_ == 0)
{
v___x_6695_ = v___x_6680_;
v_isShared_6696_ = v_isSharedCheck_6700_;
goto v_resetjp_6694_;
}
else
{
lean_inc(v_a_6693_);
lean_dec(v___x_6680_);
v___x_6695_ = lean_box(0);
v_isShared_6696_ = v_isSharedCheck_6700_;
goto v_resetjp_6694_;
}
v_resetjp_6694_:
{
lean_object* v___x_6698_; 
if (v_isShared_6696_ == 0)
{
v___x_6698_ = v___x_6695_;
goto v_reusejp_6697_;
}
else
{
lean_object* v_reuseFailAlloc_6699_; 
v_reuseFailAlloc_6699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6699_, 0, v_a_6693_);
v___x_6698_ = v_reuseFailAlloc_6699_;
goto v_reusejp_6697_;
}
v_reusejp_6697_:
{
return v___x_6698_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg___boxed(lean_object* v_ext_6722_, lean_object* v_addEntry_6723_, lean_object* v_droppedKeys_6724_, lean_object* v_constantsPerTask_6725_, lean_object* v_droppedEntriesRef_6726_, lean_object* v_ty_6727_, lean_object* v_a_6728_, lean_object* v_a_6729_, lean_object* v_a_6730_, lean_object* v_a_6731_, lean_object* v_a_6732_){
_start:
{
lean_object* v_res_6733_; 
v_res_6733_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ext_6722_, v_addEntry_6723_, v_droppedKeys_6724_, v_constantsPerTask_6725_, v_droppedEntriesRef_6726_, v_ty_6727_, v_a_6728_, v_a_6729_, v_a_6730_, v_a_6731_);
lean_dec(v_a_6731_);
lean_dec_ref(v_a_6730_);
lean_dec(v_a_6729_);
lean_dec_ref(v_a_6728_);
lean_dec_ref(v_ext_6722_);
return v_res_6733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches(lean_object* v_00_u03b1_6734_, lean_object* v_ext_6735_, lean_object* v_addEntry_6736_, lean_object* v_droppedKeys_6737_, lean_object* v_constantsPerTask_6738_, lean_object* v_droppedEntriesRef_6739_, lean_object* v_ty_6740_, lean_object* v_a_6741_, lean_object* v_a_6742_, lean_object* v_a_6743_, lean_object* v_a_6744_){
_start:
{
lean_object* v___x_6746_; 
v___x_6746_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ext_6735_, v_addEntry_6736_, v_droppedKeys_6737_, v_constantsPerTask_6738_, v_droppedEntriesRef_6739_, v_ty_6740_, v_a_6741_, v_a_6742_, v_a_6743_, v_a_6744_);
return v___x_6746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findImportMatches___boxed(lean_object* v_00_u03b1_6747_, lean_object* v_ext_6748_, lean_object* v_addEntry_6749_, lean_object* v_droppedKeys_6750_, lean_object* v_constantsPerTask_6751_, lean_object* v_droppedEntriesRef_6752_, lean_object* v_ty_6753_, lean_object* v_a_6754_, lean_object* v_a_6755_, lean_object* v_a_6756_, lean_object* v_a_6757_, lean_object* v_a_6758_){
_start:
{
lean_object* v_res_6759_; 
v_res_6759_ = l_Lean_Meta_LazyDiscrTree_findImportMatches(v_00_u03b1_6747_, v_ext_6748_, v_addEntry_6749_, v_droppedKeys_6750_, v_constantsPerTask_6751_, v_droppedEntriesRef_6752_, v_ty_6753_, v_a_6754_, v_a_6755_, v_a_6756_, v_a_6757_);
lean_dec(v_a_6757_);
lean_dec_ref(v_a_6756_);
lean_dec(v_a_6755_);
lean_dec_ref(v_a_6754_);
lean_dec_ref(v_ext_6748_);
return v_res_6759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(lean_object* v_00_u03b1_6760_, lean_object* v_cctx_6761_, lean_object* v_ngen_6762_, lean_object* v_env_6763_, lean_object* v_act_6764_, lean_object* v_constantsPerTask_6765_, lean_object* v___y_6766_, lean_object* v___y_6767_, lean_object* v___y_6768_, lean_object* v___y_6769_){
_start:
{
lean_object* v___x_6771_; 
v___x_6771_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___redArg(v_cctx_6761_, v_ngen_6762_, v_env_6763_, v_act_6764_, v_constantsPerTask_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_);
return v___x_6771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0___boxed(lean_object* v_00_u03b1_6772_, lean_object* v_cctx_6773_, lean_object* v_ngen_6774_, lean_object* v_env_6775_, lean_object* v_act_6776_, lean_object* v_constantsPerTask_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_){
_start:
{
lean_object* v_res_6783_; 
v_res_6783_ = l_Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0(v_00_u03b1_6772_, v_cctx_6773_, v_ngen_6774_, v_env_6775_, v_act_6776_, v_constantsPerTask_6777_, v___y_6778_, v___y_6779_, v___y_6780_, v___y_6781_);
lean_dec(v___y_6781_);
lean_dec_ref(v___y_6780_);
lean_dec(v___y_6779_);
lean_dec_ref(v___y_6778_);
lean_dec(v_constantsPerTask_6777_);
return v_res_6783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(lean_object* v_00_u03b1_6784_, lean_object* v_cctx_6785_, lean_object* v_env_6786_, lean_object* v_act_6787_, lean_object* v_constantsPerTask_6788_, lean_object* v_n_6789_, lean_object* v_ngen_6790_, lean_object* v_tasks_6791_, lean_object* v_start_6792_, lean_object* v_cnt_6793_, lean_object* v_idx_6794_, lean_object* v___y_6795_, lean_object* v___y_6796_, lean_object* v___y_6797_, lean_object* v___y_6798_){
_start:
{
lean_object* v___x_6800_; 
v___x_6800_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___redArg(v_cctx_6785_, v_env_6786_, v_act_6787_, v_constantsPerTask_6788_, v_n_6789_, v_ngen_6790_, v_tasks_6791_, v_start_6792_, v_cnt_6793_, v_idx_6794_);
return v___x_6800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1___boxed(lean_object* v_00_u03b1_6801_, lean_object* v_cctx_6802_, lean_object* v_env_6803_, lean_object* v_act_6804_, lean_object* v_constantsPerTask_6805_, lean_object* v_n_6806_, lean_object* v_ngen_6807_, lean_object* v_tasks_6808_, lean_object* v_start_6809_, lean_object* v_cnt_6810_, lean_object* v_idx_6811_, lean_object* v___y_6812_, lean_object* v___y_6813_, lean_object* v___y_6814_, lean_object* v___y_6815_, lean_object* v___y_6816_){
_start:
{
lean_object* v_res_6817_; 
v_res_6817_ = l___private_Lean_Meta_LazyDiscrTree_0__Lean_Meta_LazyDiscrTree_createImportedDiscrTree_go___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__1(v_00_u03b1_6801_, v_cctx_6802_, v_env_6803_, v_act_6804_, v_constantsPerTask_6805_, v_n_6806_, v_ngen_6807_, v_tasks_6808_, v_start_6809_, v_cnt_6810_, v_idx_6811_, v___y_6812_, v___y_6813_, v___y_6814_, v___y_6815_);
lean_dec(v___y_6815_);
lean_dec_ref(v___y_6814_);
lean_dec(v___y_6813_);
lean_dec_ref(v___y_6812_);
lean_dec(v_constantsPerTask_6805_);
return v_res_6817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(lean_object* v_00_u03b1_6818_, lean_object* v_z_6819_, lean_object* v_tasks_6820_){
_start:
{
lean_object* v___x_6821_; 
v___x_6821_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___redArg(v_z_6819_, v_tasks_6820_);
return v___x_6821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2___boxed(lean_object* v_00_u03b1_6822_, lean_object* v_z_6823_, lean_object* v_tasks_6824_){
_start:
{
lean_object* v_res_6825_; 
v_res_6825_ = l_Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2(v_00_u03b1_6822_, v_z_6823_, v_tasks_6824_);
lean_dec_ref(v_tasks_6824_);
return v_res_6825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(lean_object* v_00_u03b1_6826_, lean_object* v_as_6827_, size_t v_i_6828_, size_t v_stop_6829_, lean_object* v_b_6830_){
_start:
{
lean_object* v___x_6831_; 
v___x_6831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___redArg(v_as_6827_, v_i_6828_, v_stop_6829_, v_b_6830_);
return v___x_6831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b1_6832_, lean_object* v_as_6833_, lean_object* v_i_6834_, lean_object* v_stop_6835_, lean_object* v_b_6836_){
_start:
{
size_t v_i_boxed_6837_; size_t v_stop_boxed_6838_; lean_object* v_res_6839_; 
v_i_boxed_6837_ = lean_unbox_usize(v_i_6834_);
lean_dec(v_i_6834_);
v_stop_boxed_6838_ = lean_unbox_usize(v_stop_6835_);
lean_dec(v_stop_6835_);
v_res_6839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_combineGet___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__2_spec__5(v_00_u03b1_6832_, v_as_6833_, v_i_boxed_6837_, v_stop_boxed_6838_, v_b_6836_);
lean_dec_ref(v_as_6833_);
return v_res_6839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(lean_object* v___y_6840_){
_start:
{
lean_object* v___x_6842_; lean_object* v_ngen_6843_; lean_object* v_namePrefix_6844_; lean_object* v_idx_6845_; lean_object* v___x_6847_; uint8_t v_isShared_6848_; uint8_t v_isSharedCheck_6875_; 
v___x_6842_ = lean_st_ref_get(v___y_6840_);
v_ngen_6843_ = lean_ctor_get(v___x_6842_, 2);
lean_inc_ref(v_ngen_6843_);
lean_dec(v___x_6842_);
v_namePrefix_6844_ = lean_ctor_get(v_ngen_6843_, 0);
v_idx_6845_ = lean_ctor_get(v_ngen_6843_, 1);
v_isSharedCheck_6875_ = !lean_is_exclusive(v_ngen_6843_);
if (v_isSharedCheck_6875_ == 0)
{
v___x_6847_ = v_ngen_6843_;
v_isShared_6848_ = v_isSharedCheck_6875_;
goto v_resetjp_6846_;
}
else
{
lean_inc(v_idx_6845_);
lean_inc(v_namePrefix_6844_);
lean_dec(v_ngen_6843_);
v___x_6847_ = lean_box(0);
v_isShared_6848_ = v_isSharedCheck_6875_;
goto v_resetjp_6846_;
}
v_resetjp_6846_:
{
lean_object* v___x_6849_; lean_object* v_env_6850_; lean_object* v_nextMacroScope_6851_; lean_object* v_auxDeclNGen_6852_; lean_object* v_traceState_6853_; lean_object* v_cache_6854_; lean_object* v_messages_6855_; lean_object* v_infoState_6856_; lean_object* v_snapshotTasks_6857_; lean_object* v___x_6859_; uint8_t v_isShared_6860_; uint8_t v_isSharedCheck_6873_; 
v___x_6849_ = lean_st_ref_take(v___y_6840_);
v_env_6850_ = lean_ctor_get(v___x_6849_, 0);
v_nextMacroScope_6851_ = lean_ctor_get(v___x_6849_, 1);
v_auxDeclNGen_6852_ = lean_ctor_get(v___x_6849_, 3);
v_traceState_6853_ = lean_ctor_get(v___x_6849_, 4);
v_cache_6854_ = lean_ctor_get(v___x_6849_, 5);
v_messages_6855_ = lean_ctor_get(v___x_6849_, 6);
v_infoState_6856_ = lean_ctor_get(v___x_6849_, 7);
v_snapshotTasks_6857_ = lean_ctor_get(v___x_6849_, 8);
v_isSharedCheck_6873_ = !lean_is_exclusive(v___x_6849_);
if (v_isSharedCheck_6873_ == 0)
{
lean_object* v_unused_6874_; 
v_unused_6874_ = lean_ctor_get(v___x_6849_, 2);
lean_dec(v_unused_6874_);
v___x_6859_ = v___x_6849_;
v_isShared_6860_ = v_isSharedCheck_6873_;
goto v_resetjp_6858_;
}
else
{
lean_inc(v_snapshotTasks_6857_);
lean_inc(v_infoState_6856_);
lean_inc(v_messages_6855_);
lean_inc(v_cache_6854_);
lean_inc(v_traceState_6853_);
lean_inc(v_auxDeclNGen_6852_);
lean_inc(v_nextMacroScope_6851_);
lean_inc(v_env_6850_);
lean_dec(v___x_6849_);
v___x_6859_ = lean_box(0);
v_isShared_6860_ = v_isSharedCheck_6873_;
goto v_resetjp_6858_;
}
v_resetjp_6858_:
{
lean_object* v___x_6861_; lean_object* v___x_6862_; lean_object* v___x_6863_; lean_object* v___x_6865_; 
lean_inc(v_idx_6845_);
lean_inc(v_namePrefix_6844_);
v___x_6861_ = l_Lean_Name_num___override(v_namePrefix_6844_, v_idx_6845_);
v___x_6862_ = lean_unsigned_to_nat(1u);
v___x_6863_ = lean_nat_add(v_idx_6845_, v___x_6862_);
lean_dec(v_idx_6845_);
if (v_isShared_6848_ == 0)
{
lean_ctor_set(v___x_6847_, 1, v___x_6863_);
v___x_6865_ = v___x_6847_;
goto v_reusejp_6864_;
}
else
{
lean_object* v_reuseFailAlloc_6872_; 
v_reuseFailAlloc_6872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6872_, 0, v_namePrefix_6844_);
lean_ctor_set(v_reuseFailAlloc_6872_, 1, v___x_6863_);
v___x_6865_ = v_reuseFailAlloc_6872_;
goto v_reusejp_6864_;
}
v_reusejp_6864_:
{
lean_object* v___x_6867_; 
if (v_isShared_6860_ == 0)
{
lean_ctor_set(v___x_6859_, 2, v___x_6865_);
v___x_6867_ = v___x_6859_;
goto v_reusejp_6866_;
}
else
{
lean_object* v_reuseFailAlloc_6871_; 
v_reuseFailAlloc_6871_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6871_, 0, v_env_6850_);
lean_ctor_set(v_reuseFailAlloc_6871_, 1, v_nextMacroScope_6851_);
lean_ctor_set(v_reuseFailAlloc_6871_, 2, v___x_6865_);
lean_ctor_set(v_reuseFailAlloc_6871_, 3, v_auxDeclNGen_6852_);
lean_ctor_set(v_reuseFailAlloc_6871_, 4, v_traceState_6853_);
lean_ctor_set(v_reuseFailAlloc_6871_, 5, v_cache_6854_);
lean_ctor_set(v_reuseFailAlloc_6871_, 6, v_messages_6855_);
lean_ctor_set(v_reuseFailAlloc_6871_, 7, v_infoState_6856_);
lean_ctor_set(v_reuseFailAlloc_6871_, 8, v_snapshotTasks_6857_);
v___x_6867_ = v_reuseFailAlloc_6871_;
goto v_reusejp_6866_;
}
v_reusejp_6866_:
{
lean_object* v___x_6868_; lean_object* v___x_6869_; lean_object* v___x_6870_; 
v___x_6868_ = lean_st_ref_set(v___y_6840_, v___x_6867_);
v___x_6869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6869_, 0, v___x_6861_);
lean_ctor_set(v___x_6869_, 1, v___x_6862_);
v___x_6870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6870_, 0, v___x_6869_);
return v___x_6870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg___boxed(lean_object* v___y_6876_, lean_object* v___y_6877_){
_start:
{
lean_object* v_res_6878_; 
v_res_6878_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6876_);
lean_dec(v___y_6876_);
return v_res_6878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(lean_object* v___y_6879_, lean_object* v___y_6880_){
_start:
{
lean_object* v___x_6882_; 
v___x_6882_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v___y_6880_);
return v___x_6882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___boxed(lean_object* v___y_6883_, lean_object* v___y_6884_, lean_object* v___y_6885_){
_start:
{
lean_object* v_res_6886_; 
v_res_6886_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1(v___y_6883_, v___y_6884_);
lean_dec(v___y_6884_);
lean_dec_ref(v___y_6883_);
return v_res_6886_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_6887_; lean_object* v___x_6888_; lean_object* v___x_6889_; 
v___x_6887_ = lean_unsigned_to_nat(32u);
v___x_6888_ = lean_mk_empty_array_with_capacity(v___x_6887_);
v___x_6889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6889_, 0, v___x_6888_);
return v___x_6889_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1(void){
_start:
{
size_t v___x_6890_; lean_object* v___x_6891_; lean_object* v___x_6892_; lean_object* v___x_6893_; lean_object* v___x_6894_; lean_object* v___x_6895_; 
v___x_6890_ = ((size_t)5ULL);
v___x_6891_ = lean_unsigned_to_nat(0u);
v___x_6892_ = lean_unsigned_to_nat(32u);
v___x_6893_ = lean_mk_empty_array_with_capacity(v___x_6892_);
v___x_6894_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__0);
v___x_6895_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6895_, 0, v___x_6894_);
lean_ctor_set(v___x_6895_, 1, v___x_6893_);
lean_ctor_set(v___x_6895_, 2, v___x_6891_);
lean_ctor_set(v___x_6895_, 3, v___x_6891_);
lean_ctor_set_usize(v___x_6895_, 4, v___x_6890_);
return v___x_6895_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2(void){
_start:
{
lean_object* v___x_6896_; lean_object* v___x_6897_; lean_object* v___x_6898_; lean_object* v___x_6899_; 
v___x_6896_ = lean_box(1);
v___x_6897_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__1);
v___x_6898_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__1);
v___x_6899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6899_, 0, v___x_6898_);
lean_ctor_set(v___x_6899_, 1, v___x_6897_);
lean_ctor_set(v___x_6899_, 2, v___x_6896_);
return v___x_6899_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_6900_, lean_object* v___y_6901_, lean_object* v___y_6902_){
_start:
{
lean_object* v___x_6904_; lean_object* v_env_6905_; lean_object* v_options_6906_; lean_object* v___x_6907_; lean_object* v___x_6908_; lean_object* v___x_6909_; lean_object* v___x_6910_; lean_object* v___x_6911_; 
v___x_6904_ = lean_st_ref_get(v___y_6902_);
v_env_6905_ = lean_ctor_get(v___x_6904_, 0);
lean_inc_ref(v_env_6905_);
lean_dec(v___x_6904_);
v_options_6906_ = lean_ctor_get(v___y_6901_, 2);
v___x_6907_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2, &l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2_once, _init_l_Lean_Meta_LazyDiscrTree_addConstImportData___redArg___closed__2);
v___x_6908_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___closed__2);
lean_inc_ref(v_options_6906_);
v___x_6909_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6909_, 0, v_env_6905_);
lean_ctor_set(v___x_6909_, 1, v___x_6907_);
lean_ctor_set(v___x_6909_, 2, v___x_6908_);
lean_ctor_set(v___x_6909_, 3, v_options_6906_);
v___x_6910_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6910_, 0, v___x_6909_);
lean_ctor_set(v___x_6910_, 1, v_msgData_6900_);
v___x_6911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6911_, 0, v___x_6910_);
return v___x_6911_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_6912_, lean_object* v___y_6913_, lean_object* v___y_6914_, lean_object* v___y_6915_){
_start:
{
lean_object* v_res_6916_; 
v_res_6916_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_6912_, v___y_6913_, v___y_6914_);
lean_dec(v___y_6914_);
lean_dec_ref(v___y_6913_);
return v_res_6916_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(lean_object* v_ref_6917_, lean_object* v_msgData_6918_, uint8_t v_severity_6919_, uint8_t v_isSilent_6920_, lean_object* v___y_6921_, lean_object* v___y_6922_){
_start:
{
uint8_t v___y_6925_; lean_object* v___y_6926_; lean_object* v___y_6927_; lean_object* v___y_6928_; uint8_t v___y_6929_; lean_object* v___y_6930_; lean_object* v___y_6931_; lean_object* v___y_6932_; lean_object* v___y_6933_; lean_object* v___y_6961_; uint8_t v___y_6962_; uint8_t v___y_6963_; uint8_t v___y_6964_; lean_object* v___y_6965_; lean_object* v___y_6966_; lean_object* v___y_6967_; lean_object* v___y_6968_; lean_object* v___y_6986_; uint8_t v___y_6987_; uint8_t v___y_6988_; lean_object* v___y_6989_; uint8_t v___y_6990_; lean_object* v___y_6991_; lean_object* v___y_6992_; lean_object* v___y_6993_; lean_object* v___y_6997_; uint8_t v___y_6998_; uint8_t v___y_6999_; lean_object* v___y_7000_; lean_object* v___y_7001_; lean_object* v___y_7002_; uint8_t v___y_7003_; uint8_t v___x_7008_; uint8_t v___y_7010_; lean_object* v___y_7011_; lean_object* v___y_7012_; lean_object* v___y_7013_; lean_object* v___y_7014_; uint8_t v___y_7015_; uint8_t v___y_7016_; uint8_t v___y_7018_; uint8_t v___x_7033_; 
v___x_7008_ = 2;
v___x_7033_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6919_, v___x_7008_);
if (v___x_7033_ == 0)
{
v___y_7018_ = v___x_7033_;
goto v___jp_7017_;
}
else
{
uint8_t v___x_7034_; 
lean_inc_ref(v_msgData_6918_);
v___x_7034_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_6918_);
v___y_7018_ = v___x_7034_;
goto v___jp_7017_;
}
v___jp_6924_:
{
lean_object* v___x_6934_; lean_object* v_currNamespace_6935_; lean_object* v_openDecls_6936_; lean_object* v_env_6937_; lean_object* v_nextMacroScope_6938_; lean_object* v_ngen_6939_; lean_object* v_auxDeclNGen_6940_; lean_object* v_traceState_6941_; lean_object* v_cache_6942_; lean_object* v_messages_6943_; lean_object* v_infoState_6944_; lean_object* v_snapshotTasks_6945_; lean_object* v___x_6947_; uint8_t v_isShared_6948_; uint8_t v_isSharedCheck_6959_; 
v___x_6934_ = lean_st_ref_take(v___y_6933_);
v_currNamespace_6935_ = lean_ctor_get(v___y_6932_, 6);
v_openDecls_6936_ = lean_ctor_get(v___y_6932_, 7);
v_env_6937_ = lean_ctor_get(v___x_6934_, 0);
v_nextMacroScope_6938_ = lean_ctor_get(v___x_6934_, 1);
v_ngen_6939_ = lean_ctor_get(v___x_6934_, 2);
v_auxDeclNGen_6940_ = lean_ctor_get(v___x_6934_, 3);
v_traceState_6941_ = lean_ctor_get(v___x_6934_, 4);
v_cache_6942_ = lean_ctor_get(v___x_6934_, 5);
v_messages_6943_ = lean_ctor_get(v___x_6934_, 6);
v_infoState_6944_ = lean_ctor_get(v___x_6934_, 7);
v_snapshotTasks_6945_ = lean_ctor_get(v___x_6934_, 8);
v_isSharedCheck_6959_ = !lean_is_exclusive(v___x_6934_);
if (v_isSharedCheck_6959_ == 0)
{
v___x_6947_ = v___x_6934_;
v_isShared_6948_ = v_isSharedCheck_6959_;
goto v_resetjp_6946_;
}
else
{
lean_inc(v_snapshotTasks_6945_);
lean_inc(v_infoState_6944_);
lean_inc(v_messages_6943_);
lean_inc(v_cache_6942_);
lean_inc(v_traceState_6941_);
lean_inc(v_auxDeclNGen_6940_);
lean_inc(v_ngen_6939_);
lean_inc(v_nextMacroScope_6938_);
lean_inc(v_env_6937_);
lean_dec(v___x_6934_);
v___x_6947_ = lean_box(0);
v_isShared_6948_ = v_isSharedCheck_6959_;
goto v_resetjp_6946_;
}
v_resetjp_6946_:
{
lean_object* v___x_6949_; lean_object* v___x_6950_; lean_object* v___x_6951_; lean_object* v___x_6952_; lean_object* v___x_6954_; 
lean_inc(v_openDecls_6936_);
lean_inc(v_currNamespace_6935_);
v___x_6949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6949_, 0, v_currNamespace_6935_);
lean_ctor_set(v___x_6949_, 1, v_openDecls_6936_);
v___x_6950_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_6950_, 0, v___x_6949_);
lean_ctor_set(v___x_6950_, 1, v___y_6928_);
lean_inc_ref(v___y_6927_);
lean_inc_ref(v___y_6930_);
v___x_6951_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_6951_, 0, v___y_6930_);
lean_ctor_set(v___x_6951_, 1, v___y_6931_);
lean_ctor_set(v___x_6951_, 2, v___y_6926_);
lean_ctor_set(v___x_6951_, 3, v___y_6927_);
lean_ctor_set(v___x_6951_, 4, v___x_6950_);
lean_ctor_set_uint8(v___x_6951_, sizeof(void*)*5, v___y_6925_);
lean_ctor_set_uint8(v___x_6951_, sizeof(void*)*5 + 1, v___y_6929_);
lean_ctor_set_uint8(v___x_6951_, sizeof(void*)*5 + 2, v_isSilent_6920_);
v___x_6952_ = l_Lean_MessageLog_add(v___x_6951_, v_messages_6943_);
if (v_isShared_6948_ == 0)
{
lean_ctor_set(v___x_6947_, 6, v___x_6952_);
v___x_6954_ = v___x_6947_;
goto v_reusejp_6953_;
}
else
{
lean_object* v_reuseFailAlloc_6958_; 
v_reuseFailAlloc_6958_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6958_, 0, v_env_6937_);
lean_ctor_set(v_reuseFailAlloc_6958_, 1, v_nextMacroScope_6938_);
lean_ctor_set(v_reuseFailAlloc_6958_, 2, v_ngen_6939_);
lean_ctor_set(v_reuseFailAlloc_6958_, 3, v_auxDeclNGen_6940_);
lean_ctor_set(v_reuseFailAlloc_6958_, 4, v_traceState_6941_);
lean_ctor_set(v_reuseFailAlloc_6958_, 5, v_cache_6942_);
lean_ctor_set(v_reuseFailAlloc_6958_, 6, v___x_6952_);
lean_ctor_set(v_reuseFailAlloc_6958_, 7, v_infoState_6944_);
lean_ctor_set(v_reuseFailAlloc_6958_, 8, v_snapshotTasks_6945_);
v___x_6954_ = v_reuseFailAlloc_6958_;
goto v_reusejp_6953_;
}
v_reusejp_6953_:
{
lean_object* v___x_6955_; lean_object* v___x_6956_; lean_object* v___x_6957_; 
v___x_6955_ = lean_st_ref_set(v___y_6933_, v___x_6954_);
v___x_6956_ = lean_box(0);
v___x_6957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6957_, 0, v___x_6956_);
return v___x_6957_;
}
}
}
v___jp_6960_:
{
lean_object* v___x_6969_; lean_object* v___x_6970_; lean_object* v_a_6971_; lean_object* v___x_6973_; uint8_t v_isShared_6974_; uint8_t v_isSharedCheck_6984_; 
v___x_6969_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_6918_);
v___x_6970_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4_spec__5(v___x_6969_, v___y_6921_, v___y_6922_);
v_a_6971_ = lean_ctor_get(v___x_6970_, 0);
v_isSharedCheck_6984_ = !lean_is_exclusive(v___x_6970_);
if (v_isSharedCheck_6984_ == 0)
{
v___x_6973_ = v___x_6970_;
v_isShared_6974_ = v_isSharedCheck_6984_;
goto v_resetjp_6972_;
}
else
{
lean_inc(v_a_6971_);
lean_dec(v___x_6970_);
v___x_6973_ = lean_box(0);
v_isShared_6974_ = v_isSharedCheck_6984_;
goto v_resetjp_6972_;
}
v_resetjp_6972_:
{
lean_object* v___x_6975_; lean_object* v___x_6976_; lean_object* v___x_6977_; lean_object* v___x_6978_; 
lean_inc_ref_n(v___y_6965_, 2);
v___x_6975_ = l_Lean_FileMap_toPosition(v___y_6965_, v___y_6967_);
lean_dec(v___y_6967_);
v___x_6976_ = l_Lean_FileMap_toPosition(v___y_6965_, v___y_6968_);
lean_dec(v___y_6968_);
v___x_6977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6977_, 0, v___x_6976_);
v___x_6978_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___closed__0));
if (v___y_6962_ == 0)
{
lean_del_object(v___x_6973_);
lean_dec_ref(v___y_6961_);
v___y_6925_ = v___y_6963_;
v___y_6926_ = v___x_6977_;
v___y_6927_ = v___x_6978_;
v___y_6928_ = v_a_6971_;
v___y_6929_ = v___y_6964_;
v___y_6930_ = v___y_6966_;
v___y_6931_ = v___x_6975_;
v___y_6932_ = v___y_6921_;
v___y_6933_ = v___y_6922_;
goto v___jp_6924_;
}
else
{
uint8_t v___x_6979_; 
lean_inc(v_a_6971_);
v___x_6979_ = l_Lean_MessageData_hasTag(v___y_6961_, v_a_6971_);
if (v___x_6979_ == 0)
{
lean_object* v___x_6980_; lean_object* v___x_6982_; 
lean_dec_ref(v___x_6977_);
lean_dec_ref(v___x_6975_);
lean_dec(v_a_6971_);
v___x_6980_ = lean_box(0);
if (v_isShared_6974_ == 0)
{
lean_ctor_set(v___x_6973_, 0, v___x_6980_);
v___x_6982_ = v___x_6973_;
goto v_reusejp_6981_;
}
else
{
lean_object* v_reuseFailAlloc_6983_; 
v_reuseFailAlloc_6983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6983_, 0, v___x_6980_);
v___x_6982_ = v_reuseFailAlloc_6983_;
goto v_reusejp_6981_;
}
v_reusejp_6981_:
{
return v___x_6982_;
}
}
else
{
lean_del_object(v___x_6973_);
v___y_6925_ = v___y_6963_;
v___y_6926_ = v___x_6977_;
v___y_6927_ = v___x_6978_;
v___y_6928_ = v_a_6971_;
v___y_6929_ = v___y_6964_;
v___y_6930_ = v___y_6966_;
v___y_6931_ = v___x_6975_;
v___y_6932_ = v___y_6921_;
v___y_6933_ = v___y_6922_;
goto v___jp_6924_;
}
}
}
}
v___jp_6985_:
{
lean_object* v___x_6994_; 
v___x_6994_ = l_Lean_Syntax_getTailPos_x3f(v___y_6992_, v___y_6987_);
lean_dec(v___y_6992_);
if (lean_obj_tag(v___x_6994_) == 0)
{
lean_inc(v___y_6993_);
v___y_6961_ = v___y_6986_;
v___y_6962_ = v___y_6988_;
v___y_6963_ = v___y_6987_;
v___y_6964_ = v___y_6990_;
v___y_6965_ = v___y_6989_;
v___y_6966_ = v___y_6991_;
v___y_6967_ = v___y_6993_;
v___y_6968_ = v___y_6993_;
goto v___jp_6960_;
}
else
{
lean_object* v_val_6995_; 
v_val_6995_ = lean_ctor_get(v___x_6994_, 0);
lean_inc(v_val_6995_);
lean_dec_ref(v___x_6994_);
v___y_6961_ = v___y_6986_;
v___y_6962_ = v___y_6988_;
v___y_6963_ = v___y_6987_;
v___y_6964_ = v___y_6990_;
v___y_6965_ = v___y_6989_;
v___y_6966_ = v___y_6991_;
v___y_6967_ = v___y_6993_;
v___y_6968_ = v_val_6995_;
goto v___jp_6960_;
}
}
v___jp_6996_:
{
lean_object* v_ref_7004_; lean_object* v___x_7005_; 
v_ref_7004_ = l_Lean_replaceRef(v_ref_6917_, v___y_7002_);
v___x_7005_ = l_Lean_Syntax_getPos_x3f(v_ref_7004_, v___y_6999_);
if (lean_obj_tag(v___x_7005_) == 0)
{
lean_object* v___x_7006_; 
v___x_7006_ = lean_unsigned_to_nat(0u);
v___y_6986_ = v___y_6997_;
v___y_6987_ = v___y_6999_;
v___y_6988_ = v___y_6998_;
v___y_6989_ = v___y_7000_;
v___y_6990_ = v___y_7003_;
v___y_6991_ = v___y_7001_;
v___y_6992_ = v_ref_7004_;
v___y_6993_ = v___x_7006_;
goto v___jp_6985_;
}
else
{
lean_object* v_val_7007_; 
v_val_7007_ = lean_ctor_get(v___x_7005_, 0);
lean_inc(v_val_7007_);
lean_dec_ref(v___x_7005_);
v___y_6986_ = v___y_6997_;
v___y_6987_ = v___y_6999_;
v___y_6988_ = v___y_6998_;
v___y_6989_ = v___y_7000_;
v___y_6990_ = v___y_7003_;
v___y_6991_ = v___y_7001_;
v___y_6992_ = v_ref_7004_;
v___y_6993_ = v_val_7007_;
goto v___jp_6985_;
}
}
v___jp_7009_:
{
if (v___y_7016_ == 0)
{
v___y_6997_ = v___y_7014_;
v___y_6998_ = v___y_7010_;
v___y_6999_ = v___y_7015_;
v___y_7000_ = v___y_7011_;
v___y_7001_ = v___y_7013_;
v___y_7002_ = v___y_7012_;
v___y_7003_ = v_severity_6919_;
goto v___jp_6996_;
}
else
{
v___y_6997_ = v___y_7014_;
v___y_6998_ = v___y_7010_;
v___y_6999_ = v___y_7015_;
v___y_7000_ = v___y_7011_;
v___y_7001_ = v___y_7013_;
v___y_7002_ = v___y_7012_;
v___y_7003_ = v___x_7008_;
goto v___jp_6996_;
}
}
v___jp_7017_:
{
if (v___y_7018_ == 0)
{
lean_object* v_fileName_7019_; lean_object* v_fileMap_7020_; lean_object* v_options_7021_; lean_object* v_ref_7022_; uint8_t v_suppressElabErrors_7023_; lean_object* v___x_7024_; lean_object* v___x_7025_; lean_object* v___f_7026_; uint8_t v___x_7027_; uint8_t v___x_7028_; 
v_fileName_7019_ = lean_ctor_get(v___y_6921_, 0);
v_fileMap_7020_ = lean_ctor_get(v___y_6921_, 1);
v_options_7021_ = lean_ctor_get(v___y_6921_, 2);
v_ref_7022_ = lean_ctor_get(v___y_6921_, 5);
v_suppressElabErrors_7023_ = lean_ctor_get_uint8(v___y_6921_, sizeof(void*)*14 + 1);
v___x_7024_ = lean_box(v___y_7018_);
v___x_7025_ = lean_box(v_suppressElabErrors_7023_);
v___f_7026_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createImportedDiscrTree___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__0_spec__0_spec__2_spec__3_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_7026_, 0, v___x_7024_);
lean_closure_set(v___f_7026_, 1, v___x_7025_);
v___x_7027_ = 1;
v___x_7028_ = l_Lean_instBEqMessageSeverity_beq(v_severity_6919_, v___x_7027_);
if (v___x_7028_ == 0)
{
v___y_7010_ = v_suppressElabErrors_7023_;
v___y_7011_ = v_fileMap_7020_;
v___y_7012_ = v_ref_7022_;
v___y_7013_ = v_fileName_7019_;
v___y_7014_ = v___f_7026_;
v___y_7015_ = v___y_7018_;
v___y_7016_ = v___x_7028_;
goto v___jp_7009_;
}
else
{
lean_object* v___x_7029_; uint8_t v___x_7030_; 
v___x_7029_ = l_Lean_warningAsError;
v___x_7030_ = l_Lean_Option_get___at___00Lean_Meta_LazyDiscrTree_addConstImportData_spec__0(v_options_7021_, v___x_7029_);
v___y_7010_ = v_suppressElabErrors_7023_;
v___y_7011_ = v_fileMap_7020_;
v___y_7012_ = v_ref_7022_;
v___y_7013_ = v_fileName_7019_;
v___y_7014_ = v___f_7026_;
v___y_7015_ = v___y_7018_;
v___y_7016_ = v___x_7030_;
goto v___jp_7009_;
}
}
else
{
lean_object* v___x_7031_; lean_object* v___x_7032_; 
lean_dec_ref(v_msgData_6918_);
v___x_7031_ = lean_box(0);
v___x_7032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7032_, 0, v___x_7031_);
return v___x_7032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_ref_7035_, lean_object* v_msgData_7036_, lean_object* v_severity_7037_, lean_object* v_isSilent_7038_, lean_object* v___y_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_){
_start:
{
uint8_t v_severity_boxed_7042_; uint8_t v_isSilent_boxed_7043_; lean_object* v_res_7044_; 
v_severity_boxed_7042_ = lean_unbox(v_severity_7037_);
v_isSilent_boxed_7043_ = lean_unbox(v_isSilent_7038_);
v_res_7044_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_7035_, v_msgData_7036_, v_severity_boxed_7042_, v_isSilent_boxed_7043_, v___y_7039_, v___y_7040_);
lean_dec(v___y_7040_);
lean_dec_ref(v___y_7039_);
lean_dec(v_ref_7035_);
return v_res_7044_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(lean_object* v_msgData_7045_, uint8_t v_severity_7046_, uint8_t v_isSilent_7047_, lean_object* v___y_7048_, lean_object* v___y_7049_){
_start:
{
lean_object* v_ref_7051_; lean_object* v___x_7052_; 
v_ref_7051_ = lean_ctor_get(v___y_7048_, 5);
v___x_7052_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2_spec__4(v_ref_7051_, v_msgData_7045_, v_severity_7046_, v_isSilent_7047_, v___y_7048_, v___y_7049_);
return v___x_7052_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_7053_, lean_object* v_severity_7054_, lean_object* v_isSilent_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_, lean_object* v___y_7058_){
_start:
{
uint8_t v_severity_boxed_7059_; uint8_t v_isSilent_boxed_7060_; lean_object* v_res_7061_; 
v_severity_boxed_7059_ = lean_unbox(v_severity_7054_);
v_isSilent_boxed_7060_ = lean_unbox(v_isSilent_7055_);
v_res_7061_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_7053_, v_severity_boxed_7059_, v_isSilent_boxed_7060_, v___y_7056_, v___y_7057_);
lean_dec(v___y_7057_);
lean_dec_ref(v___y_7056_);
return v_res_7061_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(lean_object* v_msgData_7062_, lean_object* v___y_7063_, lean_object* v___y_7064_){
_start:
{
uint8_t v___x_7066_; uint8_t v___x_7067_; lean_object* v___x_7068_; 
v___x_7066_ = 2;
v___x_7067_ = 0;
v___x_7068_ = l_Lean_log___at___00Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0_spec__2(v_msgData_7062_, v___x_7066_, v___x_7067_, v___y_7063_, v___y_7064_);
return v___x_7068_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0___boxed(lean_object* v_msgData_7069_, lean_object* v___y_7070_, lean_object* v___y_7071_, lean_object* v___y_7072_){
_start:
{
lean_object* v_res_7073_; 
v_res_7073_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v_msgData_7069_, v___y_7070_, v___y_7071_);
lean_dec(v___y_7071_);
lean_dec_ref(v___y_7070_);
return v_res_7073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(lean_object* v_f_7074_, lean_object* v___y_7075_, lean_object* v___y_7076_){
_start:
{
lean_object* v_module_7078_; lean_object* v_const_7079_; lean_object* v_exception_7080_; lean_object* v___x_7081_; lean_object* v___x_7082_; lean_object* v___x_7083_; lean_object* v___x_7084_; lean_object* v___x_7085_; lean_object* v___x_7086_; lean_object* v___x_7087_; lean_object* v___x_7088_; lean_object* v___x_7089_; lean_object* v___x_7090_; lean_object* v___x_7091_; lean_object* v___x_7092_; 
v_module_7078_ = lean_ctor_get(v_f_7074_, 0);
lean_inc(v_module_7078_);
v_const_7079_ = lean_ctor_get(v_f_7074_, 1);
lean_inc(v_const_7079_);
v_exception_7080_ = lean_ctor_get(v_f_7074_, 2);
lean_inc_ref(v_exception_7080_);
lean_dec_ref(v_f_7074_);
v___x_7081_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__1);
v___x_7082_ = l_Lean_MessageData_ofName(v_const_7079_);
v___x_7083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7083_, 0, v___x_7081_);
lean_ctor_set(v___x_7083_, 1, v___x_7082_);
v___x_7084_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__3);
v___x_7085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7085_, 0, v___x_7083_);
lean_ctor_set(v___x_7085_, 1, v___x_7084_);
v___x_7086_ = l_Lean_MessageData_ofName(v_module_7078_);
v___x_7087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7087_, 0, v___x_7085_);
lean_ctor_set(v___x_7087_, 1, v___x_7086_);
v___x_7088_ = lean_obj_once(&l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5, &l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5_once, _init_l_Lean_Meta_LazyDiscrTree_logImportFailure___redArg___closed__5);
v___x_7089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7089_, 0, v___x_7087_);
lean_ctor_set(v___x_7089_, 1, v___x_7088_);
v___x_7090_ = l_Lean_Exception_toMessageData(v_exception_7080_);
v___x_7091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7091_, 0, v___x_7089_);
lean_ctor_set(v___x_7091_, 1, v___x_7090_);
v___x_7092_ = l_Lean_logError___at___00Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0_spec__0(v___x_7091_, v___y_7075_, v___y_7076_);
return v___x_7092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0___boxed(lean_object* v_f_7093_, lean_object* v___y_7094_, lean_object* v___y_7095_, lean_object* v___y_7096_){
_start:
{
lean_object* v_res_7097_; 
v_res_7097_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v_f_7093_, v___y_7094_, v___y_7095_);
lean_dec(v___y_7095_);
lean_dec_ref(v___y_7094_);
return v_res_7097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(lean_object* v_as_7098_, size_t v_i_7099_, size_t v_stop_7100_, lean_object* v_b_7101_, lean_object* v___y_7102_, lean_object* v___y_7103_){
_start:
{
uint8_t v___x_7105_; 
v___x_7105_ = lean_usize_dec_eq(v_i_7099_, v_stop_7100_);
if (v___x_7105_ == 0)
{
lean_object* v___x_7106_; lean_object* v___x_7107_; 
v___x_7106_ = lean_array_uget_borrowed(v_as_7098_, v_i_7099_);
lean_inc(v___x_7106_);
v___x_7107_ = l_Lean_Meta_LazyDiscrTree_logImportFailure___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__0(v___x_7106_, v___y_7102_, v___y_7103_);
if (lean_obj_tag(v___x_7107_) == 0)
{
lean_object* v_a_7108_; size_t v___x_7109_; size_t v___x_7110_; 
v_a_7108_ = lean_ctor_get(v___x_7107_, 0);
lean_inc(v_a_7108_);
lean_dec_ref(v___x_7107_);
v___x_7109_ = ((size_t)1ULL);
v___x_7110_ = lean_usize_add(v_i_7099_, v___x_7109_);
v_i_7099_ = v___x_7110_;
v_b_7101_ = v_a_7108_;
goto _start;
}
else
{
return v___x_7107_;
}
}
else
{
lean_object* v___x_7112_; 
v___x_7112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7112_, 0, v_b_7101_);
return v___x_7112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2___boxed(lean_object* v_as_7113_, lean_object* v_i_7114_, lean_object* v_stop_7115_, lean_object* v_b_7116_, lean_object* v___y_7117_, lean_object* v___y_7118_, lean_object* v___y_7119_){
_start:
{
size_t v_i_boxed_7120_; size_t v_stop_boxed_7121_; lean_object* v_res_7122_; 
v_i_boxed_7120_ = lean_unbox_usize(v_i_7114_);
lean_dec(v_i_7114_);
v_stop_boxed_7121_ = lean_unbox_usize(v_stop_7115_);
lean_dec(v_stop_7115_);
v_res_7122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v_as_7113_, v_i_boxed_7120_, v_stop_boxed_7121_, v_b_7116_, v___y_7117_, v___y_7118_);
lean_dec(v___y_7118_);
lean_dec_ref(v___y_7117_);
lean_dec_ref(v_as_7113_);
return v_res_7122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(lean_object* v_entriesForConst_7123_, lean_object* v_a_7124_, lean_object* v_a_7125_){
_start:
{
lean_object* v___x_7127_; lean_object* v___x_7128_; lean_object* v_a_7129_; lean_object* v___x_7131_; uint8_t v_isShared_7132_; uint8_t v_isSharedCheck_7163_; 
v___x_7127_ = lean_st_ref_get(v_a_7125_);
v___x_7128_ = l_Lean_Meta_LazyDiscrTree_getChildNgen___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__1___redArg(v_a_7125_);
v_a_7129_ = lean_ctor_get(v___x_7128_, 0);
v_isSharedCheck_7163_ = !lean_is_exclusive(v___x_7128_);
if (v_isSharedCheck_7163_ == 0)
{
v___x_7131_ = v___x_7128_;
v_isShared_7132_ = v_isSharedCheck_7163_;
goto v_resetjp_7130_;
}
else
{
lean_inc(v_a_7129_);
lean_dec(v___x_7128_);
v___x_7131_ = lean_box(0);
v_isShared_7132_ = v_isSharedCheck_7163_;
goto v_resetjp_7130_;
}
v_resetjp_7130_:
{
lean_object* v___x_7133_; lean_object* v_env_7134_; lean_object* v___x_7135_; lean_object* v___y_7142_; lean_object* v___x_7151_; lean_object* v___x_7152_; lean_object* v___x_7153_; uint8_t v___x_7154_; 
v___x_7133_ = l_Lean_Meta_LazyDiscrTree_ImportData_new();
v_env_7134_ = lean_ctor_get(v___x_7127_, 0);
lean_inc_ref(v_env_7134_);
lean_dec(v___x_7127_);
lean_inc(v___x_7133_);
lean_inc_ref(v_a_7124_);
v___x_7135_ = l_Lean_Meta_LazyDiscrTree_createLocalPreDiscrTree___redArg(v_a_7124_, v_a_7129_, v_env_7134_, v___x_7133_, v_entriesForConst_7123_);
v___x_7151_ = lean_st_ref_get(v___x_7133_);
lean_dec(v___x_7133_);
v___x_7152_ = lean_unsigned_to_nat(0u);
v___x_7153_ = lean_array_get_size(v___x_7151_);
v___x_7154_ = lean_nat_dec_lt(v___x_7152_, v___x_7153_);
if (v___x_7154_ == 0)
{
lean_dec(v___x_7151_);
goto v___jp_7136_;
}
else
{
lean_object* v___x_7155_; uint8_t v___x_7156_; 
v___x_7155_ = lean_box(0);
v___x_7156_ = lean_nat_dec_le(v___x_7153_, v___x_7153_);
if (v___x_7156_ == 0)
{
if (v___x_7154_ == 0)
{
lean_dec(v___x_7151_);
goto v___jp_7136_;
}
else
{
size_t v___x_7157_; size_t v___x_7158_; lean_object* v___x_7159_; 
v___x_7157_ = ((size_t)0ULL);
v___x_7158_ = lean_usize_of_nat(v___x_7153_);
v___x_7159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7151_, v___x_7157_, v___x_7158_, v___x_7155_, v_a_7124_, v_a_7125_);
lean_dec(v___x_7151_);
v___y_7142_ = v___x_7159_;
goto v___jp_7141_;
}
}
else
{
size_t v___x_7160_; size_t v___x_7161_; lean_object* v___x_7162_; 
v___x_7160_ = ((size_t)0ULL);
v___x_7161_ = lean_usize_of_nat(v___x_7153_);
v___x_7162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_createModuleDiscrTree_spec__2(v___x_7151_, v___x_7160_, v___x_7161_, v___x_7155_, v_a_7124_, v_a_7125_);
lean_dec(v___x_7151_);
v___y_7142_ = v___x_7162_;
goto v___jp_7141_;
}
}
v___jp_7136_:
{
lean_object* v___x_7137_; lean_object* v___x_7139_; 
v___x_7137_ = l_Lean_Meta_LazyDiscrTree_PreDiscrTree_toLazy___redArg(v___x_7135_);
if (v_isShared_7132_ == 0)
{
lean_ctor_set(v___x_7131_, 0, v___x_7137_);
v___x_7139_ = v___x_7131_;
goto v_reusejp_7138_;
}
else
{
lean_object* v_reuseFailAlloc_7140_; 
v_reuseFailAlloc_7140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7140_, 0, v___x_7137_);
v___x_7139_ = v_reuseFailAlloc_7140_;
goto v_reusejp_7138_;
}
v_reusejp_7138_:
{
return v___x_7139_;
}
}
v___jp_7141_:
{
if (lean_obj_tag(v___y_7142_) == 0)
{
lean_dec_ref(v___y_7142_);
goto v___jp_7136_;
}
else
{
lean_object* v_a_7143_; lean_object* v___x_7145_; uint8_t v_isShared_7146_; uint8_t v_isSharedCheck_7150_; 
lean_dec_ref(v___x_7135_);
lean_del_object(v___x_7131_);
v_a_7143_ = lean_ctor_get(v___y_7142_, 0);
v_isSharedCheck_7150_ = !lean_is_exclusive(v___y_7142_);
if (v_isSharedCheck_7150_ == 0)
{
v___x_7145_ = v___y_7142_;
v_isShared_7146_ = v_isSharedCheck_7150_;
goto v_resetjp_7144_;
}
else
{
lean_inc(v_a_7143_);
lean_dec(v___y_7142_);
v___x_7145_ = lean_box(0);
v_isShared_7146_ = v_isSharedCheck_7150_;
goto v_resetjp_7144_;
}
v_resetjp_7144_:
{
lean_object* v___x_7148_; 
if (v_isShared_7146_ == 0)
{
v___x_7148_ = v___x_7145_;
goto v_reusejp_7147_;
}
else
{
lean_object* v_reuseFailAlloc_7149_; 
v_reuseFailAlloc_7149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7149_, 0, v_a_7143_);
v___x_7148_ = v_reuseFailAlloc_7149_;
goto v_reusejp_7147_;
}
v_reusejp_7147_:
{
return v___x_7148_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg___boxed(lean_object* v_entriesForConst_7164_, lean_object* v_a_7165_, lean_object* v_a_7166_, lean_object* v_a_7167_){
_start:
{
lean_object* v_res_7168_; 
v_res_7168_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7164_, v_a_7165_, v_a_7166_);
lean_dec(v_a_7166_);
lean_dec_ref(v_a_7165_);
return v_res_7168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(lean_object* v_00_u03b1_7169_, lean_object* v_entriesForConst_7170_, lean_object* v_a_7171_, lean_object* v_a_7172_){
_start:
{
lean_object* v___x_7174_; 
v___x_7174_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7170_, v_a_7171_, v_a_7172_);
return v___x_7174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___boxed(lean_object* v_00_u03b1_7175_, lean_object* v_entriesForConst_7176_, lean_object* v_a_7177_, lean_object* v_a_7178_, lean_object* v_a_7179_){
_start:
{
lean_object* v_res_7180_; 
v_res_7180_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree(v_00_u03b1_7175_, v_entriesForConst_7176_, v_a_7177_, v_a_7178_);
lean_dec(v_a_7178_);
lean_dec_ref(v_a_7177_);
return v_res_7180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(lean_object* v_entriesForConst_7181_, lean_object* v_droppedEntriesRef_7182_, lean_object* v_droppedKeys_7183_, lean_object* v___y_7184_, lean_object* v___y_7185_, lean_object* v___y_7186_, lean_object* v___y_7187_){
_start:
{
lean_object* v_t_7190_; lean_object* v___x_7193_; 
v___x_7193_ = l_Lean_Meta_LazyDiscrTree_createModuleDiscrTree___redArg(v_entriesForConst_7181_, v___y_7186_, v___y_7187_);
if (lean_obj_tag(v___x_7193_) == 0)
{
if (lean_obj_tag(v_droppedEntriesRef_7182_) == 1)
{
lean_object* v_a_7194_; lean_object* v_val_7195_; lean_object* v___x_7197_; uint8_t v_isShared_7198_; uint8_t v_isSharedCheck_7221_; 
v_a_7194_ = lean_ctor_get(v___x_7193_, 0);
lean_inc(v_a_7194_);
lean_dec_ref(v___x_7193_);
v_val_7195_ = lean_ctor_get(v_droppedEntriesRef_7182_, 0);
v_isSharedCheck_7221_ = !lean_is_exclusive(v_droppedEntriesRef_7182_);
if (v_isSharedCheck_7221_ == 0)
{
v___x_7197_ = v_droppedEntriesRef_7182_;
v_isShared_7198_ = v_isSharedCheck_7221_;
goto v_resetjp_7196_;
}
else
{
lean_inc(v_val_7195_);
lean_dec(v_droppedEntriesRef_7182_);
v___x_7197_ = lean_box(0);
v_isShared_7198_ = v_isSharedCheck_7221_;
goto v_resetjp_7196_;
}
v_resetjp_7196_:
{
lean_object* v___x_7199_; 
v___x_7199_ = l_Lean_Meta_LazyDiscrTree_extractKeys___redArg(v_a_7194_, v_droppedKeys_7183_, v___y_7184_, v___y_7185_, v___y_7186_, v___y_7187_);
if (lean_obj_tag(v___x_7199_) == 0)
{
lean_object* v_a_7200_; lean_object* v_fst_7201_; lean_object* v_snd_7202_; lean_object* v___x_7203_; lean_object* v___y_7205_; 
v_a_7200_ = lean_ctor_get(v___x_7199_, 0);
lean_inc(v_a_7200_);
lean_dec_ref(v___x_7199_);
v_fst_7201_ = lean_ctor_get(v_a_7200_, 0);
lean_inc(v_fst_7201_);
v_snd_7202_ = lean_ctor_get(v_a_7200_, 1);
lean_inc(v_snd_7202_);
lean_dec(v_a_7200_);
v___x_7203_ = lean_st_ref_get(v_val_7195_);
if (lean_obj_tag(v___x_7203_) == 0)
{
lean_object* v___x_7211_; 
v___x_7211_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_instEmptyCollectionTrie___closed__0));
v___y_7205_ = v___x_7211_;
goto v___jp_7204_;
}
else
{
lean_object* v_val_7212_; 
v_val_7212_ = lean_ctor_get(v___x_7203_, 0);
lean_inc(v_val_7212_);
lean_dec_ref(v___x_7203_);
v___y_7205_ = v_val_7212_;
goto v___jp_7204_;
}
v___jp_7204_:
{
lean_object* v___x_7206_; lean_object* v___x_7208_; 
v___x_7206_ = l_Array_append___redArg(v___y_7205_, v_fst_7201_);
lean_dec(v_fst_7201_);
if (v_isShared_7198_ == 0)
{
lean_ctor_set(v___x_7197_, 0, v___x_7206_);
v___x_7208_ = v___x_7197_;
goto v_reusejp_7207_;
}
else
{
lean_object* v_reuseFailAlloc_7210_; 
v_reuseFailAlloc_7210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7210_, 0, v___x_7206_);
v___x_7208_ = v_reuseFailAlloc_7210_;
goto v_reusejp_7207_;
}
v_reusejp_7207_:
{
lean_object* v___x_7209_; 
v___x_7209_ = lean_st_ref_set(v_val_7195_, v___x_7208_);
lean_dec(v_val_7195_);
v_t_7190_ = v_snd_7202_;
goto v___jp_7189_;
}
}
}
else
{
lean_object* v_a_7213_; lean_object* v___x_7215_; uint8_t v_isShared_7216_; uint8_t v_isSharedCheck_7220_; 
lean_del_object(v___x_7197_);
lean_dec(v_val_7195_);
v_a_7213_ = lean_ctor_get(v___x_7199_, 0);
v_isSharedCheck_7220_ = !lean_is_exclusive(v___x_7199_);
if (v_isSharedCheck_7220_ == 0)
{
v___x_7215_ = v___x_7199_;
v_isShared_7216_ = v_isSharedCheck_7220_;
goto v_resetjp_7214_;
}
else
{
lean_inc(v_a_7213_);
lean_dec(v___x_7199_);
v___x_7215_ = lean_box(0);
v_isShared_7216_ = v_isSharedCheck_7220_;
goto v_resetjp_7214_;
}
v_resetjp_7214_:
{
lean_object* v___x_7218_; 
if (v_isShared_7216_ == 0)
{
v___x_7218_ = v___x_7215_;
goto v_reusejp_7217_;
}
else
{
lean_object* v_reuseFailAlloc_7219_; 
v_reuseFailAlloc_7219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7219_, 0, v_a_7213_);
v___x_7218_ = v_reuseFailAlloc_7219_;
goto v_reusejp_7217_;
}
v_reusejp_7217_:
{
return v___x_7218_;
}
}
}
}
}
else
{
lean_object* v_a_7222_; lean_object* v___x_7223_; 
lean_dec(v_droppedEntriesRef_7182_);
v_a_7222_ = lean_ctor_get(v___x_7193_, 0);
lean_inc(v_a_7222_);
lean_dec_ref(v___x_7193_);
v___x_7223_ = l_List_foldlM___at___00Lean_Meta_LazyDiscrTree_dropKeys_spec__0___redArg(v_a_7222_, v_droppedKeys_7183_, v___y_7184_, v___y_7185_, v___y_7186_, v___y_7187_);
if (lean_obj_tag(v___x_7223_) == 0)
{
lean_object* v_a_7224_; 
v_a_7224_ = lean_ctor_get(v___x_7223_, 0);
lean_inc(v_a_7224_);
lean_dec_ref(v___x_7223_);
v_t_7190_ = v_a_7224_;
goto v___jp_7189_;
}
else
{
lean_object* v_a_7225_; lean_object* v___x_7227_; uint8_t v_isShared_7228_; uint8_t v_isSharedCheck_7232_; 
v_a_7225_ = lean_ctor_get(v___x_7223_, 0);
v_isSharedCheck_7232_ = !lean_is_exclusive(v___x_7223_);
if (v_isSharedCheck_7232_ == 0)
{
v___x_7227_ = v___x_7223_;
v_isShared_7228_ = v_isSharedCheck_7232_;
goto v_resetjp_7226_;
}
else
{
lean_inc(v_a_7225_);
lean_dec(v___x_7223_);
v___x_7227_ = lean_box(0);
v_isShared_7228_ = v_isSharedCheck_7232_;
goto v_resetjp_7226_;
}
v_resetjp_7226_:
{
lean_object* v___x_7230_; 
if (v_isShared_7228_ == 0)
{
v___x_7230_ = v___x_7227_;
goto v_reusejp_7229_;
}
else
{
lean_object* v_reuseFailAlloc_7231_; 
v_reuseFailAlloc_7231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7231_, 0, v_a_7225_);
v___x_7230_ = v_reuseFailAlloc_7231_;
goto v_reusejp_7229_;
}
v_reusejp_7229_:
{
return v___x_7230_;
}
}
}
}
}
else
{
lean_object* v_a_7233_; lean_object* v___x_7235_; uint8_t v_isShared_7236_; uint8_t v_isSharedCheck_7240_; 
lean_dec(v_droppedKeys_7183_);
lean_dec(v_droppedEntriesRef_7182_);
v_a_7233_ = lean_ctor_get(v___x_7193_, 0);
v_isSharedCheck_7240_ = !lean_is_exclusive(v___x_7193_);
if (v_isSharedCheck_7240_ == 0)
{
v___x_7235_ = v___x_7193_;
v_isShared_7236_ = v_isSharedCheck_7240_;
goto v_resetjp_7234_;
}
else
{
lean_inc(v_a_7233_);
lean_dec(v___x_7193_);
v___x_7235_ = lean_box(0);
v_isShared_7236_ = v_isSharedCheck_7240_;
goto v_resetjp_7234_;
}
v_resetjp_7234_:
{
lean_object* v___x_7238_; 
if (v_isShared_7236_ == 0)
{
v___x_7238_ = v___x_7235_;
goto v_reusejp_7237_;
}
else
{
lean_object* v_reuseFailAlloc_7239_; 
v_reuseFailAlloc_7239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7239_, 0, v_a_7233_);
v___x_7238_ = v_reuseFailAlloc_7239_;
goto v_reusejp_7237_;
}
v_reusejp_7237_:
{
return v___x_7238_;
}
}
}
v___jp_7189_:
{
lean_object* v___x_7191_; lean_object* v___x_7192_; 
v___x_7191_ = lean_st_mk_ref(v_t_7190_);
v___x_7192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7192_, 0, v___x_7191_);
return v___x_7192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed(lean_object* v_entriesForConst_7241_, lean_object* v_droppedEntriesRef_7242_, lean_object* v_droppedKeys_7243_, lean_object* v___y_7244_, lean_object* v___y_7245_, lean_object* v___y_7246_, lean_object* v___y_7247_, lean_object* v___y_7248_){
_start:
{
lean_object* v_res_7249_; 
v_res_7249_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0(v_entriesForConst_7241_, v_droppedEntriesRef_7242_, v_droppedKeys_7243_, v___y_7244_, v___y_7245_, v___y_7246_, v___y_7247_);
lean_dec(v___y_7247_);
lean_dec_ref(v___y_7246_);
lean_dec(v___y_7245_);
lean_dec_ref(v___y_7244_);
return v_res_7249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object* v_entriesForConst_7251_, lean_object* v_droppedKeys_7252_, lean_object* v_droppedEntriesRef_7253_, lean_object* v_a_7254_, lean_object* v_a_7255_, lean_object* v_a_7256_, lean_object* v_a_7257_){
_start:
{
lean_object* v_options_7259_; lean_object* v___f_7260_; lean_object* v___x_7261_; lean_object* v___x_7262_; lean_object* v___x_7263_; 
v_options_7259_ = lean_ctor_get(v_a_7256_, 2);
v___f_7260_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_7260_, 0, v_entriesForConst_7251_);
lean_closure_set(v___f_7260_, 1, v_droppedEntriesRef_7253_);
lean_closure_set(v___f_7260_, 2, v_droppedKeys_7252_);
v___x_7261_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___closed__0));
v___x_7262_ = lean_box(0);
v___x_7263_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7261_, v_options_7259_, v___f_7260_, v___x_7262_, v_a_7254_, v_a_7255_, v_a_7256_, v_a_7257_);
return v___x_7263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg___boxed(lean_object* v_entriesForConst_7264_, lean_object* v_droppedKeys_7265_, lean_object* v_droppedEntriesRef_7266_, lean_object* v_a_7267_, lean_object* v_a_7268_, lean_object* v_a_7269_, lean_object* v_a_7270_, lean_object* v_a_7271_){
_start:
{
lean_object* v_res_7272_; 
v_res_7272_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7264_, v_droppedKeys_7265_, v_droppedEntriesRef_7266_, v_a_7267_, v_a_7268_, v_a_7269_, v_a_7270_);
lean_dec(v_a_7270_);
lean_dec_ref(v_a_7269_);
lean_dec(v_a_7268_);
lean_dec_ref(v_a_7267_);
return v_res_7272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(lean_object* v_00_u03b1_7273_, lean_object* v_entriesForConst_7274_, lean_object* v_droppedKeys_7275_, lean_object* v_droppedEntriesRef_7276_, lean_object* v_a_7277_, lean_object* v_a_7278_, lean_object* v_a_7279_, lean_object* v_a_7280_){
_start:
{
lean_object* v___x_7282_; 
v___x_7282_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_entriesForConst_7274_, v_droppedKeys_7275_, v_droppedEntriesRef_7276_, v_a_7277_, v_a_7278_, v_a_7279_, v_a_7280_);
return v___x_7282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___boxed(lean_object* v_00_u03b1_7283_, lean_object* v_entriesForConst_7284_, lean_object* v_droppedKeys_7285_, lean_object* v_droppedEntriesRef_7286_, lean_object* v_a_7287_, lean_object* v_a_7288_, lean_object* v_a_7289_, lean_object* v_a_7290_, lean_object* v_a_7291_){
_start:
{
lean_object* v_res_7292_; 
v_res_7292_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef(v_00_u03b1_7283_, v_entriesForConst_7284_, v_droppedKeys_7285_, v_droppedEntriesRef_7286_, v_a_7287_, v_a_7288_, v_a_7289_, v_a_7290_);
lean_dec(v_a_7290_);
lean_dec_ref(v_a_7289_);
lean_dec(v_a_7288_);
lean_dec_ref(v_a_7287_);
return v_res_7292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(lean_object* v_moduleRef_7293_, lean_object* v_ty_7294_, lean_object* v___y_7295_, lean_object* v___y_7296_, lean_object* v___y_7297_, lean_object* v___y_7298_){
_start:
{
lean_object* v___x_7300_; lean_object* v___x_7301_; 
v___x_7300_ = lean_st_ref_get(v_moduleRef_7293_);
v___x_7301_ = l_Lean_Meta_LazyDiscrTree_getMatch___redArg(v___x_7300_, v_ty_7294_, v___y_7295_, v___y_7296_, v___y_7297_, v___y_7298_);
if (lean_obj_tag(v___x_7301_) == 0)
{
lean_object* v_a_7302_; lean_object* v___x_7304_; uint8_t v_isShared_7305_; uint8_t v_isSharedCheck_7312_; 
v_a_7302_ = lean_ctor_get(v___x_7301_, 0);
v_isSharedCheck_7312_ = !lean_is_exclusive(v___x_7301_);
if (v_isSharedCheck_7312_ == 0)
{
v___x_7304_ = v___x_7301_;
v_isShared_7305_ = v_isSharedCheck_7312_;
goto v_resetjp_7303_;
}
else
{
lean_inc(v_a_7302_);
lean_dec(v___x_7301_);
v___x_7304_ = lean_box(0);
v_isShared_7305_ = v_isSharedCheck_7312_;
goto v_resetjp_7303_;
}
v_resetjp_7303_:
{
lean_object* v_fst_7306_; lean_object* v_snd_7307_; lean_object* v___x_7308_; lean_object* v___x_7310_; 
v_fst_7306_ = lean_ctor_get(v_a_7302_, 0);
lean_inc(v_fst_7306_);
v_snd_7307_ = lean_ctor_get(v_a_7302_, 1);
lean_inc(v_snd_7307_);
lean_dec(v_a_7302_);
v___x_7308_ = lean_st_ref_set(v_moduleRef_7293_, v_snd_7307_);
if (v_isShared_7305_ == 0)
{
lean_ctor_set(v___x_7304_, 0, v_fst_7306_);
v___x_7310_ = v___x_7304_;
goto v_reusejp_7309_;
}
else
{
lean_object* v_reuseFailAlloc_7311_; 
v_reuseFailAlloc_7311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7311_, 0, v_fst_7306_);
v___x_7310_ = v_reuseFailAlloc_7311_;
goto v_reusejp_7309_;
}
v_reusejp_7309_:
{
return v___x_7310_;
}
}
}
else
{
lean_object* v_a_7313_; lean_object* v___x_7315_; uint8_t v_isShared_7316_; uint8_t v_isSharedCheck_7320_; 
v_a_7313_ = lean_ctor_get(v___x_7301_, 0);
v_isSharedCheck_7320_ = !lean_is_exclusive(v___x_7301_);
if (v_isSharedCheck_7320_ == 0)
{
v___x_7315_ = v___x_7301_;
v_isShared_7316_ = v_isSharedCheck_7320_;
goto v_resetjp_7314_;
}
else
{
lean_inc(v_a_7313_);
lean_dec(v___x_7301_);
v___x_7315_ = lean_box(0);
v_isShared_7316_ = v_isSharedCheck_7320_;
goto v_resetjp_7314_;
}
v_resetjp_7314_:
{
lean_object* v___x_7318_; 
if (v_isShared_7316_ == 0)
{
v___x_7318_ = v___x_7315_;
goto v_reusejp_7317_;
}
else
{
lean_object* v_reuseFailAlloc_7319_; 
v_reuseFailAlloc_7319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7319_, 0, v_a_7313_);
v___x_7318_ = v_reuseFailAlloc_7319_;
goto v_reusejp_7317_;
}
v_reusejp_7317_:
{
return v___x_7318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed(lean_object* v_moduleRef_7321_, lean_object* v_ty_7322_, lean_object* v___y_7323_, lean_object* v___y_7324_, lean_object* v___y_7325_, lean_object* v___y_7326_, lean_object* v___y_7327_){
_start:
{
lean_object* v_res_7328_; 
v_res_7328_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0(v_moduleRef_7321_, v_ty_7322_, v___y_7323_, v___y_7324_, v___y_7325_, v___y_7326_);
lean_dec(v___y_7326_);
lean_dec_ref(v___y_7325_);
lean_dec(v___y_7324_);
lean_dec_ref(v___y_7323_);
lean_dec(v_moduleRef_7321_);
return v_res_7328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(lean_object* v_moduleRef_7330_, lean_object* v_ty_7331_, lean_object* v_a_7332_, lean_object* v_a_7333_, lean_object* v_a_7334_, lean_object* v_a_7335_){
_start:
{
lean_object* v_options_7337_; lean_object* v___f_7338_; lean_object* v___x_7339_; lean_object* v___x_7340_; lean_object* v___x_7341_; 
v_options_7337_ = lean_ctor_get(v_a_7334_, 2);
v___f_7338_ = lean_alloc_closure((void*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_7338_, 0, v_moduleRef_7330_);
lean_closure_set(v___f_7338_, 1, v_ty_7331_);
v___x_7339_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___closed__0));
v___x_7340_ = lean_box(0);
v___x_7341_ = l_Lean_profileitM___at___00Lean_Meta_LazyDiscrTree_findImportMatches_spec__1___redArg(v___x_7339_, v_options_7337_, v___f_7338_, v___x_7340_, v_a_7332_, v_a_7333_, v_a_7334_, v_a_7335_);
return v___x_7341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg___boxed(lean_object* v_moduleRef_7342_, lean_object* v_ty_7343_, lean_object* v_a_7344_, lean_object* v_a_7345_, lean_object* v_a_7346_, lean_object* v_a_7347_, lean_object* v_a_7348_){
_start:
{
lean_object* v_res_7349_; 
v_res_7349_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7342_, v_ty_7343_, v_a_7344_, v_a_7345_, v_a_7346_, v_a_7347_);
lean_dec(v_a_7347_);
lean_dec_ref(v_a_7346_);
lean_dec(v_a_7345_);
lean_dec_ref(v_a_7344_);
return v_res_7349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches(lean_object* v_00_u03b1_7350_, lean_object* v_moduleRef_7351_, lean_object* v_ty_7352_, lean_object* v_a_7353_, lean_object* v_a_7354_, lean_object* v_a_7355_, lean_object* v_a_7356_){
_start:
{
lean_object* v___x_7358_; 
v___x_7358_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleRef_7351_, v_ty_7352_, v_a_7353_, v_a_7354_, v_a_7355_, v_a_7356_);
return v___x_7358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findModuleMatches___boxed(lean_object* v_00_u03b1_7359_, lean_object* v_moduleRef_7360_, lean_object* v_ty_7361_, lean_object* v_a_7362_, lean_object* v_a_7363_, lean_object* v_a_7364_, lean_object* v_a_7365_, lean_object* v_a_7366_){
_start:
{
lean_object* v_res_7367_; 
v_res_7367_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches(v_00_u03b1_7359_, v_moduleRef_7360_, v_ty_7361_, v_a_7362_, v_a_7363_, v_a_7364_, v_a_7365_);
lean_dec(v_a_7365_);
lean_dec_ref(v_a_7364_);
lean_dec(v_a_7363_);
lean_dec_ref(v_a_7362_);
return v_res_7367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(lean_object* v_adjustResult_7368_, lean_object* v_j_7369_, size_t v_sz_7370_, size_t v_i_7371_, lean_object* v_bs_7372_){
_start:
{
uint8_t v___x_7373_; 
v___x_7373_ = lean_usize_dec_lt(v_i_7371_, v_sz_7370_);
if (v___x_7373_ == 0)
{
lean_dec(v_j_7369_);
lean_dec(v_adjustResult_7368_);
return v_bs_7372_;
}
else
{
lean_object* v_v_7374_; lean_object* v___x_7375_; lean_object* v_bs_x27_7376_; lean_object* v___x_7377_; size_t v___x_7378_; size_t v___x_7379_; lean_object* v___x_7380_; 
v_v_7374_ = lean_array_uget(v_bs_7372_, v_i_7371_);
v___x_7375_ = lean_unsigned_to_nat(0u);
v_bs_x27_7376_ = lean_array_uset(v_bs_7372_, v_i_7371_, v___x_7375_);
lean_inc(v_adjustResult_7368_);
lean_inc(v_j_7369_);
v___x_7377_ = lean_apply_2(v_adjustResult_7368_, v_j_7369_, v_v_7374_);
v___x_7378_ = ((size_t)1ULL);
v___x_7379_ = lean_usize_add(v_i_7371_, v___x_7378_);
v___x_7380_ = lean_array_uset(v_bs_x27_7376_, v_i_7371_, v___x_7377_);
v_i_7371_ = v___x_7379_;
v_bs_7372_ = v___x_7380_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg___boxed(lean_object* v_adjustResult_7382_, lean_object* v_j_7383_, lean_object* v_sz_7384_, lean_object* v_i_7385_, lean_object* v_bs_7386_){
_start:
{
size_t v_sz_boxed_7387_; size_t v_i_boxed_7388_; lean_object* v_res_7389_; 
v_sz_boxed_7387_ = lean_unbox_usize(v_sz_7384_);
lean_dec(v_sz_7384_);
v_i_boxed_7388_ = lean_unbox_usize(v_i_7385_);
lean_dec(v_i_7385_);
v_res_7389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7382_, v_j_7383_, v_sz_boxed_7387_, v_i_boxed_7388_, v_bs_7386_);
return v_res_7389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(lean_object* v_adjustResult_7390_, lean_object* v_j_7391_, lean_object* v_as_7392_, size_t v_i_7393_, size_t v_stop_7394_, lean_object* v_b_7395_){
_start:
{
uint8_t v___x_7396_; 
v___x_7396_ = lean_usize_dec_eq(v_i_7393_, v_stop_7394_);
if (v___x_7396_ == 0)
{
lean_object* v___x_7397_; size_t v_sz_7398_; size_t v___x_7399_; lean_object* v___x_7400_; lean_object* v___x_7401_; size_t v___x_7402_; size_t v___x_7403_; 
v___x_7397_ = lean_array_uget_borrowed(v_as_7392_, v_i_7393_);
v_sz_7398_ = lean_array_size(v___x_7397_);
v___x_7399_ = ((size_t)0ULL);
lean_inc(v___x_7397_);
lean_inc(v_j_7391_);
lean_inc(v_adjustResult_7390_);
v___x_7400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7390_, v_j_7391_, v_sz_7398_, v___x_7399_, v___x_7397_);
v___x_7401_ = l_Array_append___redArg(v_b_7395_, v___x_7400_);
lean_dec_ref(v___x_7400_);
v___x_7402_ = ((size_t)1ULL);
v___x_7403_ = lean_usize_add(v_i_7393_, v___x_7402_);
v_i_7393_ = v___x_7403_;
v_b_7395_ = v___x_7401_;
goto _start;
}
else
{
lean_dec(v_j_7391_);
lean_dec(v_adjustResult_7390_);
return v_b_7395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg___boxed(lean_object* v_adjustResult_7405_, lean_object* v_j_7406_, lean_object* v_as_7407_, lean_object* v_i_7408_, lean_object* v_stop_7409_, lean_object* v_b_7410_){
_start:
{
size_t v_i_boxed_7411_; size_t v_stop_boxed_7412_; lean_object* v_res_7413_; 
v_i_boxed_7411_ = lean_unbox_usize(v_i_7408_);
lean_dec(v_i_7408_);
v_stop_boxed_7412_ = lean_unbox_usize(v_stop_7409_);
lean_dec(v_stop_7409_);
v_res_7413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7405_, v_j_7406_, v_as_7407_, v_i_boxed_7411_, v_stop_boxed_7412_, v_b_7410_);
lean_dec_ref(v_as_7407_);
return v_res_7413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(lean_object* v_n_7414_, lean_object* v_aa_7415_, lean_object* v_adjustResult_7416_, lean_object* v_n_7417_, lean_object* v_j_7418_, lean_object* v_a_7419_){
_start:
{
lean_object* v_zero_7420_; uint8_t v_isZero_7421_; 
v_zero_7420_ = lean_unsigned_to_nat(0u);
v_isZero_7421_ = lean_nat_dec_eq(v_j_7418_, v_zero_7420_);
if (v_isZero_7421_ == 1)
{
lean_dec(v_j_7418_);
lean_dec(v_adjustResult_7416_);
return v_a_7419_;
}
else
{
lean_object* v_one_7422_; lean_object* v_n_7423_; lean_object* v___x_7424_; lean_object* v___x_7425_; lean_object* v_j_7426_; lean_object* v_b_7427_; lean_object* v___x_7428_; uint8_t v___x_7429_; 
v_one_7422_ = lean_unsigned_to_nat(1u);
v_n_7423_ = lean_nat_sub(v_j_7418_, v_one_7422_);
v___x_7424_ = lean_nat_sub(v_n_7417_, v_j_7418_);
lean_dec(v_j_7418_);
v___x_7425_ = lean_nat_sub(v_n_7414_, v_one_7422_);
v_j_7426_ = lean_nat_sub(v___x_7425_, v___x_7424_);
lean_dec(v___x_7424_);
lean_dec(v___x_7425_);
v_b_7427_ = lean_array_fget_borrowed(v_aa_7415_, v_j_7426_);
v___x_7428_ = lean_array_get_size(v_b_7427_);
v___x_7429_ = lean_nat_dec_lt(v_zero_7420_, v___x_7428_);
if (v___x_7429_ == 0)
{
lean_dec(v_j_7426_);
v_j_7418_ = v_n_7423_;
goto _start;
}
else
{
uint8_t v___x_7431_; 
v___x_7431_ = lean_nat_dec_le(v___x_7428_, v___x_7428_);
if (v___x_7431_ == 0)
{
if (v___x_7429_ == 0)
{
lean_dec(v_j_7426_);
v_j_7418_ = v_n_7423_;
goto _start;
}
else
{
size_t v___x_7433_; size_t v___x_7434_; lean_object* v___x_7435_; 
v___x_7433_ = ((size_t)0ULL);
v___x_7434_ = lean_usize_of_nat(v___x_7428_);
lean_inc(v_adjustResult_7416_);
v___x_7435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7416_, v_j_7426_, v_b_7427_, v___x_7433_, v___x_7434_, v_a_7419_);
v_j_7418_ = v_n_7423_;
v_a_7419_ = v___x_7435_;
goto _start;
}
}
else
{
size_t v___x_7437_; size_t v___x_7438_; lean_object* v___x_7439_; 
v___x_7437_ = ((size_t)0ULL);
v___x_7438_ = lean_usize_of_nat(v___x_7428_);
lean_inc(v_adjustResult_7416_);
v___x_7439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7416_, v_j_7426_, v_b_7427_, v___x_7437_, v___x_7438_, v_a_7419_);
v_j_7418_ = v_n_7423_;
v_a_7419_ = v___x_7439_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_n_7441_, lean_object* v_aa_7442_, lean_object* v_adjustResult_7443_, lean_object* v_n_7444_, lean_object* v_j_7445_, lean_object* v_a_7446_){
_start:
{
lean_object* v_res_7447_; 
v_res_7447_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7441_, v_aa_7442_, v_adjustResult_7443_, v_n_7444_, v_j_7445_, v_a_7446_);
lean_dec(v_n_7444_);
lean_dec_ref(v_aa_7442_);
lean_dec(v_n_7441_);
return v_res_7447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(lean_object* v_n_7448_, lean_object* v_adjustResult_7449_, lean_object* v_aa_7450_, lean_object* v_n_7451_, lean_object* v_j_7452_, lean_object* v_a_7453_){
_start:
{
lean_object* v_zero_7454_; uint8_t v_isZero_7455_; 
v_zero_7454_ = lean_unsigned_to_nat(0u);
v_isZero_7455_ = lean_nat_dec_eq(v_j_7452_, v_zero_7454_);
if (v_isZero_7455_ == 1)
{
lean_dec(v_adjustResult_7449_);
return v_a_7453_;
}
else
{
lean_object* v_one_7456_; lean_object* v_n_7457_; lean_object* v___x_7458_; lean_object* v___x_7459_; lean_object* v_j_7460_; lean_object* v_b_7461_; lean_object* v___x_7462_; uint8_t v___x_7463_; 
v_one_7456_ = lean_unsigned_to_nat(1u);
v_n_7457_ = lean_nat_sub(v_j_7452_, v_one_7456_);
v___x_7458_ = lean_nat_sub(v_n_7451_, v_j_7452_);
v___x_7459_ = lean_nat_sub(v_n_7448_, v_one_7456_);
v_j_7460_ = lean_nat_sub(v___x_7459_, v___x_7458_);
lean_dec(v___x_7458_);
lean_dec(v___x_7459_);
v_b_7461_ = lean_array_fget_borrowed(v_aa_7450_, v_j_7460_);
v___x_7462_ = lean_array_get_size(v_b_7461_);
v___x_7463_ = lean_nat_dec_lt(v_zero_7454_, v___x_7462_);
if (v___x_7463_ == 0)
{
lean_object* v___x_7464_; 
lean_dec(v_j_7460_);
v___x_7464_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7448_, v_aa_7450_, v_adjustResult_7449_, v_n_7451_, v_n_7457_, v_a_7453_);
return v___x_7464_;
}
else
{
uint8_t v___x_7465_; 
v___x_7465_ = lean_nat_dec_le(v___x_7462_, v___x_7462_);
if (v___x_7465_ == 0)
{
if (v___x_7463_ == 0)
{
lean_object* v___x_7466_; 
lean_dec(v_j_7460_);
v___x_7466_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7448_, v_aa_7450_, v_adjustResult_7449_, v_n_7451_, v_n_7457_, v_a_7453_);
return v___x_7466_;
}
else
{
size_t v___x_7467_; size_t v___x_7468_; lean_object* v___x_7469_; lean_object* v___x_7470_; 
v___x_7467_ = ((size_t)0ULL);
v___x_7468_ = lean_usize_of_nat(v___x_7462_);
lean_inc(v_adjustResult_7449_);
v___x_7469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7449_, v_j_7460_, v_b_7461_, v___x_7467_, v___x_7468_, v_a_7453_);
v___x_7470_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7448_, v_aa_7450_, v_adjustResult_7449_, v_n_7451_, v_n_7457_, v___x_7469_);
return v___x_7470_;
}
}
else
{
size_t v___x_7471_; size_t v___x_7472_; lean_object* v___x_7473_; lean_object* v___x_7474_; 
v___x_7471_ = ((size_t)0ULL);
v___x_7472_ = lean_usize_of_nat(v___x_7462_);
lean_inc(v_adjustResult_7449_);
v___x_7473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7449_, v_j_7460_, v_b_7461_, v___x_7471_, v___x_7472_, v_a_7453_);
v___x_7474_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7448_, v_aa_7450_, v_adjustResult_7449_, v_n_7451_, v_n_7457_, v___x_7473_);
return v___x_7474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg___boxed(lean_object* v_n_7475_, lean_object* v_adjustResult_7476_, lean_object* v_aa_7477_, lean_object* v_n_7478_, lean_object* v_j_7479_, lean_object* v_a_7480_){
_start:
{
lean_object* v_res_7481_; 
v_res_7481_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7475_, v_adjustResult_7476_, v_aa_7477_, v_n_7478_, v_j_7479_, v_a_7480_);
lean_dec(v_j_7479_);
lean_dec(v_n_7478_);
lean_dec_ref(v_aa_7477_);
lean_dec(v_n_7475_);
return v_res_7481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(lean_object* v_adjustResult_7482_, lean_object* v_mr_7483_, lean_object* v_a_7484_){
_start:
{
lean_object* v_n_7485_; lean_object* v___x_7486_; 
v_n_7485_ = lean_array_get_size(v_mr_7483_);
v___x_7486_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7485_, v_adjustResult_7482_, v_mr_7483_, v_n_7485_, v_n_7485_, v_a_7484_);
return v___x_7486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg___boxed(lean_object* v_adjustResult_7487_, lean_object* v_mr_7488_, lean_object* v_a_7489_){
_start:
{
lean_object* v_res_7490_; 
v_res_7490_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7487_, v_mr_7488_, v_a_7489_);
lean_dec_ref(v_mr_7488_);
return v_res_7490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object* v_moduleTreeRef_7491_, lean_object* v_ext_7492_, lean_object* v_addEntry_7493_, lean_object* v_droppedKeys_7494_, lean_object* v_constantsPerTask_7495_, lean_object* v_droppedEntriesRef_7496_, lean_object* v_adjustResult_7497_, lean_object* v_ty_7498_, lean_object* v_a_7499_, lean_object* v_a_7500_, lean_object* v_a_7501_, lean_object* v_a_7502_){
_start:
{
lean_object* v___x_7504_; 
lean_inc_ref(v_ty_7498_);
v___x_7504_ = l_Lean_Meta_LazyDiscrTree_findModuleMatches___redArg(v_moduleTreeRef_7491_, v_ty_7498_, v_a_7499_, v_a_7500_, v_a_7501_, v_a_7502_);
if (lean_obj_tag(v___x_7504_) == 0)
{
lean_object* v_a_7505_; lean_object* v___x_7506_; 
v_a_7505_ = lean_ctor_get(v___x_7504_, 0);
lean_inc(v_a_7505_);
lean_dec_ref(v___x_7504_);
v___x_7506_ = l_Lean_Meta_LazyDiscrTree_findImportMatches___redArg(v_ext_7492_, v_addEntry_7493_, v_droppedKeys_7494_, v_constantsPerTask_7495_, v_droppedEntriesRef_7496_, v_ty_7498_, v_a_7499_, v_a_7500_, v_a_7501_, v_a_7502_);
if (lean_obj_tag(v___x_7506_) == 0)
{
lean_object* v_a_7507_; lean_object* v___x_7509_; uint8_t v_isShared_7510_; uint8_t v_isSharedCheck_7520_; 
v_a_7507_ = lean_ctor_get(v___x_7506_, 0);
v_isSharedCheck_7520_ = !lean_is_exclusive(v___x_7506_);
if (v_isSharedCheck_7520_ == 0)
{
v___x_7509_ = v___x_7506_;
v_isShared_7510_ = v_isSharedCheck_7520_;
goto v_resetjp_7508_;
}
else
{
lean_inc(v_a_7507_);
lean_dec(v___x_7506_);
v___x_7509_ = lean_box(0);
v_isShared_7510_ = v_isSharedCheck_7520_;
goto v_resetjp_7508_;
}
v_resetjp_7508_:
{
lean_object* v___x_7511_; lean_object* v___x_7512_; lean_object* v___x_7513_; lean_object* v___x_7514_; lean_object* v___x_7515_; lean_object* v___x_7516_; lean_object* v___x_7518_; 
v___x_7511_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7505_);
v___x_7512_ = l_Lean_Meta_LazyDiscrTree_MatchResult_size___redArg(v_a_7507_);
v___x_7513_ = lean_nat_add(v___x_7511_, v___x_7512_);
lean_dec(v___x_7512_);
lean_dec(v___x_7511_);
v___x_7514_ = lean_mk_empty_array_with_capacity(v___x_7513_);
lean_dec(v___x_7513_);
lean_inc(v_adjustResult_7497_);
v___x_7515_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7497_, v_a_7505_, v___x_7514_);
lean_dec(v_a_7505_);
v___x_7516_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7497_, v_a_7507_, v___x_7515_);
lean_dec(v_a_7507_);
if (v_isShared_7510_ == 0)
{
lean_ctor_set(v___x_7509_, 0, v___x_7516_);
v___x_7518_ = v___x_7509_;
goto v_reusejp_7517_;
}
else
{
lean_object* v_reuseFailAlloc_7519_; 
v_reuseFailAlloc_7519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7519_, 0, v___x_7516_);
v___x_7518_ = v_reuseFailAlloc_7519_;
goto v_reusejp_7517_;
}
v_reusejp_7517_:
{
return v___x_7518_;
}
}
}
else
{
lean_object* v_a_7521_; lean_object* v___x_7523_; uint8_t v_isShared_7524_; uint8_t v_isSharedCheck_7528_; 
lean_dec(v_a_7505_);
lean_dec(v_adjustResult_7497_);
v_a_7521_ = lean_ctor_get(v___x_7506_, 0);
v_isSharedCheck_7528_ = !lean_is_exclusive(v___x_7506_);
if (v_isSharedCheck_7528_ == 0)
{
v___x_7523_ = v___x_7506_;
v_isShared_7524_ = v_isSharedCheck_7528_;
goto v_resetjp_7522_;
}
else
{
lean_inc(v_a_7521_);
lean_dec(v___x_7506_);
v___x_7523_ = lean_box(0);
v_isShared_7524_ = v_isSharedCheck_7528_;
goto v_resetjp_7522_;
}
v_resetjp_7522_:
{
lean_object* v___x_7526_; 
if (v_isShared_7524_ == 0)
{
v___x_7526_ = v___x_7523_;
goto v_reusejp_7525_;
}
else
{
lean_object* v_reuseFailAlloc_7527_; 
v_reuseFailAlloc_7527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7527_, 0, v_a_7521_);
v___x_7526_ = v_reuseFailAlloc_7527_;
goto v_reusejp_7525_;
}
v_reusejp_7525_:
{
return v___x_7526_;
}
}
}
}
else
{
lean_object* v_a_7529_; lean_object* v___x_7531_; uint8_t v_isShared_7532_; uint8_t v_isSharedCheck_7536_; 
lean_dec_ref(v_ty_7498_);
lean_dec(v_adjustResult_7497_);
lean_dec(v_droppedEntriesRef_7496_);
lean_dec(v_constantsPerTask_7495_);
lean_dec(v_droppedKeys_7494_);
lean_dec_ref(v_addEntry_7493_);
v_a_7529_ = lean_ctor_get(v___x_7504_, 0);
v_isSharedCheck_7536_ = !lean_is_exclusive(v___x_7504_);
if (v_isSharedCheck_7536_ == 0)
{
v___x_7531_ = v___x_7504_;
v_isShared_7532_ = v_isSharedCheck_7536_;
goto v_resetjp_7530_;
}
else
{
lean_inc(v_a_7529_);
lean_dec(v___x_7504_);
v___x_7531_ = lean_box(0);
v_isShared_7532_ = v_isSharedCheck_7536_;
goto v_resetjp_7530_;
}
v_resetjp_7530_:
{
lean_object* v___x_7534_; 
if (v_isShared_7532_ == 0)
{
v___x_7534_ = v___x_7531_;
goto v_reusejp_7533_;
}
else
{
lean_object* v_reuseFailAlloc_7535_; 
v_reuseFailAlloc_7535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7535_, 0, v_a_7529_);
v___x_7534_ = v_reuseFailAlloc_7535_;
goto v_reusejp_7533_;
}
v_reusejp_7533_:
{
return v___x_7534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg___boxed(lean_object* v_moduleTreeRef_7537_, lean_object* v_ext_7538_, lean_object* v_addEntry_7539_, lean_object* v_droppedKeys_7540_, lean_object* v_constantsPerTask_7541_, lean_object* v_droppedEntriesRef_7542_, lean_object* v_adjustResult_7543_, lean_object* v_ty_7544_, lean_object* v_a_7545_, lean_object* v_a_7546_, lean_object* v_a_7547_, lean_object* v_a_7548_, lean_object* v_a_7549_){
_start:
{
lean_object* v_res_7550_; 
v_res_7550_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7537_, v_ext_7538_, v_addEntry_7539_, v_droppedKeys_7540_, v_constantsPerTask_7541_, v_droppedEntriesRef_7542_, v_adjustResult_7543_, v_ty_7544_, v_a_7545_, v_a_7546_, v_a_7547_, v_a_7548_);
lean_dec(v_a_7548_);
lean_dec_ref(v_a_7547_);
lean_dec(v_a_7546_);
lean_dec_ref(v_a_7545_);
lean_dec_ref(v_ext_7538_);
return v_res_7550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt(lean_object* v_00_u03b1_7551_, lean_object* v_00_u03b2_7552_, lean_object* v_moduleTreeRef_7553_, lean_object* v_ext_7554_, lean_object* v_addEntry_7555_, lean_object* v_droppedKeys_7556_, lean_object* v_constantsPerTask_7557_, lean_object* v_droppedEntriesRef_7558_, lean_object* v_adjustResult_7559_, lean_object* v_ty_7560_, lean_object* v_a_7561_, lean_object* v_a_7562_, lean_object* v_a_7563_, lean_object* v_a_7564_){
_start:
{
lean_object* v___x_7566_; 
v___x_7566_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleTreeRef_7553_, v_ext_7554_, v_addEntry_7555_, v_droppedKeys_7556_, v_constantsPerTask_7557_, v_droppedEntriesRef_7558_, v_adjustResult_7559_, v_ty_7560_, v_a_7561_, v_a_7562_, v_a_7563_, v_a_7564_);
return v___x_7566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___boxed(lean_object* v_00_u03b1_7567_, lean_object* v_00_u03b2_7568_, lean_object* v_moduleTreeRef_7569_, lean_object* v_ext_7570_, lean_object* v_addEntry_7571_, lean_object* v_droppedKeys_7572_, lean_object* v_constantsPerTask_7573_, lean_object* v_droppedEntriesRef_7574_, lean_object* v_adjustResult_7575_, lean_object* v_ty_7576_, lean_object* v_a_7577_, lean_object* v_a_7578_, lean_object* v_a_7579_, lean_object* v_a_7580_, lean_object* v_a_7581_){
_start:
{
lean_object* v_res_7582_; 
v_res_7582_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt(v_00_u03b1_7567_, v_00_u03b2_7568_, v_moduleTreeRef_7569_, v_ext_7570_, v_addEntry_7571_, v_droppedKeys_7572_, v_constantsPerTask_7573_, v_droppedEntriesRef_7574_, v_adjustResult_7575_, v_ty_7576_, v_a_7577_, v_a_7578_, v_a_7579_, v_a_7580_);
lean_dec(v_a_7580_);
lean_dec_ref(v_a_7579_);
lean_dec(v_a_7578_);
lean_dec_ref(v_a_7577_);
lean_dec_ref(v_ext_7570_);
return v_res_7582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(lean_object* v_00_u03b1_7583_, lean_object* v_00_u03b2_7584_, lean_object* v_adjustResult_7585_, lean_object* v_mr_7586_, lean_object* v_a_7587_){
_start:
{
lean_object* v___x_7588_; 
v___x_7588_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___redArg(v_adjustResult_7585_, v_mr_7586_, v_a_7587_);
return v___x_7588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0___boxed(lean_object* v_00_u03b1_7589_, lean_object* v_00_u03b2_7590_, lean_object* v_adjustResult_7591_, lean_object* v_mr_7592_, lean_object* v_a_7593_){
_start:
{
lean_object* v_res_7594_; 
v_res_7594_ = l_Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0(v_00_u03b1_7589_, v_00_u03b2_7590_, v_adjustResult_7591_, v_mr_7592_, v_a_7593_);
lean_dec_ref(v_mr_7592_);
return v_res_7594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(lean_object* v_00_u03b1_7595_, lean_object* v_00_u03b2_7596_, lean_object* v_adjustResult_7597_, lean_object* v_j_7598_, size_t v_sz_7599_, size_t v_i_7600_, lean_object* v_bs_7601_){
_start:
{
lean_object* v___x_7602_; 
v___x_7602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___redArg(v_adjustResult_7597_, v_j_7598_, v_sz_7599_, v_i_7600_, v_bs_7601_);
return v___x_7602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0___boxed(lean_object* v_00_u03b1_7603_, lean_object* v_00_u03b2_7604_, lean_object* v_adjustResult_7605_, lean_object* v_j_7606_, lean_object* v_sz_7607_, lean_object* v_i_7608_, lean_object* v_bs_7609_){
_start:
{
size_t v_sz_boxed_7610_; size_t v_i_boxed_7611_; lean_object* v_res_7612_; 
v_sz_boxed_7610_ = lean_unbox_usize(v_sz_7607_);
lean_dec(v_sz_7607_);
v_i_boxed_7611_ = lean_unbox_usize(v_i_7608_);
lean_dec(v_i_7608_);
v_res_7612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__0(v_00_u03b1_7603_, v_00_u03b2_7604_, v_adjustResult_7605_, v_j_7606_, v_sz_boxed_7610_, v_i_boxed_7611_, v_bs_7609_);
return v_res_7612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(lean_object* v_00_u03b1_7613_, lean_object* v_00_u03b2_7614_, lean_object* v_adjustResult_7615_, lean_object* v_j_7616_, lean_object* v_as_7617_, size_t v_i_7618_, size_t v_stop_7619_, lean_object* v_b_7620_){
_start:
{
lean_object* v___x_7621_; 
v___x_7621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___redArg(v_adjustResult_7615_, v_j_7616_, v_as_7617_, v_i_7618_, v_stop_7619_, v_b_7620_);
return v___x_7621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1___boxed(lean_object* v_00_u03b1_7622_, lean_object* v_00_u03b2_7623_, lean_object* v_adjustResult_7624_, lean_object* v_j_7625_, lean_object* v_as_7626_, lean_object* v_i_7627_, lean_object* v_stop_7628_, lean_object* v_b_7629_){
_start:
{
size_t v_i_boxed_7630_; size_t v_stop_boxed_7631_; lean_object* v_res_7632_; 
v_i_boxed_7630_ = lean_unbox_usize(v_i_7627_);
lean_dec(v_i_7627_);
v_stop_boxed_7631_ = lean_unbox_usize(v_stop_7628_);
lean_dec(v_stop_7628_);
v_res_7632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__1(v_00_u03b1_7622_, v_00_u03b2_7623_, v_adjustResult_7624_, v_j_7625_, v_as_7626_, v_i_boxed_7630_, v_stop_boxed_7631_, v_b_7629_);
lean_dec_ref(v_as_7626_);
return v_res_7632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(lean_object* v_00_u03b2_7633_, lean_object* v_n_7634_, lean_object* v_00_u03b1_7635_, lean_object* v_adjustResult_7636_, lean_object* v_aa_7637_, lean_object* v_n_7638_, lean_object* v_j_7639_, lean_object* v_a_7640_, lean_object* v_a_7641_){
_start:
{
lean_object* v___x_7642_; 
v___x_7642_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___redArg(v_n_7634_, v_adjustResult_7636_, v_aa_7637_, v_n_7638_, v_j_7639_, v_a_7641_);
return v___x_7642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2___boxed(lean_object* v_00_u03b2_7643_, lean_object* v_n_7644_, lean_object* v_00_u03b1_7645_, lean_object* v_adjustResult_7646_, lean_object* v_aa_7647_, lean_object* v_n_7648_, lean_object* v_j_7649_, lean_object* v_a_7650_, lean_object* v_a_7651_){
_start:
{
lean_object* v_res_7652_; 
v_res_7652_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2(v_00_u03b2_7643_, v_n_7644_, v_00_u03b1_7645_, v_adjustResult_7646_, v_aa_7647_, v_n_7648_, v_j_7649_, v_a_7650_, v_a_7651_);
lean_dec(v_j_7649_);
lean_dec(v_n_7648_);
lean_dec_ref(v_aa_7647_);
lean_dec(v_n_7644_);
return v_res_7652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_7653_, lean_object* v_n_7654_, lean_object* v_00_u03b1_7655_, lean_object* v_aa_7656_, lean_object* v_adjustResult_7657_, lean_object* v_n_7658_, lean_object* v_j_7659_, lean_object* v_a_7660_, lean_object* v_a_7661_){
_start:
{
lean_object* v___x_7662_; 
v___x_7662_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___redArg(v_n_7654_, v_aa_7656_, v_adjustResult_7657_, v_n_7658_, v_j_7659_, v_a_7661_);
return v___x_7662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b2_7663_, lean_object* v_n_7664_, lean_object* v_00_u03b1_7665_, lean_object* v_aa_7666_, lean_object* v_adjustResult_7667_, lean_object* v_n_7668_, lean_object* v_j_7669_, lean_object* v_a_7670_, lean_object* v_a_7671_){
_start:
{
lean_object* v_res_7672_; 
v_res_7672_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Meta_LazyDiscrTree_MatchResult_appendResultsAux___at___00Lean_Meta_LazyDiscrTree_findMatchesExt_spec__0_spec__2_spec__3(v_00_u03b2_7663_, v_n_7664_, v_00_u03b1_7665_, v_aa_7666_, v_adjustResult_7667_, v_n_7668_, v_j_7669_, v_a_7670_, v_a_7671_);
lean_dec(v_n_7668_);
lean_dec_ref(v_aa_7666_);
lean_dec(v_n_7664_);
return v_res_7672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(lean_object* v_x_7673_, lean_object* v_v_7674_){
_start:
{
lean_inc(v_v_7674_);
return v_v_7674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0___boxed(lean_object* v_x_7675_, lean_object* v_v_7676_){
_start:
{
lean_object* v_res_7677_; 
v_res_7677_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg___lam__0(v_x_7675_, v_v_7676_);
lean_dec(v_v_7676_);
lean_dec(v_x_7675_);
return v_res_7677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object* v_ext_7679_, lean_object* v_addEntry_7680_, lean_object* v_droppedKeys_7681_, lean_object* v_constantsPerTask_7682_, lean_object* v_droppedEntriesRef_7683_, lean_object* v_ty_7684_, lean_object* v_a_7685_, lean_object* v_a_7686_, lean_object* v_a_7687_, lean_object* v_a_7688_){
_start:
{
lean_object* v___x_7690_; 
lean_inc(v_droppedEntriesRef_7683_);
lean_inc(v_droppedKeys_7681_);
lean_inc_ref(v_addEntry_7680_);
v___x_7690_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v_addEntry_7680_, v_droppedKeys_7681_, v_droppedEntriesRef_7683_, v_a_7685_, v_a_7686_, v_a_7687_, v_a_7688_);
if (lean_obj_tag(v___x_7690_) == 0)
{
lean_object* v_a_7691_; lean_object* v___f_7692_; lean_object* v___x_7693_; 
v_a_7691_ = lean_ctor_get(v___x_7690_, 0);
lean_inc(v_a_7691_);
lean_dec_ref(v___x_7690_);
v___f_7692_ = ((lean_object*)(l_Lean_Meta_LazyDiscrTree_findMatches___redArg___closed__0));
v___x_7693_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_a_7691_, v_ext_7679_, v_addEntry_7680_, v_droppedKeys_7681_, v_constantsPerTask_7682_, v_droppedEntriesRef_7683_, v___f_7692_, v_ty_7684_, v_a_7685_, v_a_7686_, v_a_7687_, v_a_7688_);
return v___x_7693_;
}
else
{
lean_object* v_a_7694_; lean_object* v___x_7696_; uint8_t v_isShared_7697_; uint8_t v_isSharedCheck_7701_; 
lean_dec_ref(v_ty_7684_);
lean_dec(v_droppedEntriesRef_7683_);
lean_dec(v_constantsPerTask_7682_);
lean_dec(v_droppedKeys_7681_);
lean_dec_ref(v_addEntry_7680_);
v_a_7694_ = lean_ctor_get(v___x_7690_, 0);
v_isSharedCheck_7701_ = !lean_is_exclusive(v___x_7690_);
if (v_isSharedCheck_7701_ == 0)
{
v___x_7696_ = v___x_7690_;
v_isShared_7697_ = v_isSharedCheck_7701_;
goto v_resetjp_7695_;
}
else
{
lean_inc(v_a_7694_);
lean_dec(v___x_7690_);
v___x_7696_ = lean_box(0);
v_isShared_7697_ = v_isSharedCheck_7701_;
goto v_resetjp_7695_;
}
v_resetjp_7695_:
{
lean_object* v___x_7699_; 
if (v_isShared_7697_ == 0)
{
v___x_7699_ = v___x_7696_;
goto v_reusejp_7698_;
}
else
{
lean_object* v_reuseFailAlloc_7700_; 
v_reuseFailAlloc_7700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7700_, 0, v_a_7694_);
v___x_7699_ = v_reuseFailAlloc_7700_;
goto v_reusejp_7698_;
}
v_reusejp_7698_:
{
return v___x_7699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg___boxed(lean_object* v_ext_7702_, lean_object* v_addEntry_7703_, lean_object* v_droppedKeys_7704_, lean_object* v_constantsPerTask_7705_, lean_object* v_droppedEntriesRef_7706_, lean_object* v_ty_7707_, lean_object* v_a_7708_, lean_object* v_a_7709_, lean_object* v_a_7710_, lean_object* v_a_7711_, lean_object* v_a_7712_){
_start:
{
lean_object* v_res_7713_; 
v_res_7713_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ext_7702_, v_addEntry_7703_, v_droppedKeys_7704_, v_constantsPerTask_7705_, v_droppedEntriesRef_7706_, v_ty_7707_, v_a_7708_, v_a_7709_, v_a_7710_, v_a_7711_);
lean_dec(v_a_7711_);
lean_dec_ref(v_a_7710_);
lean_dec(v_a_7709_);
lean_dec_ref(v_a_7708_);
lean_dec_ref(v_ext_7702_);
return v_res_7713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches(lean_object* v_00_u03b1_7714_, lean_object* v_ext_7715_, lean_object* v_addEntry_7716_, lean_object* v_droppedKeys_7717_, lean_object* v_constantsPerTask_7718_, lean_object* v_droppedEntriesRef_7719_, lean_object* v_ty_7720_, lean_object* v_a_7721_, lean_object* v_a_7722_, lean_object* v_a_7723_, lean_object* v_a_7724_){
_start:
{
lean_object* v___x_7726_; 
v___x_7726_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v_ext_7715_, v_addEntry_7716_, v_droppedKeys_7717_, v_constantsPerTask_7718_, v_droppedEntriesRef_7719_, v_ty_7720_, v_a_7721_, v_a_7722_, v_a_7723_, v_a_7724_);
return v___x_7726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___boxed(lean_object* v_00_u03b1_7727_, lean_object* v_ext_7728_, lean_object* v_addEntry_7729_, lean_object* v_droppedKeys_7730_, lean_object* v_constantsPerTask_7731_, lean_object* v_droppedEntriesRef_7732_, lean_object* v_ty_7733_, lean_object* v_a_7734_, lean_object* v_a_7735_, lean_object* v_a_7736_, lean_object* v_a_7737_, lean_object* v_a_7738_){
_start:
{
lean_object* v_res_7739_; 
v_res_7739_ = l_Lean_Meta_LazyDiscrTree_findMatches(v_00_u03b1_7727_, v_ext_7728_, v_addEntry_7729_, v_droppedKeys_7730_, v_constantsPerTask_7731_, v_droppedEntriesRef_7732_, v_ty_7733_, v_a_7734_, v_a_7735_, v_a_7736_, v_a_7737_);
lean_dec(v_a_7737_);
lean_dec_ref(v_a_7736_);
lean_dec(v_a_7735_);
lean_dec_ref(v_a_7734_);
lean_dec_ref(v_ext_7728_);
return v_res_7739_;
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
