// Lean compiler output
// Module: Lean.Meta.Injective
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Refl import Lean.Meta.Tactic.Assumption import Lean.Meta.SameCtorUtils import Init.Omega import Lean.Meta.Tactic.Injection import Lean.Meta.Tactic.Simp.Attr
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_splitAndCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_Meta_simpExtension;
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_elimOptParam___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optParam"};
static const lean_object* l_Lean_Meta_elimOptParam___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_elimOptParam___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_elimOptParam___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_elimOptParam___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 160, 223, 165, 16, 51, 54, 209)}};
static const lean_object* l_Lean_Meta_elimOptParam___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_elimOptParam___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_elimOptParam___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_elimOptParam___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_elimOptParam___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_elimOptParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_elimOptParam___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_elimOptParam___closed__0 = (const lean_object*)&l_Lean_Meta_elimOptParam___closed__0_value;
static const lean_closure_object l_Lean_Meta_elimOptParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_elimOptParam___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_elimOptParam___closed__1 = (const lean_object*)&l_Lean_Meta_elimOptParam___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unexpected constructor type for `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "failed to prove injectivity theorem for constructor `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "`, use 'set_option genInjectivity false' to disable the generation"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.Injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "_private.Lean.Meta.Injective.0.Lean.Meta.solveEqOfCtorEq"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__5 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__5_value),LEAN_SCALAR_PTR_LITERAL(39, 126, 11, 127, 131, 182, 22, 10)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "solving injectivity goal for "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " with hypothesis "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at\n"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkInjectiveTheoremNameFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor___closed__0 = (const lean_object*)&l_Lean_Meta_mkInjectiveTheoremNameFor___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInjectiveTheoremNameFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 11, 58, 56, 192, 58, 162, 195)}};
static const lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1 = (const lean_object*)&l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "generating `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__0 = (const lean_object*)&l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 235, 155, 31, 77, 126, 235, 172)}};
static const lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1 = (const lean_object*)&l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "unexpected number of goals after applying `Lean.and_imp`"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "injEq_helper"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(167, 111, 180, 146, 132, 58, 155, 57)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "unexpected number of subgoals when proving injective theorem for constructor `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "propIntro"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(189, 136, 38, 165, 207, 169, 133, 34)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "genInjectivity"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(56, 68, 112, 222, 169, 79, 62, 37)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "generate injectivity theorems for inductive datatype constructors. Temporarily (for bootstrapping reasons) also controls the generation of the\n    `ctorIdx` definition."};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 17, 232, 138, 187, 170, 36, 13)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_genInjectivity;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__0;
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__1;
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__2;
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__3;
static const lean_array_object l_Lean_Meta_mkInjectiveTheorems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__4 = (const lean_object*)&l_Lean_Meta_mkInjectiveTheorems___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 101, 109, 194, 24, 99, 201, 78)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(74, 76, 255, 124, 31, 108, 47, 16)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 106, 16, 37, 3, 60, 11, 157)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(3, 239, 173, 245, 77, 160, 209, 24)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 239, 175, 71, 176, 92, 247, 26)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 126, 32, 109, 177, 184, 17, 126)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 151, 10, 103, 183, 199, 62, 165)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(242, 157, 244, 230, 219, 101, 50, 39)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 105, 167, 47, 98, 73, 248, 220)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0_value)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "failed to generate heterogeneous injectivity theorem for `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "noConfusion"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hinj"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_6_ = l_Lean_mkConst(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg(lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
lean_object* v_array_9_; lean_object* v_start_10_; lean_object* v_stop_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_25_; 
v_array_9_ = lean_ctor_get(v_a_7_, 0);
v_start_10_ = lean_ctor_get(v_a_7_, 1);
v_stop_11_ = lean_ctor_get(v_a_7_, 2);
v_isSharedCheck_25_ = !lean_is_exclusive(v_a_7_);
if (v_isSharedCheck_25_ == 0)
{
v___x_13_ = v_a_7_;
v_isShared_14_ = v_isSharedCheck_25_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_stop_11_);
lean_inc(v_start_10_);
lean_inc(v_array_9_);
lean_dec(v_a_7_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_25_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
uint8_t v___x_15_; 
v___x_15_ = lean_nat_dec_lt(v_start_10_, v_stop_11_);
if (v___x_15_ == 0)
{
lean_del_object(v___x_13_);
lean_dec(v_stop_11_);
lean_dec(v_start_10_);
lean_dec_ref(v_array_9_);
return v_b_8_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_19_; 
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_add(v_start_10_, v___x_16_);
lean_inc_ref(v_array_9_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_17_);
v___x_19_ = v___x_13_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_array_9_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_24_, 2, v_stop_11_);
v___x_19_ = v_reuseFailAlloc_24_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_array_fget(v_array_9_, v_start_10_);
lean_dec(v_start_10_);
lean_dec_ref(v_array_9_);
v___x_21_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2);
v___x_22_ = l_Lean_mkAppB(v___x_21_, v___x_20_, v_b_8_);
v_a_7_ = v___x_19_;
v_b_8_ = v___x_22_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(lean_object* v_args_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_27_ = lean_array_get_size(v_args_26_);
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_dec_eq(v___x_27_, v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v_result_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_30_ = l_Lean_instInhabitedExpr;
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_sub(v___x_27_, v___x_31_);
v_result_33_ = lean_array_get(v___x_30_, v_args_26_, v___x_32_);
lean_dec(v___x_32_);
v___x_34_ = l_Array_reverse___redArg(v_args_26_);
v___x_35_ = lean_array_get_size(v___x_34_);
v___x_36_ = l_Array_toSubarray___redArg(v___x_34_, v___x_31_, v___x_35_);
v___x_37_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg(v___x_36_, v_result_33_);
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; 
lean_dec_ref(v_args_26_);
v___x_39_ = lean_box(0);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0(lean_object* v_inst_40_, lean_object* v_R_41_, lean_object* v_a_42_, lean_object* v_b_43_, lean_object* v_c_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg(v_a_42_, v_b_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__0(lean_object* v_e_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = ((lean_object*)(l_Lean_Meta_elimOptParam___lam__0___closed__1));
v___x_56_ = lean_unsigned_to_nat(2u);
v___x_57_ = l_Lean_Expr_isAppOfArity(v_e_51_, v___x_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Meta_elimOptParam___lam__0___closed__2));
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_60_ = l_Lean_Expr_getAppNumArgs(v_e_51_);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_sub(v___x_60_, v___x_61_);
lean_dec(v___x_60_);
v___x_63_ = l_Lean_Expr_getRevArg_x21(v_e_51_, v___x_62_);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__0___boxed(lean_object* v_e_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Meta_elimOptParam___lam__0(v_e_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec_ref(v_e_66_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__1(lean_object* v_e_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_e_71_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__1___boxed(lean_object* v_e_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_elimOptParam___lam__1(v_e_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
return v_x_82_;
}
else
{
lean_object* v_key_84_; lean_object* v_value_85_; lean_object* v_tail_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_109_; 
v_key_84_ = lean_ctor_get(v_x_83_, 0);
v_value_85_ = lean_ctor_get(v_x_83_, 1);
v_tail_86_ = lean_ctor_get(v_x_83_, 2);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_109_ == 0)
{
v___x_88_ = v_x_83_;
v_isShared_89_ = v_isSharedCheck_109_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_tail_86_);
lean_inc(v_value_85_);
lean_inc(v_key_84_);
lean_dec(v_x_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_109_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v_fold_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_90_ = lean_array_get_size(v_x_82_);
v___x_91_ = l_Lean_ExprStructEq_hash(v_key_84_);
v___x_92_ = 32ULL;
v___x_93_ = lean_uint64_shift_right(v___x_91_, v___x_92_);
v_fold_94_ = lean_uint64_xor(v___x_91_, v___x_93_);
v___x_95_ = 16ULL;
v___x_96_ = lean_uint64_shift_right(v_fold_94_, v___x_95_);
v___x_97_ = lean_uint64_xor(v_fold_94_, v___x_96_);
v___x_98_ = lean_uint64_to_usize(v___x_97_);
v___x_99_ = lean_usize_of_nat(v___x_90_);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_sub(v___x_99_, v___x_100_);
v___x_102_ = lean_usize_land(v___x_98_, v___x_101_);
v___x_103_ = lean_array_uget_borrowed(v_x_82_, v___x_102_);
lean_inc(v___x_103_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 2, v___x_103_);
v___x_105_ = v___x_88_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_key_84_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_value_85_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v___x_103_);
v___x_105_ = v_reuseFailAlloc_108_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; 
v___x_106_ = lean_array_uset(v_x_82_, v___x_102_, v___x_105_);
v_x_82_ = v___x_106_;
v_x_83_ = v_tail_86_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_110_, lean_object* v_source_111_, lean_object* v_target_112_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_array_get_size(v_source_111_);
v___x_114_ = lean_nat_dec_lt(v_i_110_, v___x_113_);
if (v___x_114_ == 0)
{
lean_dec_ref(v_source_111_);
lean_dec(v_i_110_);
return v_target_112_;
}
else
{
lean_object* v_es_115_; lean_object* v___x_116_; lean_object* v_source_117_; lean_object* v_target_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_es_115_ = lean_array_fget(v_source_111_, v_i_110_);
v___x_116_ = lean_box(0);
v_source_117_ = lean_array_fset(v_source_111_, v_i_110_, v___x_116_);
v_target_118_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_112_, v_es_115_);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_i_110_, v___x_119_);
lean_dec(v_i_110_);
v_i_110_ = v___x_120_;
v_source_111_ = v_source_117_;
v_target_112_ = v_target_118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_nbuckets_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_123_ = lean_array_get_size(v_data_122_);
v___x_124_ = lean_unsigned_to_nat(2u);
v_nbuckets_125_ = lean_nat_mul(v___x_123_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_box(0);
v___x_128_ = lean_mk_array(v_nbuckets_125_, v___x_127_);
v___x_129_ = lean_array_propagate_mark(v_data_122_, v___x_128_);
v___x_130_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_126_, v_data_122_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_131_, lean_object* v_b_132_, lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_dec(v_b_132_);
lean_dec_ref(v_a_131_);
return v_x_133_;
}
else
{
lean_object* v_key_134_; lean_object* v_value_135_; lean_object* v_tail_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_148_; 
v_key_134_ = lean_ctor_get(v_x_133_, 0);
v_value_135_ = lean_ctor_get(v_x_133_, 1);
v_tail_136_ = lean_ctor_get(v_x_133_, 2);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_148_ == 0)
{
v___x_138_ = v_x_133_;
v_isShared_139_ = v_isSharedCheck_148_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_tail_136_);
lean_inc(v_value_135_);
lean_inc(v_key_134_);
lean_dec(v_x_133_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_148_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
uint8_t v___x_140_; 
v___x_140_ = l_Lean_ExprStructEq_beq(v_key_134_, v_a_131_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_131_, v_b_132_, v_tail_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 2, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_key_134_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_value_135_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
else
{
lean_object* v___x_146_; 
lean_dec(v_value_135_);
lean_dec(v_key_134_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v_b_132_);
lean_ctor_set(v___x_138_, 0, v_a_131_);
v___x_146_ = v___x_138_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_131_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_b_132_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_tail_136_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
else
{
lean_object* v_key_152_; lean_object* v_tail_153_; uint8_t v___x_154_; 
v_key_152_ = lean_ctor_get(v_x_150_, 0);
v_tail_153_ = lean_ctor_get(v_x_150_, 2);
v___x_154_ = l_Lean_ExprStructEq_beq(v_key_152_, v_a_149_);
if (v___x_154_ == 0)
{
v_x_150_ = v_tail_153_;
goto _start;
}
else
{
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_156_, lean_object* v_x_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_156_, v_x_157_);
lean_dec(v_x_157_);
lean_dec_ref(v_a_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object* v_m_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_size_163_; lean_object* v_buckets_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_207_; 
v_size_163_ = lean_ctor_get(v_m_160_, 0);
v_buckets_164_ = lean_ctor_get(v_m_160_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_m_160_);
if (v_isSharedCheck_207_ == 0)
{
v___x_166_ = v_m_160_;
v_isShared_167_ = v_isSharedCheck_207_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_buckets_164_);
lean_inc(v_size_163_);
lean_dec(v_m_160_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_207_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v_fold_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; lean_object* v_bkt_181_; uint8_t v___x_182_; 
v___x_168_ = lean_array_get_size(v_buckets_164_);
v___x_169_ = l_Lean_ExprStructEq_hash(v_a_161_);
v___x_170_ = 32ULL;
v___x_171_ = lean_uint64_shift_right(v___x_169_, v___x_170_);
v_fold_172_ = lean_uint64_xor(v___x_169_, v___x_171_);
v___x_173_ = 16ULL;
v___x_174_ = lean_uint64_shift_right(v_fold_172_, v___x_173_);
v___x_175_ = lean_uint64_xor(v_fold_172_, v___x_174_);
v___x_176_ = lean_uint64_to_usize(v___x_175_);
v___x_177_ = lean_usize_of_nat(v___x_168_);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_sub(v___x_177_, v___x_178_);
v___x_180_ = lean_usize_land(v___x_176_, v___x_179_);
v_bkt_181_ = lean_array_uget_borrowed(v_buckets_164_, v___x_180_);
v___x_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_161_, v_bkt_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v_size_x27_184_; lean_object* v___x_185_; lean_object* v_buckets_x27_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v_size_x27_184_ = lean_nat_add(v_size_163_, v___x_183_);
lean_dec(v_size_163_);
lean_inc(v_bkt_181_);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v_a_161_);
lean_ctor_set(v___x_185_, 1, v_b_162_);
lean_ctor_set(v___x_185_, 2, v_bkt_181_);
v_buckets_x27_186_ = lean_array_uset(v_buckets_164_, v___x_180_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(4u);
v___x_188_ = lean_nat_mul(v_size_x27_184_, v___x_187_);
v___x_189_ = lean_unsigned_to_nat(3u);
v___x_190_ = lean_nat_div(v___x_188_, v___x_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_array_get_size(v_buckets_x27_186_);
v___x_192_ = lean_nat_dec_le(v___x_190_, v___x_191_);
lean_dec(v___x_190_);
if (v___x_192_ == 0)
{
lean_object* v_val_193_; lean_object* v___x_195_; 
v_val_193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_186_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_val_193_);
lean_ctor_set(v___x_166_, 0, v_size_x27_184_);
v___x_195_ = v___x_166_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_size_x27_184_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_val_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
else
{
lean_object* v___x_198_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_buckets_x27_186_);
lean_ctor_set(v___x_166_, 0, v_size_x27_184_);
v___x_198_ = v___x_166_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_size_x27_184_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_buckets_x27_186_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
lean_object* v___x_200_; lean_object* v_buckets_x27_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
lean_inc(v_bkt_181_);
v___x_200_ = lean_box(0);
v_buckets_x27_201_ = lean_array_uset(v_buckets_164_, v___x_180_, v___x_200_);
v___x_202_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_161_, v_b_162_, v_bkt_181_);
v___x_203_ = lean_array_uset(v_buckets_x27_201_, v___x_180_, v___x_202_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_203_);
v___x_205_ = v___x_166_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_size_163_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(lean_object* v_a_208_, lean_object* v_e_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_212_ = lean_st_ref_take(v_a_208_);
v___x_213_ = lean_box(0);
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v___x_212_, v_e_209_, v_a_210_);
v___x_215_ = lean_st_ref_put(v_a_208_, v___x_214_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed(lean_object* v_a_216_, lean_object* v_e_217_, lean_object* v_a_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(v_a_216_, v_e_217_, v_a_218_);
lean_dec(v_a_216_);
return v_res_220_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_box(0);
v___x_222_ = l_Lean_interruptExceptionId;
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_228_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = l_Lean_maxRecDepthErrorMessage;
v___x_235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_237_ = l_Lean_MessageData_ofFormat(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_239_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_240_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_241_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_ref_241_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(lean_object* v_x_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___y_255_; lean_object* v___y_265_; uint8_t v___y_266_; uint8_t v___y_267_; lean_object* v___y_268_; uint16_t v___y_269_; lean_object* v___y_270_; lean_object* v_toCold_275_; lean_object* v_currRecDepth_276_; lean_object* v_ref_277_; uint16_t v_optionFlags_278_; uint8_t v_suppressElabErrors_279_; uint8_t v_isRecordingDeps_280_; lean_object* v_maxRecDepth_281_; lean_object* v_cancelTk_x3f_282_; 
v_toCold_275_ = lean_ctor_get(v___y_251_, 0);
v_currRecDepth_276_ = lean_ctor_get(v___y_251_, 1);
v_ref_277_ = lean_ctor_get(v___y_251_, 2);
v_optionFlags_278_ = lean_ctor_get_uint16(v___y_251_, sizeof(void*)*3);
v_suppressElabErrors_279_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 2);
v_isRecordingDeps_280_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 3);
v_maxRecDepth_281_ = lean_ctor_get(v_toCold_275_, 3);
v_cancelTk_x3f_282_ = lean_ctor_get(v_toCold_275_, 10);
if (lean_obj_tag(v_cancelTk_x3f_282_) == 1)
{
lean_object* v_val_288_; uint8_t v___x_289_; 
v_val_288_ = lean_ctor_get(v_cancelTk_x3f_282_, 0);
v___x_289_ = l_IO_CancelToken_isSet(v_val_288_);
if (v___x_289_ == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v___x_290_; lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_x_249_);
v___x_290_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
goto v___jp_283_;
}
v___jp_254_:
{
if (lean_obj_tag(v___y_255_) == 0)
{
return v___y_255_;
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
v_a_256_ = lean_ctor_get(v___y_255_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___y_255_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___y_255_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___y_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
v___jp_264_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v___y_270_, v___x_271_);
lean_inc_ref(v___y_265_);
v___x_273_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_273_, 0, v___y_265_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
lean_ctor_set(v___x_273_, 2, v___y_268_);
lean_ctor_set_uint16(v___x_273_, sizeof(void*)*3, v___y_269_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 2, v___y_267_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 3, v___y_266_);
lean_inc(v___y_252_);
lean_inc(v___y_250_);
v___x_274_ = lean_apply_4(v_x_249_, v___y_250_, v___x_273_, v___y_252_, lean_box(0));
v___y_255_ = v___x_274_;
goto v___jp_254_;
}
v___jp_283_:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_nat_dec_eq(v_maxRecDepth_281_, v___x_284_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
v___x_286_ = lean_nat_dec_eq(v_currRecDepth_276_, v_maxRecDepth_281_);
if (v___x_286_ == 0)
{
lean_inc(v_ref_277_);
v___y_265_ = v_toCold_275_;
v___y_266_ = v_isRecordingDeps_280_;
v___y_267_ = v_suppressElabErrors_279_;
v___y_268_ = v_ref_277_;
v___y_269_ = v_optionFlags_278_;
v___y_270_ = v_currRecDepth_276_;
goto v___jp_264_;
}
else
{
lean_object* v___x_287_; 
lean_dec_ref(v_x_249_);
lean_inc(v_ref_277_);
v___x_287_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_277_);
v___y_255_ = v___x_287_;
goto v___jp_254_;
}
}
else
{
lean_inc(v_ref_277_);
v___y_265_ = v_toCold_275_;
v___y_266_ = v_isRecordingDeps_280_;
v___y_267_ = v_suppressElabErrors_279_;
v___y_268_ = v_ref_277_;
v___y_269_ = v_optionFlags_278_;
v___y_270_ = v_currRecDepth_276_;
goto v___jp_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_305_, lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_apply_1(v_x_306_, lean_box(0));
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_312_, lean_object* v_x_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_312_, v_x_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_box(0);
return v___x_320_;
}
else
{
lean_object* v_key_321_; lean_object* v_value_322_; lean_object* v_tail_323_; uint8_t v___x_324_; 
v_key_321_ = lean_ctor_get(v_x_319_, 0);
v_value_322_ = lean_ctor_get(v_x_319_, 1);
v_tail_323_ = lean_ctor_get(v_x_319_, 2);
v___x_324_ = l_Lean_ExprStructEq_beq(v_key_321_, v_a_318_);
if (v___x_324_ == 0)
{
v_x_319_ = v_tail_323_;
goto _start;
}
else
{
lean_object* v___x_326_; 
lean_inc(v_value_322_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_value_322_);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_327_, v_x_328_);
lean_dec(v_x_328_);
lean_dec_ref(v_a_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_buckets_332_; lean_object* v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v_fold_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_buckets_332_ = lean_ctor_get(v_m_330_, 1);
v___x_333_ = lean_array_get_size(v_buckets_332_);
v___x_334_ = l_Lean_ExprStructEq_hash(v_a_331_);
v___x_335_ = 32ULL;
v___x_336_ = lean_uint64_shift_right(v___x_334_, v___x_335_);
v_fold_337_ = lean_uint64_xor(v___x_334_, v___x_336_);
v___x_338_ = 16ULL;
v___x_339_ = lean_uint64_shift_right(v_fold_337_, v___x_338_);
v___x_340_ = lean_uint64_xor(v_fold_337_, v___x_339_);
v___x_341_ = lean_uint64_to_usize(v___x_340_);
v___x_342_ = lean_usize_of_nat(v___x_333_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_sub(v___x_342_, v___x_343_);
v___x_345_ = lean_usize_land(v___x_341_, v___x_344_);
v___x_346_ = lean_array_uget_borrowed(v_buckets_332_, v___x_345_);
v___x_347_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_331_, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_348_, v_a_349_);
lean_dec_ref(v_a_349_);
lean_dec_ref(v_m_348_);
return v_res_350_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_352_; lean_object* v_dummy_353_; 
v___x_352_ = lean_box(0);
v_dummy_353_ = l_Lean_Expr_sort___override(v___x_352_);
return v_dummy_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_354_, lean_object* v_post_355_, size_t v_sz_356_, size_t v_i_357_, lean_object* v_bs_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_lt(v_i_357_, v_sz_356_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref(v_post_355_);
lean_dec_ref(v_pre_354_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_bs_358_);
return v___x_364_;
}
else
{
lean_object* v_v_365_; lean_object* v___x_366_; lean_object* v_bs_x27_367_; lean_object* v___x_368_; 
v_v_365_ = lean_array_uget(v_bs_358_, v_i_357_);
v___x_366_ = lean_unsigned_to_nat(0u);
v_bs_x27_367_ = lean_array_uset(v_bs_358_, v_i_357_, v___x_366_);
lean_inc_ref(v_post_355_);
lean_inc_ref(v_pre_354_);
v___x_368_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_354_, v_post_355_, v_v_365_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_add(v_i_357_, v___x_370_);
v___x_372_ = lean_array_uset(v_bs_x27_367_, v_i_357_, v_a_369_);
v_i_357_ = v___x_371_;
v_bs_358_ = v___x_372_;
goto _start;
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v_bs_x27_367_);
lean_dec_ref(v_post_355_);
lean_dec_ref(v_pre_354_);
v_a_374_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_368_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_368_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_382_, lean_object* v_post_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
if (lean_obj_tag(v_x_384_) == 5)
{
lean_object* v_fn_391_; lean_object* v_arg_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_fn_391_ = lean_ctor_get(v_x_384_, 0);
lean_inc_ref(v_fn_391_);
v_arg_392_ = lean_ctor_get(v_x_384_, 1);
lean_inc_ref(v_arg_392_);
lean_dec_ref_known(v_x_384_, 2);
v___x_393_ = lean_array_set(v_x_385_, v_x_386_, v_arg_392_);
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_sub(v_x_386_, v___x_394_);
lean_dec(v_x_386_);
v_x_384_ = v_fn_391_;
v_x_385_ = v___x_393_;
v_x_386_ = v___x_395_;
goto _start;
}
else
{
lean_object* v___x_397_; 
lean_dec(v_x_386_);
lean_inc_ref(v_post_383_);
lean_inc_ref(v_pre_382_);
v___x_397_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_382_, v_post_383_, v_x_384_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; size_t v_sz_399_; size_t v___x_400_; lean_object* v___x_401_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v_sz_399_ = lean_array_size(v_x_385_);
v___x_400_ = ((size_t)0ULL);
lean_inc_ref(v_post_383_);
lean_inc_ref(v_pre_382_);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_382_, v_post_383_, v_sz_399_, v___x_400_, v_x_385_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = l_Lean_mkAppN(v_a_398_, v_a_402_);
lean_dec(v_a_402_);
v___x_404_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_382_, v_post_383_, v___x_403_, v___y_387_, v___y_388_, v___y_389_);
return v___x_404_;
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_a_398_);
lean_dec_ref(v_post_383_);
lean_dec_ref(v_pre_382_);
v_a_405_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_401_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_401_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_dec_ref(v_x_385_);
lean_dec_ref(v_post_383_);
lean_dec_ref(v_pre_382_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_413_, lean_object* v_pre_414_, lean_object* v_e_415_, lean_object* v_post_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Core_checkSystem(v___x_413_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v___x_422_; 
lean_dec_ref_known(v___x_421_, 1);
lean_inc_ref(v_pre_414_);
lean_inc(v___y_419_);
lean_inc_ref(v___y_418_);
lean_inc_ref(v_e_415_);
v___x_422_ = lean_apply_4(v_pre_414_, v_e_415_, v___y_418_, v___y_419_, lean_box(0));
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_538_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_538_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_538_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_538_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___y_428_; 
switch(lean_obj_tag(v_a_423_))
{
case 0:
{
lean_object* v_e_528_; lean_object* v___x_530_; 
lean_dec_ref(v_post_416_);
lean_dec_ref(v_e_415_);
lean_dec_ref(v_pre_414_);
v_e_528_ = lean_ctor_get(v_a_423_, 0);
lean_inc_ref(v_e_528_);
lean_dec_ref_known(v_a_423_, 1);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v_e_528_);
v___x_530_ = v___x_425_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_e_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
case 1:
{
lean_object* v_e_532_; lean_object* v___x_533_; 
lean_del_object(v___x_425_);
lean_dec_ref(v_e_415_);
v_e_532_ = lean_ctor_get(v_a_423_, 0);
lean_inc_ref(v_e_532_);
lean_dec_ref_known(v_a_423_, 1);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_e_532_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v_a_534_, v___y_417_, v___y_418_, v___y_419_);
return v___x_535_;
}
else
{
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_533_;
}
}
default: 
{
lean_object* v_e_x3f_536_; 
lean_del_object(v___x_425_);
v_e_x3f_536_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_e_x3f_536_);
lean_dec_ref_known(v_a_423_, 1);
if (lean_obj_tag(v_e_x3f_536_) == 0)
{
v___y_428_ = v_e_415_;
goto v___jp_427_;
}
else
{
lean_object* v_val_537_; 
lean_dec_ref(v_e_415_);
v_val_537_ = lean_ctor_get(v_e_x3f_536_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v_e_x3f_536_, 1);
v___y_428_ = v_val_537_;
goto v___jp_427_;
}
}
}
v___jp_427_:
{
switch(lean_obj_tag(v___y_428_))
{
case 7:
{
lean_object* v_binderName_429_; lean_object* v_binderType_430_; lean_object* v_body_431_; uint8_t v_binderInfo_432_; lean_object* v___x_433_; 
v_binderName_429_ = lean_ctor_get(v___y_428_, 0);
v_binderType_430_ = lean_ctor_get(v___y_428_, 1);
v_body_431_ = lean_ctor_get(v___y_428_, 2);
v_binderInfo_432_ = lean_ctor_get_uint8(v___y_428_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_430_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_binderType_430_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
lean_inc_ref(v_body_431_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_body_431_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; size_t v___x_437_; size_t v___x_438_; uint8_t v___x_439_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = lean_ptr_addr(v_binderType_430_);
v___x_438_ = lean_ptr_addr(v_a_434_);
v___x_439_ = lean_usize_dec_eq(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_inc(v_binderName_429_);
lean_dec_ref_known(v___y_428_, 3);
v___x_440_ = l_Lean_Expr_forallE___override(v_binderName_429_, v_a_434_, v_a_436_, v_binderInfo_432_);
v___x_441_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_440_, v___y_417_, v___y_418_, v___y_419_);
return v___x_441_;
}
else
{
size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v___x_442_ = lean_ptr_addr(v_body_431_);
v___x_443_ = lean_ptr_addr(v_a_436_);
v___x_444_ = lean_usize_dec_eq(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_inc(v_binderName_429_);
lean_dec_ref_known(v___y_428_, 3);
v___x_445_ = l_Lean_Expr_forallE___override(v_binderName_429_, v_a_434_, v_a_436_, v_binderInfo_432_);
v___x_446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_445_, v___y_417_, v___y_418_, v___y_419_);
return v___x_446_;
}
else
{
uint8_t v___x_447_; 
v___x_447_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_432_, v_binderInfo_432_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_inc(v_binderName_429_);
lean_dec_ref_known(v___y_428_, 3);
v___x_448_ = l_Lean_Expr_forallE___override(v_binderName_429_, v_a_434_, v_a_436_, v_binderInfo_432_);
v___x_449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_448_, v___y_417_, v___y_418_, v___y_419_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; 
lean_dec(v_a_436_);
lean_dec(v_a_434_);
v___x_450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_450_;
}
}
}
}
else
{
lean_dec(v_a_434_);
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_435_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_433_;
}
}
case 6:
{
lean_object* v_binderName_451_; lean_object* v_binderType_452_; lean_object* v_body_453_; uint8_t v_binderInfo_454_; lean_object* v___x_455_; 
v_binderName_451_ = lean_ctor_get(v___y_428_, 0);
v_binderType_452_ = lean_ctor_get(v___y_428_, 1);
v_body_453_ = lean_ctor_get(v___y_428_, 2);
v_binderInfo_454_ = lean_ctor_get_uint8(v___y_428_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_452_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_binderType_452_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
lean_inc_ref(v_body_453_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_body_453_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = lean_ptr_addr(v_binderType_452_);
v___x_460_ = lean_ptr_addr(v_a_456_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc(v_binderName_451_);
lean_dec_ref_known(v___y_428_, 3);
v___x_462_ = l_Lean_Expr_lam___override(v_binderName_451_, v_a_456_, v_a_458_, v_binderInfo_454_);
v___x_463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_462_, v___y_417_, v___y_418_, v___y_419_);
return v___x_463_;
}
else
{
size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_ptr_addr(v_body_453_);
v___x_465_ = lean_ptr_addr(v_a_458_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc(v_binderName_451_);
lean_dec_ref_known(v___y_428_, 3);
v___x_467_ = l_Lean_Expr_lam___override(v_binderName_451_, v_a_456_, v_a_458_, v_binderInfo_454_);
v___x_468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_467_, v___y_417_, v___y_418_, v___y_419_);
return v___x_468_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_454_, v_binderInfo_454_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc(v_binderName_451_);
lean_dec_ref_known(v___y_428_, 3);
v___x_470_ = l_Lean_Expr_lam___override(v_binderName_451_, v_a_456_, v_a_458_, v_binderInfo_454_);
v___x_471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_470_, v___y_417_, v___y_418_, v___y_419_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; 
lean_dec(v_a_458_);
lean_dec(v_a_456_);
v___x_472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_472_;
}
}
}
}
else
{
lean_dec(v_a_456_);
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_457_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_455_;
}
}
case 8:
{
lean_object* v_declName_473_; lean_object* v_type_474_; lean_object* v_value_475_; lean_object* v_body_476_; uint8_t v_nondep_477_; lean_object* v___x_478_; 
v_declName_473_ = lean_ctor_get(v___y_428_, 0);
v_type_474_ = lean_ctor_get(v___y_428_, 1);
v_value_475_ = lean_ctor_get(v___y_428_, 2);
v_body_476_ = lean_ctor_get(v___y_428_, 3);
v_nondep_477_ = lean_ctor_get_uint8(v___y_428_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_474_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_type_474_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
lean_inc_ref(v_value_475_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_value_475_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
lean_inc_ref(v_body_476_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_482_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_body_476_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; size_t v___x_484_; size_t v___x_485_; uint8_t v___x_486_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = lean_ptr_addr(v_type_474_);
v___x_485_ = lean_ptr_addr(v_a_479_);
v___x_486_ = lean_usize_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_declName_473_);
lean_dec_ref_known(v___y_428_, 4);
v___x_487_ = l_Lean_Expr_letE___override(v_declName_473_, v_a_479_, v_a_481_, v_a_483_, v_nondep_477_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_487_, v___y_417_, v___y_418_, v___y_419_);
return v___x_488_;
}
else
{
size_t v___x_489_; size_t v___x_490_; uint8_t v___x_491_; 
v___x_489_ = lean_ptr_addr(v_value_475_);
v___x_490_ = lean_ptr_addr(v_a_481_);
v___x_491_ = lean_usize_dec_eq(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc(v_declName_473_);
lean_dec_ref_known(v___y_428_, 4);
v___x_492_ = l_Lean_Expr_letE___override(v_declName_473_, v_a_479_, v_a_481_, v_a_483_, v_nondep_477_);
v___x_493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_492_, v___y_417_, v___y_418_, v___y_419_);
return v___x_493_;
}
else
{
size_t v___x_494_; size_t v___x_495_; uint8_t v___x_496_; 
v___x_494_ = lean_ptr_addr(v_body_476_);
v___x_495_ = lean_ptr_addr(v_a_483_);
v___x_496_ = lean_usize_dec_eq(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_inc(v_declName_473_);
lean_dec_ref_known(v___y_428_, 4);
v___x_497_ = l_Lean_Expr_letE___override(v_declName_473_, v_a_479_, v_a_481_, v_a_483_, v_nondep_477_);
v___x_498_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_497_, v___y_417_, v___y_418_, v___y_419_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
lean_dec(v_a_483_);
lean_dec(v_a_481_);
lean_dec(v_a_479_);
v___x_499_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_499_;
}
}
}
}
else
{
lean_dec(v_a_481_);
lean_dec(v_a_479_);
lean_dec_ref_known(v___y_428_, 4);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_482_;
}
}
else
{
lean_dec(v_a_479_);
lean_dec_ref_known(v___y_428_, 4);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_480_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 4);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_478_;
}
}
case 5:
{
lean_object* v_dummy_500_; lean_object* v_nargs_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_dummy_500_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_501_ = l_Lean_Expr_getAppNumArgs(v___y_428_);
lean_inc(v_nargs_501_);
v___x_502_ = lean_mk_array(v_nargs_501_, v_dummy_500_);
v___x_503_ = lean_unsigned_to_nat(1u);
v___x_504_ = lean_nat_sub(v_nargs_501_, v___x_503_);
lean_dec(v_nargs_501_);
v___x_505_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_414_, v_post_416_, v___y_428_, v___x_502_, v___x_504_, v___y_417_, v___y_418_, v___y_419_);
return v___x_505_;
}
case 10:
{
lean_object* v_data_506_; lean_object* v_expr_507_; lean_object* v___x_508_; 
v_data_506_ = lean_ctor_get(v___y_428_, 0);
v_expr_507_ = lean_ctor_get(v___y_428_, 1);
lean_inc_ref(v_expr_507_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_expr_507_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; size_t v___x_510_; size_t v___x_511_; uint8_t v___x_512_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = lean_ptr_addr(v_expr_507_);
v___x_511_ = lean_ptr_addr(v_a_509_);
v___x_512_ = lean_usize_dec_eq(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_inc(v_data_506_);
lean_dec_ref_known(v___y_428_, 2);
v___x_513_ = l_Lean_Expr_mdata___override(v_data_506_, v_a_509_);
v___x_514_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_513_, v___y_417_, v___y_418_, v___y_419_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; 
lean_dec(v_a_509_);
v___x_515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_515_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 2);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_508_;
}
}
case 11:
{
lean_object* v_typeName_516_; lean_object* v_idx_517_; lean_object* v_struct_518_; lean_object* v___x_519_; 
v_typeName_516_ = lean_ctor_get(v___y_428_, 0);
v_idx_517_ = lean_ctor_get(v___y_428_, 1);
v_struct_518_ = lean_ctor_get(v___y_428_, 2);
lean_inc_ref(v_struct_518_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_struct_518_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; size_t v___x_521_; size_t v___x_522_; uint8_t v___x_523_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_ptr_addr(v_struct_518_);
v___x_522_ = lean_ptr_addr(v_a_520_);
v___x_523_ = lean_usize_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_inc(v_idx_517_);
lean_inc(v_typeName_516_);
lean_dec_ref_known(v___y_428_, 3);
v___x_524_ = l_Lean_Expr_proj___override(v_typeName_516_, v_idx_517_, v_a_520_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_524_, v___y_417_, v___y_418_, v___y_419_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
lean_dec(v_a_520_);
v___x_526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_526_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_519_;
}
}
default: 
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_527_;
}
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref(v_post_416_);
lean_dec_ref(v_e_415_);
lean_dec_ref(v_pre_414_);
v_a_539_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_422_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_422_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
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
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_post_416_);
lean_dec_ref(v_e_415_);
lean_dec_ref(v_pre_414_);
v_a_547_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_421_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_421_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_555_, lean_object* v_pre_556_, lean_object* v_e_557_, lean_object* v_post_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_555_, v_pre_556_, v_e_557_, v_post_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_564_, lean_object* v_post_565_, lean_object* v_e_566_, lean_object* v_a_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_inc(v_a_567_);
v___x_571_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_571_, 0, lean_box(0));
lean_closure_set(v___x_571_, 1, lean_box(0));
lean_closure_set(v___x_571_, 2, v_a_567_);
v___x_572_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_571_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_604_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_604_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_604_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_604_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_573_, v_e_566_);
lean_dec(v_a_573_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
lean_del_object(v___x_575_);
v___x_578_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_566_);
v___f_579_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_579_, 0, v___x_578_);
lean_closure_set(v___f_579_, 1, v_pre_564_);
lean_closure_set(v___f_579_, 2, v_e_566_);
lean_closure_set(v___f_579_, 3, v_post_565_);
v___x_580_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_579_, v_a_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___f_582_; lean_object* v___x_583_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc_n(v_a_581_, 2);
lean_dec_ref_known(v___x_580_, 1);
lean_inc(v_a_567_);
v___f_582_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_582_, 0, v_a_567_);
lean_closure_set(v___f_582_, 1, v_e_566_);
lean_closure_set(v___f_582_, 2, v_a_581_);
v___x_583_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_582_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v___x_583_, 0);
lean_dec(v_unused_591_);
v___x_585_ = v___x_583_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_dec(v___x_583_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v_a_581_);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_581_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_a_581_);
v_a_592_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_583_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_583_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_dec_ref(v_e_566_);
return v___x_580_;
}
}
else
{
lean_object* v_val_600_; lean_object* v___x_602_; 
lean_dec_ref(v_e_566_);
lean_dec_ref(v_post_565_);
lean_dec_ref(v_pre_564_);
v_val_600_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_600_);
lean_dec_ref_known(v___x_577_, 1);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_val_600_);
v___x_602_ = v___x_575_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_val_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_e_566_);
lean_dec_ref(v_post_565_);
lean_dec_ref(v_pre_564_);
v_a_605_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_572_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_572_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_613_, lean_object* v_post_614_, lean_object* v_e_615_, lean_object* v_a_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; 
lean_inc_ref(v_post_614_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc_ref(v_e_615_);
v___x_620_ = lean_apply_4(v_post_614_, v_e_615_, v___y_617_, v___y_618_, lean_box(0));
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_639_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_639_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_639_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_639_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
switch(lean_obj_tag(v_a_621_))
{
case 0:
{
lean_object* v_e_625_; lean_object* v___x_627_; 
lean_dec_ref(v_e_615_);
lean_dec_ref(v_post_614_);
lean_dec_ref(v_pre_613_);
v_e_625_ = lean_ctor_get(v_a_621_, 0);
lean_inc_ref(v_e_625_);
lean_dec_ref_known(v_a_621_, 1);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_e_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_e_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
case 1:
{
lean_object* v_e_629_; lean_object* v___x_630_; 
lean_del_object(v___x_623_);
lean_dec_ref(v_e_615_);
v_e_629_ = lean_ctor_get(v_a_621_, 0);
lean_inc_ref(v_e_629_);
lean_dec_ref_known(v_a_621_, 1);
v___x_630_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_613_, v_post_614_, v_e_629_, v_a_616_, v___y_617_, v___y_618_);
return v___x_630_;
}
default: 
{
lean_object* v_e_x3f_631_; 
lean_dec_ref(v_post_614_);
lean_dec_ref(v_pre_613_);
v_e_x3f_631_ = lean_ctor_get(v_a_621_, 0);
lean_inc(v_e_x3f_631_);
lean_dec_ref_known(v_a_621_, 1);
if (lean_obj_tag(v_e_x3f_631_) == 0)
{
lean_object* v___x_633_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_e_615_);
v___x_633_ = v___x_623_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_e_615_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
else
{
lean_object* v_val_635_; lean_object* v___x_637_; 
lean_dec_ref(v_e_615_);
v_val_635_ = lean_ctor_get(v_e_x3f_631_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v_e_x3f_631_, 1);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_val_635_);
v___x_637_ = v___x_623_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_val_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_e_615_);
lean_dec_ref(v_post_614_);
lean_dec_ref(v_pre_613_);
v_a_640_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_620_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_620_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_648_, lean_object* v_post_649_, lean_object* v_e_650_, lean_object* v_a_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_648_, v_post_649_, v_e_650_, v_a_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v_a_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_656_, lean_object* v_post_657_, lean_object* v_sz_658_, lean_object* v_i_659_, lean_object* v_bs_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
size_t v_sz_boxed_665_; size_t v_i_boxed_666_; lean_object* v_res_667_; 
v_sz_boxed_665_ = lean_unbox_usize(v_sz_658_);
lean_dec(v_sz_658_);
v_i_boxed_666_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_656_, v_post_657_, v_sz_boxed_665_, v_i_boxed_666_, v_bs_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_668_, lean_object* v_post_669_, lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_668_, v_post_669_, v_x_670_, v_x_671_, v_x_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_678_, lean_object* v_post_679_, lean_object* v_e_680_, lean_object* v_a_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_678_, v_post_679_, v_e_680_, v_a_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v_a_681_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_686_, lean_object* v_x_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_apply_1(v_x_687_, lean_box(0));
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_693_, v_x_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_698_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_box(0);
v___x_700_ = lean_unsigned_to_nat(16u);
v___x_701_ = lean_mk_array(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_706_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_706_, 0, lean_box(0));
lean_closure_set(v___x_706_, 1, lean_box(0));
lean_closure_set(v___x_706_, 2, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_707_, lean_object* v_pre_708_, lean_object* v_post_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_a_715_; lean_object* v___x_716_; 
v___x_713_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_714_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_713_, v___y_710_, v___y_711_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v___x_714_);
v___x_716_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_708_, v_post_709_, v_input_707_, v_a_715_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_718_, 0, lean_box(0));
lean_closure_set(v___x_718_, 1, lean_box(0));
lean_closure_set(v___x_718_, 2, v_a_715_);
v___x_719_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_718_, v___y_710_, v___y_711_);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v___x_719_, 0);
lean_dec(v_unused_727_);
v___x_721_ = v___x_719_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_dec(v___x_719_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_a_717_);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_717_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_dec(v_a_715_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_728_, lean_object* v_pre_729_, lean_object* v_post_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_728_, v_pre_729_, v_post_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___x_743_; 
v___f_741_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_742_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_743_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_737_, v___f_741_, v___f_742_, v_a_738_, v_a_739_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Meta_elimOptParam(v_type_744_, v_a_745_, v_a_746_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_749_, lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_750_, v_a_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_753_, lean_object* v_m_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_753_, v_m_754_, v_a_755_);
lean_dec_ref(v_a_755_);
lean_dec_ref(v_m_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_757_, lean_object* v_ref_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_758_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_763_, lean_object* v_ref_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_763_, v_ref_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_780_, v___y_781_, v___y_782_, v___y_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_786_, v_x_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_793_, lean_object* v_m_794_, lean_object* v_a_795_, lean_object* v_b_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_794_, v_a_795_, v_b_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_798_, lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_802_, lean_object* v_a_803_, lean_object* v_x_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_802_, v_a_803_, v_x_804_);
lean_dec(v_x_804_);
lean_dec_ref(v_a_803_);
return v_res_805_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_806_, lean_object* v_a_807_, lean_object* v_x_808_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_807_, v_x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_810_, lean_object* v_a_811_, lean_object* v_x_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_810_, v_a_811_, v_x_812_);
lean_dec(v_x_812_);
lean_dec_ref(v_a_811_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_815_, lean_object* v_data_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_818_, lean_object* v_a_819_, lean_object* v_b_820_, lean_object* v_x_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_819_, v_b_820_, v_x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_823_, lean_object* v_i_824_, lean_object* v_source_825_, lean_object* v_target_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_824_, v_source_825_, v_target_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_828_, lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_832_, lean_object* v_as_833_, size_t v_sz_834_, size_t v_i_835_, lean_object* v_b_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_a_843_; uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_lt(v_i_835_, v_sz_834_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_b_836_);
return v___x_848_;
}
else
{
lean_object* v_snd_849_; lean_object* v_fst_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_928_; 
v_snd_849_ = lean_ctor_get(v_b_836_, 1);
v_fst_850_ = lean_ctor_get(v_b_836_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_b_836_);
if (v_isSharedCheck_928_ == 0)
{
v___x_852_ = v_b_836_;
v_isShared_853_ = v_isSharedCheck_928_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_849_);
lean_inc(v_fst_850_);
lean_dec(v_b_836_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_928_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_array_854_; lean_object* v_start_855_; lean_object* v_stop_856_; uint8_t v___x_857_; 
v_array_854_ = lean_ctor_get(v_snd_849_, 0);
v_start_855_ = lean_ctor_get(v_snd_849_, 1);
v_stop_856_ = lean_ctor_get(v_snd_849_, 2);
v___x_857_ = lean_nat_dec_lt(v_start_855_, v_stop_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_859_; 
if (v_isShared_853_ == 0)
{
v___x_859_ = v___x_852_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_fst_850_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_snd_849_);
v___x_859_ = v_reuseFailAlloc_861_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
else
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_924_; 
lean_inc(v_stop_856_);
lean_inc(v_start_855_);
lean_inc_ref(v_array_854_);
v_isSharedCheck_924_ = !lean_is_exclusive(v_snd_849_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; 
v_unused_925_ = lean_ctor_get(v_snd_849_, 2);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_snd_849_, 1);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_snd_849_, 0);
lean_dec(v_unused_927_);
v___x_863_ = v_snd_849_;
v_isShared_864_ = v_isSharedCheck_924_;
goto v_resetjp_862_;
}
else
{
lean_dec(v_snd_849_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_924_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v_a_865_ = lean_array_uget_borrowed(v_as_833_, v_i_835_);
v___x_866_ = lean_array_fget(v_array_854_, v_start_855_);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_start_855_, v___x_867_);
lean_dec(v_start_855_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_868_);
v___x_870_ = v___x_863_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_array_854_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_stop_856_);
v___x_870_ = v_reuseFailAlloc_923_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; 
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v_a_865_);
v___x_871_ = lean_infer_type(v_a_865_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_871_) == 0)
{
if (v_skipIfPropOrEq_832_ == 0)
{
lean_object* v___x_872_; 
lean_dec_ref_known(v___x_871_, 1);
lean_inc(v_a_865_);
v___x_872_ = l_Lean_Meta_mkEqHEq(v_a_865_, v___x_866_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = lean_array_push(v_fst_850_, v_a_873_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_870_);
lean_ctor_set(v___x_852_, 0, v___x_874_);
v___x_876_ = v___x_852_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_870_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
v_a_843_ = v___x_876_;
goto v___jp_842_;
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v___x_870_);
lean_del_object(v___x_852_);
lean_dec(v_fst_850_);
v_a_878_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_872_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_872_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_871_, 1);
v___x_887_ = l_Lean_Meta_isProp(v_a_886_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; uint8_t v___x_893_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_893_ = lean_unbox(v_a_888_);
lean_dec(v_a_888_);
if (v___x_893_ == 0)
{
uint8_t v___x_894_; 
v___x_894_ = lean_expr_eqv(v_a_865_, v___x_866_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_del_object(v___x_852_);
lean_inc(v_a_865_);
v___x_895_ = l_Lean_Meta_mkEqHEq(v_a_865_, v___x_866_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = lean_array_push(v_fst_850_, v_a_896_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_870_);
v_a_843_ = v___x_898_;
goto v___jp_842_;
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v___x_870_);
lean_dec(v_fst_850_);
v_a_899_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_895_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_895_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_dec(v___x_866_);
goto v___jp_889_;
}
}
else
{
lean_dec(v___x_866_);
goto v___jp_889_;
}
v___jp_889_:
{
lean_object* v___x_891_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_870_);
v___x_891_ = v___x_852_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_fst_850_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_870_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
v_a_843_ = v___x_891_;
goto v___jp_842_;
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v___x_870_);
lean_dec(v___x_866_);
lean_del_object(v___x_852_);
lean_dec(v_fst_850_);
v_a_907_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_887_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_887_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___x_870_);
lean_dec(v___x_866_);
lean_del_object(v___x_852_);
lean_dec(v_fst_850_);
v_a_915_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_871_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_871_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
}
}
v___jp_842_:
{
size_t v___x_844_; size_t v___x_845_; 
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_add(v_i_835_, v___x_844_);
v_i_835_ = v___x_845_;
v_b_836_ = v_a_843_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_929_, lean_object* v_as_930_, lean_object* v_sz_931_, lean_object* v_i_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_939_; size_t v_sz_boxed_940_; size_t v_i_boxed_941_; lean_object* v_res_942_; 
v_skipIfPropOrEq_boxed_939_ = lean_unbox(v_skipIfPropOrEq_929_);
v_sz_boxed_940_ = lean_unbox_usize(v_sz_931_);
lean_dec(v_sz_931_);
v_i_boxed_941_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_939_, v_as_930_, v_sz_boxed_940_, v_i_boxed_941_, v_b_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec_ref(v_as_930_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_945_, lean_object* v_args2_946_, uint8_t v_skipIfPropOrEq_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_953_; lean_object* v_eqs_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; size_t v_sz_958_; size_t v___x_959_; lean_object* v___x_960_; 
v___x_953_ = lean_unsigned_to_nat(0u);
v_eqs_954_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_955_ = lean_array_get_size(v_args2_946_);
v___x_956_ = l_Array_toSubarray___redArg(v_args2_946_, v___x_953_, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_eqs_954_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v_sz_958_ = lean_array_size(v_args1_945_);
v___x_959_ = ((size_t)0ULL);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_947_, v_args1_945_, v_sz_958_, v___x_959_, v___x_957_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_969_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_969_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_fst_965_; lean_object* v___x_967_; 
v_fst_965_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_fst_965_);
lean_dec(v_a_961_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v_fst_965_);
v___x_967_ = v___x_963_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_fst_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_960_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_960_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_978_, lean_object* v_args2_979_, lean_object* v_skipIfPropOrEq_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_986_; lean_object* v_res_987_; 
v_skipIfPropOrEq_boxed_986_ = lean_unbox(v_skipIfPropOrEq_980_);
v_res_987_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_978_, v_args2_979_, v_skipIfPropOrEq_boxed_986_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec_ref(v_args1_978_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_988_, lean_object* v_b_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
v___x_995_ = lean_apply_6(v_k_988_, v_b_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, lean_box(0));
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_996_, lean_object* v_b_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_996_, v_b_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1004_, uint8_t v_bi_1005_, lean_object* v_type_1006_, lean_object* v_k_1007_, uint8_t v_kind_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___f_1014_; lean_object* v___x_1015_; 
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1014_, 0, v_k_1007_);
v___x_1015_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1004_, v_bi_1005_, v_type_1006_, v___f_1014_, v_kind_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1015_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1015_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1032_, lean_object* v_bi_1033_, lean_object* v_type_1034_, lean_object* v_k_1035_, lean_object* v_kind_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
uint8_t v_bi_boxed_1042_; uint8_t v_kind_boxed_1043_; lean_object* v_res_1044_; 
v_bi_boxed_1042_ = lean_unbox(v_bi_1033_);
v_kind_boxed_1043_ = lean_unbox(v_kind_1036_);
v_res_1044_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1032_, v_bi_boxed_1042_, v_type_1034_, v_k_1035_, v_kind_boxed_1043_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1045_, lean_object* v_name_1046_, uint8_t v_bi_1047_, lean_object* v_type_1048_, lean_object* v_k_1049_, uint8_t v_kind_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1046_, v_bi_1047_, v_type_1048_, v_k_1049_, v_kind_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1057_, lean_object* v_name_1058_, lean_object* v_bi_1059_, lean_object* v_type_1060_, lean_object* v_k_1061_, lean_object* v_kind_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
uint8_t v_bi_boxed_1068_; uint8_t v_kind_boxed_1069_; lean_object* v_res_1070_; 
v_bi_boxed_1068_ = lean_unbox(v_bi_1059_);
v_kind_boxed_1069_ = lean_unbox(v_kind_1062_);
v_res_1070_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1057_, v_name_1058_, v_bi_boxed_1068_, v_type_1060_, v_k_1061_, v_kind_boxed_1069_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v_env_1078_; uint8_t v___x_1079_; lean_object* v_env_1080_; lean_object* v___x_1081_; lean_object* v_toCold_1082_; lean_object* v_mctx_1083_; lean_object* v_lctx_1084_; lean_object* v_options_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1077_ = lean_st_ref_get(v___y_1075_);
v_env_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_ref(v_env_1078_);
lean_dec(v___x_1077_);
v___x_1079_ = 0;
v_env_1080_ = l_Lean_Environment_setRecordingDeps(v_env_1078_, v___x_1079_);
v___x_1081_ = lean_st_ref_get(v___y_1073_);
v_toCold_1082_ = lean_ctor_get(v___y_1074_, 0);
v_mctx_1083_ = lean_ctor_get(v___x_1081_, 0);
lean_inc_ref(v_mctx_1083_);
lean_dec(v___x_1081_);
v_lctx_1084_ = lean_ctor_get(v___y_1072_, 2);
v_options_1085_ = lean_ctor_get(v_toCold_1082_, 2);
lean_inc_ref(v_options_1085_);
lean_inc_ref(v_lctx_1084_);
v___x_1086_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1086_, 0, v_env_1080_);
lean_ctor_set(v___x_1086_, 1, v_mctx_1083_);
lean_ctor_set(v___x_1086_, 2, v_lctx_1084_);
lean_ctor_set(v___x_1086_, 3, v_options_1085_);
v___x_1087_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_msgData_1071_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_ref_1102_; lean_object* v___x_1103_; lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1112_; 
v_ref_1102_ = lean_ctor_get(v___y_1099_, 2);
v___x_1103_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_inc(v_ref_1102_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_ref_1102_);
lean_ctor_set(v___x_1108_, 1, v_a_1104_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 1);
lean_ctor_set(v___x_1106_, 0, v___x_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1120_, lean_object* v_body_1121_, lean_object* v_args2_1122_, lean_object* v_args2New_1123_, lean_object* v_ctorVal_1124_, lean_object* v_useEq_1125_, lean_object* v_args1_1126_, lean_object* v_resultType_1127_, lean_object* v_k_1128_, lean_object* v_arg2_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
uint8_t v_useEq_boxed_1135_; lean_object* v_res_1136_; 
v_useEq_boxed_1135_ = lean_unbox(v_useEq_1125_);
v_res_1136_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1120_, v_body_1121_, v_args2_1122_, v_args2New_1123_, v_ctorVal_1124_, v_useEq_boxed_1135_, v_args1_1126_, v_resultType_1127_, v_k_1128_, v_arg2_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec_ref(v_body_1121_);
lean_dec(v_i_1120_);
return v_res_1136_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1142_ = l_Lean_stringToMessageData(v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1143_, uint8_t v_useEq_1144_, lean_object* v_args1_1145_, lean_object* v_resultType_1146_, lean_object* v_k_1147_, lean_object* v_i_1148_, lean_object* v_type_1149_, lean_object* v_args2_1150_, lean_object* v_args2New_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = lean_array_get_size(v_args1_1145_);
v___x_1158_ = lean_nat_dec_lt(v_i_1148_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
lean_dec_ref(v_type_1149_);
lean_dec(v_i_1148_);
lean_dec_ref(v_resultType_1146_);
lean_dec_ref(v_args1_1145_);
lean_dec_ref(v_ctorVal_1143_);
lean_inc(v_a_1155_);
lean_inc_ref(v_a_1154_);
lean_inc(v_a_1153_);
lean_inc_ref(v_a_1152_);
v___x_1159_ = lean_apply_7(v_k_1147_, v_args2_1150_, v_args2New_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, lean_box(0));
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; 
lean_inc(v_a_1155_);
lean_inc_ref(v_a_1154_);
lean_inc(v_a_1153_);
lean_inc_ref(v_a_1152_);
v___x_1160_ = lean_whnf(v_type_1149_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
if (lean_obj_tag(v_a_1161_) == 7)
{
lean_object* v_binderName_1162_; lean_object* v_binderType_1163_; lean_object* v_body_1164_; lean_object* v_lctx_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_binderName_1162_ = lean_ctor_get(v_a_1161_, 0);
lean_inc(v_binderName_1162_);
v_binderType_1163_ = lean_ctor_get(v_a_1161_, 1);
lean_inc_ref(v_binderType_1163_);
v_body_1164_ = lean_ctor_get(v_a_1161_, 2);
lean_inc_ref(v_body_1164_);
lean_dec_ref_known(v_a_1161_, 3);
v_lctx_1165_ = lean_ctor_get(v_a_1152_, 2);
v___x_1166_ = lean_array_fget_borrowed(v_args1_1145_, v_i_1148_);
lean_inc(v___x_1166_);
lean_inc_ref(v_lctx_1165_);
v___x_1167_ = l_Lean_Meta_occursOrInType(v_lctx_1165_, v___x_1166_, v_resultType_1146_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___f_1169_; uint8_t v___y_1171_; 
v___x_1168_ = lean_box(v_useEq_1144_);
v___f_1169_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1169_, 0, v_i_1148_);
lean_closure_set(v___f_1169_, 1, v_body_1164_);
lean_closure_set(v___f_1169_, 2, v_args2_1150_);
lean_closure_set(v___f_1169_, 3, v_args2New_1151_);
lean_closure_set(v___f_1169_, 4, v_ctorVal_1143_);
lean_closure_set(v___f_1169_, 5, v___x_1168_);
lean_closure_set(v___f_1169_, 6, v_args1_1145_);
lean_closure_set(v___f_1169_, 7, v_resultType_1146_);
lean_closure_set(v___f_1169_, 8, v_k_1147_);
if (v_useEq_1144_ == 0)
{
uint8_t v___x_1174_; 
v___x_1174_ = 1;
v___y_1171_ = v___x_1174_;
goto v___jp_1170_;
}
else
{
uint8_t v___x_1175_; 
v___x_1175_ = 0;
v___y_1171_ = v___x_1175_;
goto v___jp_1170_;
}
v___jp_1170_:
{
uint8_t v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = 0;
v___x_1173_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1162_, v___y_1171_, v_binderType_1163_, v___f_1169_, v___x_1172_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1173_;
}
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec_ref(v_binderType_1163_);
lean_dec(v_binderName_1162_);
v___x_1176_ = lean_unsigned_to_nat(1u);
v___x_1177_ = lean_nat_add(v_i_1148_, v___x_1176_);
lean_dec(v_i_1148_);
v___x_1178_ = lean_expr_instantiate1(v_body_1164_, v___x_1166_);
lean_dec_ref(v_body_1164_);
lean_inc(v___x_1166_);
v___x_1179_ = lean_array_push(v_args2_1150_, v___x_1166_);
v_i_1148_ = v___x_1177_;
v_type_1149_ = v___x_1178_;
v_args2_1150_ = v___x_1179_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1181_; lean_object* v_name_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v_a_1161_);
lean_dec_ref(v_args2New_1151_);
lean_dec_ref(v_args2_1150_);
lean_dec(v_i_1148_);
lean_dec_ref(v_k_1147_);
lean_dec_ref(v_resultType_1146_);
lean_dec_ref(v_args1_1145_);
v_toConstantVal_1181_ = lean_ctor_get(v_ctorVal_1143_, 0);
lean_inc_ref(v_toConstantVal_1181_);
lean_dec_ref(v_ctorVal_1143_);
v_name_1182_ = lean_ctor_get(v_toConstantVal_1181_, 0);
lean_inc(v_name_1182_);
lean_dec_ref(v_toConstantVal_1181_);
v___x_1183_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1184_ = l_Lean_MessageData_ofName(v_name_1182_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1187_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1188_;
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_args2New_1151_);
lean_dec_ref(v_args2_1150_);
lean_dec(v_i_1148_);
lean_dec_ref(v_k_1147_);
lean_dec_ref(v_resultType_1146_);
lean_dec_ref(v_args1_1145_);
lean_dec_ref(v_ctorVal_1143_);
v_a_1189_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1160_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1160_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1197_, lean_object* v_body_1198_, lean_object* v_args2_1199_, lean_object* v_args2New_1200_, lean_object* v_ctorVal_1201_, uint8_t v_useEq_1202_, lean_object* v_args1_1203_, lean_object* v_resultType_1204_, lean_object* v_k_1205_, lean_object* v_arg2_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_add(v_i_1197_, v___x_1212_);
v___x_1214_ = lean_expr_instantiate1(v_body_1198_, v_arg2_1206_);
lean_inc_ref(v_arg2_1206_);
v___x_1215_ = lean_array_push(v_args2_1199_, v_arg2_1206_);
v___x_1216_ = lean_array_push(v_args2New_1200_, v_arg2_1206_);
v___x_1217_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1201_, v_useEq_1202_, v_args1_1203_, v_resultType_1204_, v_k_1205_, v___x_1213_, v___x_1214_, v___x_1215_, v___x_1216_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1218_, lean_object* v_useEq_1219_, lean_object* v_args1_1220_, lean_object* v_resultType_1221_, lean_object* v_k_1222_, lean_object* v_i_1223_, lean_object* v_type_1224_, lean_object* v_args2_1225_, lean_object* v_args2New_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
uint8_t v_useEq_boxed_1232_; lean_object* v_res_1233_; 
v_useEq_boxed_1232_ = lean_unbox(v_useEq_1219_);
v_res_1233_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1218_, v_useEq_boxed_1232_, v_args1_1220_, v_resultType_1221_, v_k_1222_, v_i_1223_, v_type_1224_, v_args2_1225_, v_args2New_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1234_, lean_object* v_msg_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1242_, lean_object* v_msg_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1242_, v_msg_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1250_, lean_object* v_h__1_1251_, lean_object* v_h__2_1252_){
_start:
{
if (lean_obj_tag(v_____x_1250_) == 7)
{
lean_object* v_binderName_1253_; lean_object* v_binderType_1254_; lean_object* v_body_1255_; uint8_t v_binderInfo_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec(v_h__2_1252_);
v_binderName_1253_ = lean_ctor_get(v_____x_1250_, 0);
lean_inc(v_binderName_1253_);
v_binderType_1254_ = lean_ctor_get(v_____x_1250_, 1);
lean_inc_ref(v_binderType_1254_);
v_body_1255_ = lean_ctor_get(v_____x_1250_, 2);
lean_inc_ref(v_body_1255_);
v_binderInfo_1256_ = lean_ctor_get_uint8(v_____x_1250_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1250_, 3);
v___x_1257_ = lean_box(v_binderInfo_1256_);
v___x_1258_ = lean_apply_4(v_h__1_1251_, v_binderName_1253_, v_binderType_1254_, v_body_1255_, v___x_1257_);
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; 
lean_dec(v_h__1_1251_);
v___x_1259_ = lean_apply_2(v_h__2_1252_, v_____x_1250_, lean_box(0));
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1260_, lean_object* v_____x_1261_, lean_object* v_h__1_1262_, lean_object* v_h__2_1263_){
_start:
{
if (lean_obj_tag(v_____x_1261_) == 7)
{
lean_object* v_binderName_1264_; lean_object* v_binderType_1265_; lean_object* v_body_1266_; uint8_t v_binderInfo_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v_h__2_1263_);
v_binderName_1264_ = lean_ctor_get(v_____x_1261_, 0);
lean_inc(v_binderName_1264_);
v_binderType_1265_ = lean_ctor_get(v_____x_1261_, 1);
lean_inc_ref(v_binderType_1265_);
v_body_1266_ = lean_ctor_get(v_____x_1261_, 2);
lean_inc_ref(v_body_1266_);
v_binderInfo_1267_ = lean_ctor_get_uint8(v_____x_1261_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1261_, 3);
v___x_1268_ = lean_box(v_binderInfo_1267_);
v___x_1269_ = lean_apply_4(v_h__1_1262_, v_binderName_1264_, v_binderType_1265_, v_body_1266_, v___x_1268_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; 
lean_dec(v_h__1_1262_);
v___x_1270_ = lean_apply_2(v_h__2_1263_, v_____x_1261_, lean_box(0));
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1271_, lean_object* v_b_1272_, lean_object* v_c_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
v___x_1279_ = lean_apply_7(v_k_1271_, v_b_1272_, v_c_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, lean_box(0));
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1280_, lean_object* v_b_1281_, lean_object* v_c_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1280_, v_b_1281_, v_c_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1289_, lean_object* v_k_1290_, uint8_t v_cleanupAnnotations_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___f_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___f_1297_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1297_, 0, v_k_1290_);
v___x_1298_ = 0;
v___x_1299_ = lean_box(0);
v___x_1300_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1298_, v___x_1299_, v_type_1289_, v___f_1297_, v_cleanupAnnotations_1291_, v___x_1298_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_a_1309_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1300_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1300_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1317_, lean_object* v_k_1318_, lean_object* v_cleanupAnnotations_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1325_; lean_object* v_res_1326_; 
v_cleanupAnnotations_boxed_1325_ = lean_unbox(v_cleanupAnnotations_1319_);
v_res_1326_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1317_, v_k_1318_, v_cleanupAnnotations_boxed_1325_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1327_, lean_object* v_type_1328_, lean_object* v_k_1329_, uint8_t v_cleanupAnnotations_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1328_, v_k_1329_, v_cleanupAnnotations_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_type_1338_, lean_object* v_k_1339_, lean_object* v_cleanupAnnotations_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1346_; lean_object* v_res_1347_; 
v_cleanupAnnotations_boxed_1346_ = lean_unbox(v_cleanupAnnotations_1340_);
v_res_1347_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1337_, v_type_1338_, v_k_1339_, v_cleanupAnnotations_boxed_1346_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1348_, lean_object* v_maxFVars_x3f_1349_, lean_object* v_k_1350_, uint8_t v_cleanupAnnotations_1351_, uint8_t v_whnfType_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___f_1358_; lean_object* v___x_1359_; 
v___f_1358_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1358_, 0, v_k_1350_);
v___x_1359_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1348_, v_maxFVars_x3f_1349_, v___f_1358_, v_cleanupAnnotations_1351_, v_whnfType_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1359_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1376_, lean_object* v_maxFVars_x3f_1377_, lean_object* v_k_1378_, lean_object* v_cleanupAnnotations_1379_, lean_object* v_whnfType_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1386_; uint8_t v_whnfType_boxed_1387_; lean_object* v_res_1388_; 
v_cleanupAnnotations_boxed_1386_ = lean_unbox(v_cleanupAnnotations_1379_);
v_whnfType_boxed_1387_ = lean_unbox(v_whnfType_1380_);
v_res_1388_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1376_, v_maxFVars_x3f_1377_, v_k_1378_, v_cleanupAnnotations_boxed_1386_, v_whnfType_boxed_1387_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1389_, lean_object* v_type_1390_, lean_object* v_maxFVars_x3f_1391_, lean_object* v_k_1392_, uint8_t v_cleanupAnnotations_1393_, uint8_t v_whnfType_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1390_, v_maxFVars_x3f_1391_, v_k_1392_, v_cleanupAnnotations_1393_, v_whnfType_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_type_1402_, lean_object* v_maxFVars_x3f_1403_, lean_object* v_k_1404_, lean_object* v_cleanupAnnotations_1405_, lean_object* v_whnfType_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1412_; uint8_t v_whnfType_boxed_1413_; lean_object* v_res_1414_; 
v_cleanupAnnotations_boxed_1412_ = lean_unbox(v_cleanupAnnotations_1405_);
v_whnfType_boxed_1413_ = lean_unbox(v_whnfType_1406_);
v_res_1414_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1401_, v_type_1402_, v_maxFVars_x3f_1403_, v_k_1404_, v_cleanupAnnotations_boxed_1412_, v_whnfType_boxed_1413_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1415_, lean_object* v_us_1416_, lean_object* v_params_1417_, lean_object* v_args1_1418_, uint8_t v_useEq_1419_, lean_object* v_args2_1420_, lean_object* v_args2New_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1427_ = l_Lean_mkConst(v_name_1415_, v_us_1416_);
v___x_1428_ = l_Lean_mkAppN(v___x_1427_, v_params_1417_);
lean_inc_ref(v___x_1428_);
v___x_1429_ = l_Lean_mkAppN(v___x_1428_, v_args1_1418_);
v___x_1430_ = l_Lean_mkAppN(v___x_1428_, v_args2_1420_);
v___x_1431_ = l_Lean_Meta_mkEq(v___x_1429_, v___x_1430_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; uint8_t v___x_1433_; lean_object* v_result_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___x_1480_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = 1;
v___x_1480_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1418_, v_args2_1420_, v___x_1433_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1512_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1512_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1512_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; 
v___x_1485_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1481_);
if (lean_obj_tag(v___x_1485_) == 1)
{
lean_del_object(v___x_1483_);
if (v_useEq_1419_ == 0)
{
lean_object* v_val_1486_; lean_object* v___x_1487_; 
v_val_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1487_ = l_Lean_mkArrow(v_a_1432_, v_val_1486_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v_result_1435_ = v_a_1488_;
v___y_1436_ = v___y_1422_;
v___y_1437_ = v___y_1423_;
v___y_1438_ = v___y_1424_;
v___y_1439_ = v___y_1425_;
goto v___jp_1434_;
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_a_1489_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1487_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1487_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v_val_1497_; lean_object* v___x_1498_; 
v_val_1497_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1498_ = l_Lean_Meta_mkEq(v_a_1432_, v_val_1497_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v_result_1435_ = v_a_1499_;
v___y_1436_ = v___y_1422_;
v___y_1437_ = v___y_1423_;
v___y_1438_ = v___y_1424_;
v___y_1439_ = v___y_1425_;
goto v___jp_1434_;
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1498_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1498_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
lean_dec(v___x_1485_);
lean_dec(v_a_1432_);
v___x_1508_ = lean_box(0);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1508_);
v___x_1510_ = v___x_1483_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_a_1432_);
v_a_1513_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1480_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1480_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
v___jp_1434_:
{
uint8_t v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = 0;
v___x_1441_ = 1;
v___x_1442_ = l_Lean_Meta_mkForallFVars(v_args2New_1421_, v_result_1435_, v___x_1440_, v___x_1433_, v___x_1433_, v___x_1441_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = l_Lean_Meta_mkForallFVars(v_args1_1418_, v_a_1443_, v___x_1440_, v___x_1433_, v___x_1433_, v___x_1441_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = l_Lean_Meta_mkForallFVars(v_params_1417_, v_a_1445_, v___x_1440_, v___x_1433_, v___x_1433_, v___x_1441_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_a_1447_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_a_1456_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1446_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1446_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_a_1464_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1444_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1444_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1472_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1442_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1442_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v_args2_1420_);
v_a_1521_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1431_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1431_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1529_, lean_object* v_us_1530_, lean_object* v_params_1531_, lean_object* v_args1_1532_, lean_object* v_useEq_1533_, lean_object* v_args2_1534_, lean_object* v_args2New_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v_useEq_boxed_1541_; lean_object* v_res_1542_; 
v_useEq_boxed_1541_ = lean_unbox(v_useEq_1533_);
v_res_1542_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1529_, v_us_1530_, v_params_1531_, v_args1_1532_, v_useEq_boxed_1541_, v_args2_1534_, v_args2New_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v_args2New_1535_);
lean_dec_ref(v_args1_1532_);
lean_dec_ref(v_params_1531_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1543_, size_t v_i_1544_, lean_object* v_bs_1545_){
_start:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_usize_dec_lt(v_i_1544_, v_sz_1543_);
if (v___x_1546_ == 0)
{
return v_bs_1545_;
}
else
{
lean_object* v_v_1547_; lean_object* v___x_1548_; lean_object* v_bs_x27_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v_v_1547_ = lean_array_uget(v_bs_1545_, v_i_1544_);
v___x_1548_ = lean_unsigned_to_nat(0u);
v_bs_x27_1549_ = lean_array_uset(v_bs_1545_, v_i_1544_, v___x_1548_);
v___x_1550_ = l_Lean_Expr_fvarId_x21(v_v_1547_);
lean_dec(v_v_1547_);
v___x_1551_ = 1;
v___x_1552_ = lean_box(v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1550_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = ((size_t)1ULL);
v___x_1555_ = lean_usize_add(v_i_1544_, v___x_1554_);
v___x_1556_ = lean_array_uset(v_bs_x27_1549_, v_i_1544_, v___x_1553_);
v_i_1544_ = v___x_1555_;
v_bs_1545_ = v___x_1556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1558_, lean_object* v_i_1559_, lean_object* v_bs_1560_){
_start:
{
size_t v_sz_boxed_1561_; size_t v_i_boxed_1562_; lean_object* v_res_1563_; 
v_sz_boxed_1561_ = lean_unbox_usize(v_sz_1558_);
lean_dec(v_sz_1558_);
v_i_boxed_1562_ = lean_unbox_usize(v_i_1559_);
lean_dec(v_i_1559_);
v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1561_, v_i_boxed_1562_, v_bs_1560_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1564_, lean_object* v_k_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1564_, v_k_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_a_1580_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1571_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1571_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1588_, lean_object* v_k_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1588_, v_k_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v_bs_1588_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1596_, lean_object* v_k_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_sz_1603_ = lean_array_size(v_bs_1596_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1603_, v___x_1604_, v_bs_1596_);
v___x_1606_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1605_, v_k_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec_ref(v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1607_, lean_object* v_k_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1607_, v_k_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1615_, lean_object* v_us_1616_, lean_object* v_params_1617_, uint8_t v_useEq_1618_, lean_object* v_ctorVal_1619_, lean_object* v_type_1620_, lean_object* v_args1_1621_, lean_object* v_resultType_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; lean_object* v___f_1629_; 
v___x_1628_ = lean_box(v_useEq_1618_);
lean_inc_ref(v_args1_1621_);
lean_inc_ref(v_params_1617_);
v___f_1629_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1629_, 0, v_name_1615_);
lean_closure_set(v___f_1629_, 1, v_us_1616_);
lean_closure_set(v___f_1629_, 2, v_params_1617_);
lean_closure_set(v___f_1629_, 3, v_args1_1621_);
lean_closure_set(v___f_1629_, 4, v___x_1628_);
if (v_useEq_1618_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1630_ = l_Array_append___redArg(v_params_1617_, v_args1_1621_);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1633_ = lean_box(v_useEq_1618_);
v___x_1634_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1634_, 0, v_ctorVal_1619_);
lean_closure_set(v___x_1634_, 1, v___x_1633_);
lean_closure_set(v___x_1634_, 2, v_args1_1621_);
lean_closure_set(v___x_1634_, 3, v_resultType_1622_);
lean_closure_set(v___x_1634_, 4, v___f_1629_);
lean_closure_set(v___x_1634_, 5, v___x_1631_);
lean_closure_set(v___x_1634_, 6, v_type_1620_);
lean_closure_set(v___x_1634_, 7, v___x_1632_);
lean_closure_set(v___x_1634_, 8, v___x_1632_);
v___x_1635_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1630_, v___x_1634_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec_ref(v_params_1617_);
v___x_1636_ = lean_unsigned_to_nat(0u);
v___x_1637_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1638_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1619_, v_useEq_1618_, v_args1_1621_, v_resultType_1622_, v___f_1629_, v___x_1636_, v_type_1620_, v___x_1637_, v___x_1637_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1639_, lean_object* v_us_1640_, lean_object* v_params_1641_, lean_object* v_useEq_1642_, lean_object* v_ctorVal_1643_, lean_object* v_type_1644_, lean_object* v_args1_1645_, lean_object* v_resultType_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
uint8_t v_useEq_boxed_1652_; lean_object* v_res_1653_; 
v_useEq_boxed_1652_ = lean_unbox(v_useEq_1642_);
v_res_1653_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1639_, v_us_1640_, v_params_1641_, v_useEq_boxed_1652_, v_ctorVal_1643_, v_type_1644_, v_args1_1645_, v_resultType_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1654_, lean_object* v_us_1655_, uint8_t v_useEq_1656_, lean_object* v_ctorVal_1657_, lean_object* v_params_1658_, lean_object* v_type_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; lean_object* v___f_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1665_ = lean_box(v_useEq_1656_);
lean_inc_ref(v_type_1659_);
v___f_1666_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1666_, 0, v_name_1654_);
lean_closure_set(v___f_1666_, 1, v_us_1655_);
lean_closure_set(v___f_1666_, 2, v_params_1658_);
lean_closure_set(v___f_1666_, 3, v___x_1665_);
lean_closure_set(v___f_1666_, 4, v_ctorVal_1657_);
lean_closure_set(v___f_1666_, 5, v_type_1659_);
v___x_1667_ = 0;
v___x_1668_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1659_, v___f_1666_, v___x_1667_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1669_, lean_object* v_us_1670_, lean_object* v_useEq_1671_, lean_object* v_ctorVal_1672_, lean_object* v_params_1673_, lean_object* v_type_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
uint8_t v_useEq_boxed_1680_; lean_object* v_res_1681_; 
v_useEq_boxed_1680_ = lean_unbox(v_useEq_1671_);
v_res_1681_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1669_, v_us_1670_, v_useEq_boxed_1680_, v_ctorVal_1672_, v_params_1673_, v_type_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
if (lean_obj_tag(v_a_1682_) == 0)
{
lean_object* v___x_1684_; 
v___x_1684_ = l_List_reverse___redArg(v_a_1683_);
return v___x_1684_;
}
else
{
lean_object* v_head_1685_; lean_object* v_tail_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1695_; 
v_head_1685_ = lean_ctor_get(v_a_1682_, 0);
v_tail_1686_ = lean_ctor_get(v_a_1682_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_a_1682_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1688_ = v_a_1682_;
v_isShared_1689_ = v_isSharedCheck_1695_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_tail_1686_);
lean_inc(v_head_1685_);
lean_dec(v_a_1682_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1695_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = l_Lean_mkLevelParam(v_head_1685_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 1, v_a_1683_);
lean_ctor_set(v___x_1688_, 0, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_a_1683_);
v___x_1692_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
v_a_1682_ = v_tail_1686_;
v_a_1683_ = v___x_1692_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1696_, uint8_t v_useEq_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_toConstantVal_1703_; lean_object* v_numParams_1704_; lean_object* v_name_1705_; lean_object* v_levelParams_1706_; lean_object* v_type_1707_; lean_object* v___x_1708_; lean_object* v_us_1709_; lean_object* v___x_1710_; lean_object* v___f_1711_; lean_object* v___x_1712_; 
v_toConstantVal_1703_ = lean_ctor_get(v_ctorVal_1696_, 0);
v_numParams_1704_ = lean_ctor_get(v_ctorVal_1696_, 3);
lean_inc(v_numParams_1704_);
v_name_1705_ = lean_ctor_get(v_toConstantVal_1703_, 0);
lean_inc(v_name_1705_);
v_levelParams_1706_ = lean_ctor_get(v_toConstantVal_1703_, 1);
v_type_1707_ = lean_ctor_get(v_toConstantVal_1703_, 2);
lean_inc_ref(v_type_1707_);
v___x_1708_ = lean_box(0);
lean_inc(v_levelParams_1706_);
v_us_1709_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1706_, v___x_1708_);
v___x_1710_ = lean_box(v_useEq_1697_);
v___f_1711_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1711_, 0, v_name_1705_);
lean_closure_set(v___f_1711_, 1, v_us_1709_);
lean_closure_set(v___f_1711_, 2, v___x_1710_);
lean_closure_set(v___f_1711_, 3, v_ctorVal_1696_);
v___x_1712_ = l_Lean_Meta_elimOptParam(v_type_1707_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_numParams_1704_);
v___x_1715_ = 0;
v___x_1716_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1713_, v___x_1714_, v___f_1711_, v___x_1715_, v___x_1715_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v___x_1716_;
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v___f_1711_);
lean_dec(v_numParams_1704_);
v_a_1717_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1712_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1712_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1725_, lean_object* v_useEq_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
uint8_t v_useEq_boxed_1732_; lean_object* v_res_1733_; 
v_useEq_boxed_1732_ = lean_unbox(v_useEq_1726_);
v_res_1733_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1725_, v_useEq_boxed_1732_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1734_, lean_object* v_bs_1735_, lean_object* v_k_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1735_, v_k_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1743_, lean_object* v_bs_1744_, lean_object* v_k_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1743_, v_bs_1744_, v_k_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v_bs_1744_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1752_, lean_object* v_bs_1753_, lean_object* v_k_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1753_, v_k_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_bs_1762_, lean_object* v_k_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1761_, v_bs_1762_, v_k_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
uint8_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = 0;
v___x_1777_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1770_, v___x_1776_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
return v_res_1784_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1790_ = l_Lean_stringToMessageData(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1792_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1793_ = l_Lean_MessageData_ofName(v_ctorName_1791_);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1797_, lean_object* v_mvarId_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1804_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1797_);
v___x_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_mvarId_1798_);
v___x_1806_ = l_Lean_indentD(v___x_1805_);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1804_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1807_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1809_, lean_object* v_mvarId_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1809_, v_mvarId_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1817_, lean_object* v_ctorName_1818_, lean_object* v_mvarId_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1818_, v_mvarId_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1826_, lean_object* v_ctorName_1827_, lean_object* v_mvarId_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1826_, v_ctorName_1827_, v_mvarId_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1835_, lean_object* v_as_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
if (lean_obj_tag(v_as_1836_) == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_dec(v_ctorName_1835_);
v___x_1842_ = lean_box(0);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
return v___x_1843_;
}
else
{
lean_object* v_head_1844_; lean_object* v_tail_1845_; lean_object* v___x_1846_; 
v_head_1844_ = lean_ctor_get(v_as_1836_, 0);
lean_inc_n(v_head_1844_, 2);
v_tail_1845_ = lean_ctor_get(v_as_1836_, 1);
lean_inc(v_tail_1845_);
lean_dec_ref_known(v_as_1836_, 2);
v___x_1846_ = l_Lean_MVarId_assumptionCore(v_head_1844_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; uint8_t v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = lean_unbox(v_a_1847_);
lean_dec(v_a_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; 
lean_dec(v_tail_1845_);
v___x_1849_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1835_, v_head_1844_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1849_;
}
else
{
lean_dec(v_head_1844_);
v_as_1836_ = v_tail_1845_;
goto _start;
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_tail_1845_);
lean_dec(v_head_1844_);
lean_dec(v_ctorName_1835_);
v_a_1851_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1846_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1846_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1859_, lean_object* v_as_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1859_, v_as_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1867_, lean_object* v_ctorName_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_MVarId_splitAndCore(v_mvarId_1867_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v___x_1876_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1868_, v_a_1875_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
return v___x_1876_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_ctorName_1868_);
v_a_1877_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1874_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1874_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1885_, lean_object* v_ctorName_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1885_, v_ctorName_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___f_1900_; lean_object* v___x_922__overap_1901_; lean_object* v___x_1902_; 
v___f_1900_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_922__overap_1901_ = lean_panic_fn_borrowed(v___f_1900_, v_msg_1894_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
v___x_1902_ = lean_apply_5(v___x_922__overap_1901_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, lean_box(0));
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
return v_res_1909_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1910_; double v___x_1911_; 
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = lean_float_of_nat(v___x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1915_, lean_object* v_msg_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_ref_1922_; lean_object* v___x_1923_; lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1969_; 
v_ref_1922_ = lean_ctor_get(v___y_1919_, 2);
v___x_1923_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1969_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1969_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v_traceState_1929_; lean_object* v_env_1930_; lean_object* v_nextMacroScope_1931_; lean_object* v_ngen_1932_; lean_object* v_auxDeclNGen_1933_; lean_object* v_cache_1934_; lean_object* v_recordedDeps_1935_; lean_object* v_messages_1936_; lean_object* v_infoState_1937_; lean_object* v_snapshotTasks_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1968_; 
v___x_1928_ = lean_st_ref_take(v___y_1920_);
v_traceState_1929_ = lean_ctor_get(v___x_1928_, 4);
v_env_1930_ = lean_ctor_get(v___x_1928_, 0);
v_nextMacroScope_1931_ = lean_ctor_get(v___x_1928_, 1);
v_ngen_1932_ = lean_ctor_get(v___x_1928_, 2);
v_auxDeclNGen_1933_ = lean_ctor_get(v___x_1928_, 3);
v_cache_1934_ = lean_ctor_get(v___x_1928_, 5);
v_recordedDeps_1935_ = lean_ctor_get(v___x_1928_, 6);
v_messages_1936_ = lean_ctor_get(v___x_1928_, 7);
v_infoState_1937_ = lean_ctor_get(v___x_1928_, 8);
v_snapshotTasks_1938_ = lean_ctor_get(v___x_1928_, 9);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1940_ = v___x_1928_;
v_isShared_1941_ = v_isSharedCheck_1968_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_snapshotTasks_1938_);
lean_inc(v_infoState_1937_);
lean_inc(v_messages_1936_);
lean_inc(v_recordedDeps_1935_);
lean_inc(v_cache_1934_);
lean_inc(v_traceState_1929_);
lean_inc(v_auxDeclNGen_1933_);
lean_inc(v_ngen_1932_);
lean_inc(v_nextMacroScope_1931_);
lean_inc(v_env_1930_);
lean_dec(v___x_1928_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1968_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
uint64_t v_tid_1942_; lean_object* v_traces_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1967_; 
v_tid_1942_ = lean_ctor_get_uint64(v_traceState_1929_, sizeof(void*)*1);
v_traces_1943_ = lean_ctor_get(v_traceState_1929_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_traceState_1929_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1945_ = v_traceState_1929_;
v_isShared_1946_ = v_isSharedCheck_1967_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_traces_1943_);
lean_dec(v_traceState_1929_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1967_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; double v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1947_ = lean_box(0);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1950_ = 0;
v___x_1951_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1952_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1952_, 0, v_cls_1915_);
lean_ctor_set(v___x_1952_, 1, v___x_1948_);
lean_ctor_set(v___x_1952_, 2, v___x_1951_);
lean_ctor_set_float(v___x_1952_, sizeof(void*)*3, v___x_1949_);
lean_ctor_set_float(v___x_1952_, sizeof(void*)*3 + 8, v___x_1949_);
lean_ctor_set_uint8(v___x_1952_, sizeof(void*)*3 + 16, v___x_1950_);
v___x_1953_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1954_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1952_);
lean_ctor_set(v___x_1954_, 1, v_a_1924_);
lean_ctor_set(v___x_1954_, 2, v___x_1953_);
lean_inc(v_ref_1922_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v_ref_1922_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = l_Lean_PersistentArray_push___redArg(v_traces_1943_, v___x_1955_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1956_);
v___x_1958_ = v___x_1945_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1956_);
lean_ctor_set_uint64(v_reuseFailAlloc_1966_, sizeof(void*)*1, v_tid_1942_);
v___x_1958_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1960_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 4, v___x_1958_);
v___x_1960_ = v___x_1940_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_env_1930_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_nextMacroScope_1931_);
lean_ctor_set(v_reuseFailAlloc_1965_, 2, v_ngen_1932_);
lean_ctor_set(v_reuseFailAlloc_1965_, 3, v_auxDeclNGen_1933_);
lean_ctor_set(v_reuseFailAlloc_1965_, 4, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1965_, 5, v_cache_1934_);
lean_ctor_set(v_reuseFailAlloc_1965_, 6, v_recordedDeps_1935_);
lean_ctor_set(v_reuseFailAlloc_1965_, 7, v_messages_1936_);
lean_ctor_set(v_reuseFailAlloc_1965_, 8, v_infoState_1937_);
lean_ctor_set(v_reuseFailAlloc_1965_, 9, v_snapshotTasks_1938_);
v___x_1960_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = lean_st_ref_put(v___y_1920_, v___x_1960_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1947_);
v___x_1963_ = v___x_1926_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1947_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1970_, lean_object* v_msg_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1970_, v_msg_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1977_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1981_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1982_ = lean_unsigned_to_nat(30u);
v___x_1983_ = lean_unsigned_to_nat(96u);
v___x_1984_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1985_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1986_ = l_mkPanicMessageWithDecl(v___x_1985_, v___x_1984_, v___x_1983_, v___x_1982_, v___x_1981_);
return v___x_1986_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_cls_1995_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_1996_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_1997_ = l_Lean_Name_append(v___x_1996_, v_cls_1995_);
return v___x_1997_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_2000_ = l_Lean_stringToMessageData(v___x_1999_);
return v___x_2000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_2003_ = l_Lean_stringToMessageData(v___x_2002_);
return v___x_2003_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2006_ = l_Lean_stringToMessageData(v___x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2007_, lean_object* v_mvarId_2008_, lean_object* v_h_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v_toCold_2035_; lean_object* v_options_2036_; uint8_t v_hasTrace_2037_; 
v_toCold_2035_ = lean_ctor_get(v_a_2012_, 0);
v_options_2036_ = lean_ctor_get(v_toCold_2035_, 2);
v_hasTrace_2037_ = lean_ctor_get_uint8(v_options_2036_, sizeof(void*)*1);
if (v_hasTrace_2037_ == 0)
{
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v_inheritedTraceOptions_2038_; lean_object* v_cls_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v_inheritedTraceOptions_2038_ = lean_ctor_get(v_toCold_2035_, 11);
v_cls_2039_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2040_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2041_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2038_, v_options_2036_, v___x_2040_);
if (v___x_2041_ == 0)
{
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2042_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2007_);
v___x_2043_ = l_Lean_MessageData_ofName(v_ctorName_2007_);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2042_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
lean_inc(v_h_2009_);
v___x_2047_ = l_Lean_mkFVar(v_h_2009_);
v___x_2048_ = l_Lean_MessageData_ofExpr(v___x_2047_);
v___x_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2046_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
lean_inc(v_mvarId_2008_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_mvarId_2008_);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2039_, v___x_2053_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_dec_ref_known(v___x_2054_, 1);
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_dec(v_h_2009_);
lean_dec(v_mvarId_2008_);
lean_dec(v_ctorName_2007_);
return v___x_2054_;
}
}
}
v___jp_2015_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_box(0);
v___x_2021_ = l_Lean_Meta_injection(v_mvarId_2008_, v_h_2009_, v___x_2020_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
if (lean_obj_tag(v_a_2022_) == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec(v_ctorName_2007_);
v___x_2023_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2024_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2023_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2024_;
}
else
{
lean_object* v_mvarId_2025_; lean_object* v___x_2026_; 
v_mvarId_2025_ = lean_ctor_get(v_a_2022_, 0);
lean_inc(v_mvarId_2025_);
lean_dec_ref_known(v_a_2022_, 3);
v___x_2026_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2025_, v_ctorName_2007_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2026_;
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_ctorName_2007_);
v_a_2027_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2021_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2021_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2055_, lean_object* v_mvarId_2056_, lean_object* v_h_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2055_, v_mvarId_2056_, v_h_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2064_, lean_object* v_k_2065_, uint8_t v_cleanupAnnotations_2066_, uint8_t v_whnfType_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___f_2073_; lean_object* v___x_2074_; 
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2073_, 0, v_k_2065_);
v___x_2074_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2064_, v___f_2073_, v_cleanupAnnotations_2066_, v_whnfType_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_a_2083_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2074_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2074_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2091_, lean_object* v_k_2092_, lean_object* v_cleanupAnnotations_2093_, lean_object* v_whnfType_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2100_; uint8_t v_whnfType_boxed_2101_; lean_object* v_res_2102_; 
v_cleanupAnnotations_boxed_2100_ = lean_unbox(v_cleanupAnnotations_2093_);
v_whnfType_boxed_2101_ = lean_unbox(v_whnfType_2094_);
v_res_2102_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2091_, v_k_2092_, v_cleanupAnnotations_boxed_2100_, v_whnfType_boxed_2101_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2103_, lean_object* v_type_2104_, lean_object* v_k_2105_, uint8_t v_cleanupAnnotations_2106_, uint8_t v_whnfType_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2104_, v_k_2105_, v_cleanupAnnotations_2106_, v_whnfType_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_type_2115_, lean_object* v_k_2116_, lean_object* v_cleanupAnnotations_2117_, lean_object* v_whnfType_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2124_; uint8_t v_whnfType_boxed_2125_; lean_object* v_res_2126_; 
v_cleanupAnnotations_boxed_2124_ = lean_unbox(v_cleanupAnnotations_2117_);
v_whnfType_boxed_2125_ = lean_unbox(v_whnfType_2118_);
v_res_2126_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2114_, v_type_2115_, v_k_2116_, v_cleanupAnnotations_boxed_2124_, v_whnfType_boxed_2125_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2127_, lean_object* v_ctorName_2128_, lean_object* v_xs_2129_, lean_object* v_type_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_box(0);
v___x_2137_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2130_, v___x_2136_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = l_Lean_Expr_mvarId_x21(v_a_2138_);
v___x_2140_ = lean_array_get_size(v_xs_2129_);
v___x_2141_ = lean_unsigned_to_nat(1u);
v___x_2142_ = lean_nat_sub(v___x_2140_, v___x_2141_);
v___x_2143_ = lean_array_get_borrowed(v___x_2127_, v_xs_2129_, v___x_2142_);
lean_dec(v___x_2142_);
v___x_2144_ = l_Lean_Expr_fvarId_x21(v___x_2143_);
v___x_2145_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2128_, v___x_2139_, v___x_2144_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2145_) == 0)
{
uint8_t v___x_2146_; uint8_t v___x_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; 
lean_dec_ref_known(v___x_2145_, 1);
v___x_2146_ = 0;
v___x_2147_ = 1;
v___x_2148_ = 1;
v___x_2149_ = l_Lean_Meta_mkLambdaFVars(v_xs_2129_, v_a_2138_, v___x_2146_, v___x_2147_, v___x_2146_, v___x_2147_, v___x_2148_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
return v___x_2149_;
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v_a_2138_);
v_a_2150_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2145_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2145_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_dec(v_ctorName_2128_);
return v___x_2137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2158_, lean_object* v_ctorName_2159_, lean_object* v_xs_2160_, lean_object* v_type_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2158_, v_ctorName_2159_, v_xs_2160_, v_type_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec_ref(v_xs_2160_);
lean_dec_ref(v___x_2158_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2168_, lean_object* v_targetType_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v___x_2175_; lean_object* v___f_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2175_ = l_Lean_instInhabitedExpr;
v___f_2176_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2176_, 0, v___x_2175_);
lean_closure_set(v___f_2176_, 1, v_ctorName_2168_);
v___x_2177_ = 0;
v___x_2178_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2169_, v___f_2176_, v___x_2177_, v___x_2177_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2179_, lean_object* v_targetType_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2179_, v_targetType_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2190_){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2192_ = l_Lean_Name_append(v_ctorName_2190_, v___x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v___x_2196_; 
v___x_2196_ = l_Lean_Expr_hasMVar(v_e_2193_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_e_2193_);
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; lean_object* v_mctx_2199_; lean_object* v___x_2200_; lean_object* v_fst_2201_; lean_object* v_snd_2202_; lean_object* v___x_2203_; lean_object* v_cache_2204_; lean_object* v_zetaDeltaFVarIds_2205_; lean_object* v_postponed_2206_; lean_object* v_diag_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2216_; 
v___x_2198_ = lean_st_ref_get(v___y_2194_);
v_mctx_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc_ref(v_mctx_2199_);
lean_dec(v___x_2198_);
v___x_2200_ = l_Lean_instantiateMVarsCore(v_mctx_2199_, v_e_2193_);
v_fst_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_fst_2201_);
v_snd_2202_ = lean_ctor_get(v___x_2200_, 1);
lean_inc(v_snd_2202_);
lean_dec_ref(v___x_2200_);
v___x_2203_ = lean_st_ref_take(v___y_2194_);
v_cache_2204_ = lean_ctor_get(v___x_2203_, 1);
v_zetaDeltaFVarIds_2205_ = lean_ctor_get(v___x_2203_, 2);
v_postponed_2206_ = lean_ctor_get(v___x_2203_, 3);
v_diag_2207_ = lean_ctor_get(v___x_2203_, 4);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2203_, 0);
lean_dec(v_unused_2217_);
v___x_2209_ = v___x_2203_;
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_diag_2207_);
lean_inc(v_postponed_2206_);
lean_inc(v_zetaDeltaFVarIds_2205_);
lean_inc(v_cache_2204_);
lean_dec(v___x_2203_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v_snd_2202_);
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_snd_2202_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_cache_2204_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_zetaDeltaFVarIds_2205_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_postponed_2206_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_diag_2207_);
v___x_2212_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_st_ref_put(v___y_2194_, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_fst_2201_);
return v___x_2214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2218_, v___y_2219_);
lean_dec(v___y_2219_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2222_, v___y_2224_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2235_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_unsigned_to_nat(32u);
v___x_2237_ = lean_mk_empty_array_with_capacity(v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2239_ = ((size_t)5ULL);
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = lean_unsigned_to_nat(32u);
v___x_2242_ = lean_mk_empty_array_with_capacity(v___x_2241_);
v___x_2243_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2244_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v___x_2242_);
lean_ctor_set(v___x_2244_, 2, v___x_2240_);
lean_ctor_set(v___x_2244_, 3, v___x_2240_);
lean_ctor_set_usize(v___x_2244_, 4, v___x_2239_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; lean_object* v_traceState_2248_; lean_object* v_traces_2249_; lean_object* v___x_2250_; lean_object* v_traceState_2251_; lean_object* v_env_2252_; lean_object* v_nextMacroScope_2253_; lean_object* v_ngen_2254_; lean_object* v_auxDeclNGen_2255_; lean_object* v_cache_2256_; lean_object* v_recordedDeps_2257_; lean_object* v_messages_2258_; lean_object* v_infoState_2259_; lean_object* v_snapshotTasks_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2279_; 
v___x_2247_ = lean_st_ref_get(v___y_2245_);
v_traceState_2248_ = lean_ctor_get(v___x_2247_, 4);
lean_inc_ref(v_traceState_2248_);
lean_dec(v___x_2247_);
v_traces_2249_ = lean_ctor_get(v_traceState_2248_, 0);
lean_inc_ref(v_traces_2249_);
lean_dec_ref(v_traceState_2248_);
v___x_2250_ = lean_st_ref_take(v___y_2245_);
v_traceState_2251_ = lean_ctor_get(v___x_2250_, 4);
v_env_2252_ = lean_ctor_get(v___x_2250_, 0);
v_nextMacroScope_2253_ = lean_ctor_get(v___x_2250_, 1);
v_ngen_2254_ = lean_ctor_get(v___x_2250_, 2);
v_auxDeclNGen_2255_ = lean_ctor_get(v___x_2250_, 3);
v_cache_2256_ = lean_ctor_get(v___x_2250_, 5);
v_recordedDeps_2257_ = lean_ctor_get(v___x_2250_, 6);
v_messages_2258_ = lean_ctor_get(v___x_2250_, 7);
v_infoState_2259_ = lean_ctor_get(v___x_2250_, 8);
v_snapshotTasks_2260_ = lean_ctor_get(v___x_2250_, 9);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2262_ = v___x_2250_;
v_isShared_2263_ = v_isSharedCheck_2279_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_snapshotTasks_2260_);
lean_inc(v_infoState_2259_);
lean_inc(v_messages_2258_);
lean_inc(v_recordedDeps_2257_);
lean_inc(v_cache_2256_);
lean_inc(v_traceState_2251_);
lean_inc(v_auxDeclNGen_2255_);
lean_inc(v_ngen_2254_);
lean_inc(v_nextMacroScope_2253_);
lean_inc(v_env_2252_);
lean_dec(v___x_2250_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2279_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
uint64_t v_tid_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2277_; 
v_tid_2264_ = lean_ctor_get_uint64(v_traceState_2251_, sizeof(void*)*1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_traceState_2251_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v_traceState_2251_, 0);
lean_dec(v_unused_2278_);
v___x_2266_ = v_traceState_2251_;
v_isShared_2267_ = v_isSharedCheck_2277_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v_traceState_2251_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2277_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2268_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2268_);
v___x_2270_ = v___x_2266_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2268_);
lean_ctor_set_uint64(v_reuseFailAlloc_2276_, sizeof(void*)*1, v_tid_2264_);
v___x_2270_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 4, v___x_2270_);
v___x_2272_ = v___x_2262_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_env_2252_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_nextMacroScope_2253_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_ngen_2254_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v_auxDeclNGen_2255_);
lean_ctor_set(v_reuseFailAlloc_2275_, 4, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2275_, 5, v_cache_2256_);
lean_ctor_set(v_reuseFailAlloc_2275_, 6, v_recordedDeps_2257_);
lean_ctor_set(v_reuseFailAlloc_2275_, 7, v_messages_2258_);
lean_ctor_set(v_reuseFailAlloc_2275_, 8, v_infoState_2259_);
lean_ctor_set(v_reuseFailAlloc_2275_, 9, v_snapshotTasks_2260_);
v___x_2272_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_st_ref_put(v___y_2245_, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_traces_2249_);
return v___x_2274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2280_);
lean_dec(v___y_2280_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
return v_res_2294_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2295_, lean_object* v_opt_2296_){
_start:
{
lean_object* v_name_2297_; lean_object* v_defValue_2298_; lean_object* v_map_2299_; lean_object* v___x_2300_; 
v_name_2297_ = lean_ctor_get(v_opt_2296_, 0);
v_defValue_2298_ = lean_ctor_get(v_opt_2296_, 1);
v_map_2299_ = lean_ctor_get(v_opts_2295_, 0);
v___x_2300_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2299_, v_name_2297_);
if (lean_obj_tag(v___x_2300_) == 0)
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_unbox(v_defValue_2298_);
return v___x_2301_;
}
else
{
lean_object* v_val_2302_; 
v_val_2302_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_val_2302_);
lean_dec_ref_known(v___x_2300_, 1);
if (lean_obj_tag(v_val_2302_) == 1)
{
uint8_t v_v_2303_; 
v_v_2303_ = lean_ctor_get_uint8(v_val_2302_, 0);
lean_dec_ref_known(v_val_2302_, 0);
return v_v_2303_;
}
else
{
uint8_t v___x_2304_; 
lean_dec(v_val_2302_);
v___x_2304_ = lean_unbox(v_defValue_2298_);
return v___x_2304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2305_, lean_object* v_opt_2306_){
_start:
{
uint8_t v_res_2307_; lean_object* v_r_2308_; 
v_res_2307_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2305_, v_opt_2306_);
lean_dec_ref(v_opt_2306_);
lean_dec_ref(v_opts_2305_);
v_r_2308_ = lean_box(v_res_2307_);
return v_r_2308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2311_ = l_Lean_stringToMessageData(v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2312_, lean_object* v_x_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2319_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2320_ = l_Lean_MessageData_ofName(v_name_2312_);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2325_, lean_object* v_x_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2325_, v_x_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec_ref(v_x_2326_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2333_, lean_object* v_val_2334_, lean_object* v_name_2335_, lean_object* v_levelParams_2336_, uint8_t v___x_2337_, lean_object* v_____r_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v___x_2344_; 
lean_inc_ref(v_val_2334_);
v___x_2344_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2333_, v_val_2334_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v_a_2347_; lean_object* v___x_2348_; lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2361_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2334_, v___y_2340_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref(v___x_2346_);
v___x_2348_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2345_, v___y_2340_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2361_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2361_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
lean_inc(v_name_2335_);
v___x_2353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2353_, 0, v_name_2335_);
lean_ctor_set(v___x_2353_, 1, v_levelParams_2336_);
lean_ctor_set(v___x_2353_, 2, v_a_2347_);
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_name_2335_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2353_);
lean_ctor_set(v___x_2356_, 1, v_a_2349_);
lean_ctor_set(v___x_2356_, 2, v___x_2355_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 2);
lean_ctor_set(v___x_2351_, 0, v___x_2356_);
v___x_2358_ = v___x_2351_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_addDecl(v___x_2358_, v___x_2337_, v___y_2341_, v___y_2342_);
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_levelParams_2336_);
lean_dec(v_name_2335_);
lean_dec_ref(v_val_2334_);
v_a_2362_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2344_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2344_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2370_, lean_object* v_val_2371_, lean_object* v_name_2372_, lean_object* v_levelParams_2373_, lean_object* v___x_2374_, lean_object* v_____r_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
uint8_t v___x_12478__boxed_2381_; lean_object* v_res_2382_; 
v___x_12478__boxed_2381_ = lean_unbox(v___x_2374_);
v_res_2382_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2370_, v_val_2371_, v_name_2372_, v_levelParams_2373_, v___x_12478__boxed_2381_, v_____r_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2383_, lean_object* v_val_2384_, lean_object* v_name_2385_, lean_object* v_levelParams_2386_, lean_object* v_____r_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2393_; 
lean_inc_ref(v_val_2384_);
v___x_2393_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2383_, v_val_2384_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v_a_2396_; lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2411_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2384_, v___y_2389_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2394_, v___y_2389_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2411_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2411_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
lean_inc(v_name_2385_);
v___x_2402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2402_, 0, v_name_2385_);
lean_ctor_set(v___x_2402_, 1, v_levelParams_2386_);
lean_ctor_set(v___x_2402_, 2, v_a_2396_);
v___x_2403_ = lean_box(0);
v___x_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2404_, 0, v_name_2385_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2402_);
lean_ctor_set(v___x_2405_, 1, v_a_2398_);
lean_ctor_set(v___x_2405_, 2, v___x_2404_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set_tag(v___x_2400_, 2);
lean_ctor_set(v___x_2400_, 0, v___x_2405_);
v___x_2407_ = v___x_2400_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
uint8_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = 0;
v___x_2409_ = l_Lean_addDecl(v___x_2407_, v___x_2408_, v___y_2390_, v___y_2391_);
return v___x_2409_;
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_levelParams_2386_);
lean_dec(v_name_2385_);
lean_dec_ref(v_val_2384_);
v_a_2412_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2393_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2393_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2420_, lean_object* v_val_2421_, lean_object* v_name_2422_, lean_object* v_levelParams_2423_, lean_object* v_____r_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2420_, v_val_2421_, v_name_2422_, v_levelParams_2423_, v_____r_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t v_sz_2431_, size_t v_i_2432_, lean_object* v_bs_2433_){
_start:
{
uint8_t v___x_2434_; 
v___x_2434_ = lean_usize_dec_lt(v_i_2432_, v_sz_2431_);
if (v___x_2434_ == 0)
{
return v_bs_2433_;
}
else
{
lean_object* v_v_2435_; lean_object* v_msg_2436_; lean_object* v___x_2437_; lean_object* v_bs_x27_2438_; size_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; 
v_v_2435_ = lean_array_uget_borrowed(v_bs_2433_, v_i_2432_);
v_msg_2436_ = lean_ctor_get(v_v_2435_, 1);
lean_inc_ref(v_msg_2436_);
v___x_2437_ = lean_unsigned_to_nat(0u);
v_bs_x27_2438_ = lean_array_uset(v_bs_2433_, v_i_2432_, v___x_2437_);
v___x_2439_ = ((size_t)1ULL);
v___x_2440_ = lean_usize_add(v_i_2432_, v___x_2439_);
v___x_2441_ = lean_array_uset(v_bs_x27_2438_, v_i_2432_, v_msg_2436_);
v_i_2432_ = v___x_2440_;
v_bs_2433_ = v___x_2441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2443_, lean_object* v_i_2444_, lean_object* v_bs_2445_){
_start:
{
size_t v_sz_boxed_2446_; size_t v_i_boxed_2447_; lean_object* v_res_2448_; 
v_sz_boxed_2446_ = lean_unbox_usize(v_sz_2443_);
lean_dec(v_sz_2443_);
v_i_boxed_2447_ = lean_unbox_usize(v_i_2444_);
lean_dec(v_i_2444_);
v_res_2448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_boxed_2446_, v_i_boxed_2447_, v_bs_2445_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_oldTraces_2449_, lean_object* v_data_2450_, lean_object* v_ref_2451_, lean_object* v_msg_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_toCold_2458_; lean_object* v_currRecDepth_2459_; lean_object* v_ref_2460_; uint16_t v_optionFlags_2461_; uint8_t v_suppressElabErrors_2462_; uint8_t v_isRecordingDeps_2463_; lean_object* v_ref_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v_traceState_2467_; lean_object* v_traces_2468_; lean_object* v___x_2469_; size_t v_sz_2470_; size_t v___x_2471_; lean_object* v___x_2472_; lean_object* v_msg_2473_; lean_object* v___x_2474_; lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2513_; 
v_toCold_2458_ = lean_ctor_get(v___y_2455_, 0);
v_currRecDepth_2459_ = lean_ctor_get(v___y_2455_, 1);
v_ref_2460_ = lean_ctor_get(v___y_2455_, 2);
v_optionFlags_2461_ = lean_ctor_get_uint16(v___y_2455_, sizeof(void*)*3);
v_suppressElabErrors_2462_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2463_ = lean_ctor_get_uint8(v___y_2455_, sizeof(void*)*3 + 3);
v_ref_2464_ = l_Lean_replaceRef(v_ref_2451_, v_ref_2460_);
lean_inc(v_currRecDepth_2459_);
lean_inc_ref(v_toCold_2458_);
v___x_2465_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2465_, 0, v_toCold_2458_);
lean_ctor_set(v___x_2465_, 1, v_currRecDepth_2459_);
lean_ctor_set(v___x_2465_, 2, v_ref_2464_);
lean_ctor_set_uint16(v___x_2465_, sizeof(void*)*3, v_optionFlags_2461_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*3 + 2, v_suppressElabErrors_2462_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*3 + 3, v_isRecordingDeps_2463_);
v___x_2466_ = lean_st_ref_get(v___y_2456_);
v_traceState_2467_ = lean_ctor_get(v___x_2466_, 4);
lean_inc_ref(v_traceState_2467_);
lean_dec(v___x_2466_);
v_traces_2468_ = lean_ctor_get(v_traceState_2467_, 0);
lean_inc_ref(v_traces_2468_);
lean_dec_ref(v_traceState_2467_);
v___x_2469_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2468_);
lean_dec_ref(v_traces_2468_);
v_sz_2470_ = lean_array_size(v___x_2469_);
v___x_2471_ = ((size_t)0ULL);
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_2470_, v___x_2471_, v___x_2469_);
v_msg_2473_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2473_, 0, v_data_2450_);
lean_ctor_set(v_msg_2473_, 1, v_msg_2452_);
lean_ctor_set(v_msg_2473_, 2, v___x_2472_);
v___x_2474_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2473_, v___y_2453_, v___y_2454_, v___x_2465_, v___y_2456_);
lean_dec_ref_known(v___x_2465_, 3);
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2477_ = v___x_2474_;
v_isShared_2478_ = v_isSharedCheck_2513_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2474_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2513_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v_traceState_2480_; lean_object* v_env_2481_; lean_object* v_nextMacroScope_2482_; lean_object* v_ngen_2483_; lean_object* v_auxDeclNGen_2484_; lean_object* v_cache_2485_; lean_object* v_recordedDeps_2486_; lean_object* v_messages_2487_; lean_object* v_infoState_2488_; lean_object* v_snapshotTasks_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2512_; 
v___x_2479_ = lean_st_ref_take(v___y_2456_);
v_traceState_2480_ = lean_ctor_get(v___x_2479_, 4);
v_env_2481_ = lean_ctor_get(v___x_2479_, 0);
v_nextMacroScope_2482_ = lean_ctor_get(v___x_2479_, 1);
v_ngen_2483_ = lean_ctor_get(v___x_2479_, 2);
v_auxDeclNGen_2484_ = lean_ctor_get(v___x_2479_, 3);
v_cache_2485_ = lean_ctor_get(v___x_2479_, 5);
v_recordedDeps_2486_ = lean_ctor_get(v___x_2479_, 6);
v_messages_2487_ = lean_ctor_get(v___x_2479_, 7);
v_infoState_2488_ = lean_ctor_get(v___x_2479_, 8);
v_snapshotTasks_2489_ = lean_ctor_get(v___x_2479_, 9);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2491_ = v___x_2479_;
v_isShared_2492_ = v_isSharedCheck_2512_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_snapshotTasks_2489_);
lean_inc(v_infoState_2488_);
lean_inc(v_messages_2487_);
lean_inc(v_recordedDeps_2486_);
lean_inc(v_cache_2485_);
lean_inc(v_traceState_2480_);
lean_inc(v_auxDeclNGen_2484_);
lean_inc(v_ngen_2483_);
lean_inc(v_nextMacroScope_2482_);
lean_inc(v_env_2481_);
lean_dec(v___x_2479_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2512_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
uint64_t v_tid_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2510_; 
v_tid_2493_ = lean_ctor_get_uint64(v_traceState_2480_, sizeof(void*)*1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_traceState_2480_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; 
v_unused_2511_ = lean_ctor_get(v_traceState_2480_, 0);
lean_dec(v_unused_2511_);
v___x_2495_ = v_traceState_2480_;
v_isShared_2496_ = v_isSharedCheck_2510_;
goto v_resetjp_2494_;
}
else
{
lean_dec(v_traceState_2480_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2510_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2497_ = lean_box(0);
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_ref_2451_);
lean_ctor_set(v___x_2498_, 1, v_a_2475_);
v___x_2499_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2449_, v___x_2498_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2499_);
v___x_2501_ = v___x_2495_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2499_);
lean_ctor_set_uint64(v_reuseFailAlloc_2509_, sizeof(void*)*1, v_tid_2493_);
v___x_2501_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2503_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v___x_2501_);
v___x_2503_ = v___x_2491_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_env_2481_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_nextMacroScope_2482_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_ngen_2483_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_auxDeclNGen_2484_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2508_, 5, v_cache_2485_);
lean_ctor_set(v_reuseFailAlloc_2508_, 6, v_recordedDeps_2486_);
lean_ctor_set(v_reuseFailAlloc_2508_, 7, v_messages_2487_);
lean_ctor_set(v_reuseFailAlloc_2508_, 8, v_infoState_2488_);
lean_ctor_set(v_reuseFailAlloc_2508_, 9, v_snapshotTasks_2489_);
v___x_2503_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = lean_st_ref_put(v___y_2456_, v___x_2503_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2497_);
v___x_2506_ = v___x_2477_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2497_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_oldTraces_2514_, lean_object* v_data_2515_, lean_object* v_ref_2516_, lean_object* v_msg_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2514_, v_data_2515_, v_ref_2516_, v_msg_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2524_, lean_object* v_opt_2525_){
_start:
{
lean_object* v_name_2526_; lean_object* v_defValue_2527_; lean_object* v_map_2528_; lean_object* v___x_2529_; 
v_name_2526_ = lean_ctor_get(v_opt_2525_, 0);
v_defValue_2527_ = lean_ctor_get(v_opt_2525_, 1);
v_map_2528_ = lean_ctor_get(v_opts_2524_, 0);
v___x_2529_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2528_, v_name_2526_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_inc(v_defValue_2527_);
return v_defValue_2527_;
}
else
{
lean_object* v_val_2530_; 
v_val_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_val_2530_);
lean_dec_ref_known(v___x_2529_, 1);
if (lean_obj_tag(v_val_2530_) == 3)
{
lean_object* v_v_2531_; 
v_v_2531_ = lean_ctor_get(v_val_2530_, 0);
lean_inc(v_v_2531_);
lean_dec_ref_known(v_val_2530_, 1);
return v_v_2531_;
}
else
{
lean_dec(v_val_2530_);
lean_inc(v_defValue_2527_);
return v_defValue_2527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2532_, lean_object* v_opt_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2532_, v_opt_2533_);
lean_dec_ref(v_opt_2533_);
lean_dec_ref(v_opts_2532_);
return v_res_2534_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_e_2535_){
_start:
{
if (lean_obj_tag(v_e_2535_) == 0)
{
uint8_t v___x_2536_; 
v___x_2536_ = 2;
return v___x_2536_;
}
else
{
uint8_t v___x_2537_; 
v___x_2537_ = 0;
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_e_2538_){
_start:
{
uint8_t v_res_2539_; lean_object* v_r_2540_; 
v_res_2539_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_e_2538_);
lean_dec_ref(v_e_2538_);
v_r_2540_ = lean_box(v_res_2539_);
return v_r_2540_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object* v_x_2541_){
_start:
{
if (lean_obj_tag(v_x_2541_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_a_2543_ = lean_ctor_get(v_x_2541_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_x_2541_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v_x_2541_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v_x_2541_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set_tag(v___x_2545_, 1);
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_a_2551_ = lean_ctor_get(v_x_2541_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_x_2541_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v_x_2541_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v_x_2541_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set_tag(v___x_2553_, 0);
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object* v_x_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2559_);
return v_res_2561_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2564_ = l_Lean_stringToMessageData(v___x_2563_);
return v___x_2564_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2565_; double v___x_2566_; 
v___x_2565_ = lean_unsigned_to_nat(1000u);
v___x_2566_ = lean_float_of_nat(v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2567_, uint8_t v_collapsed_2568_, lean_object* v_tag_2569_, lean_object* v_opts_2570_, uint8_t v_clsEnabled_2571_, lean_object* v_oldTraces_2572_, lean_object* v_msg_2573_, lean_object* v_resStartStop_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_fst_2580_; lean_object* v_snd_2581_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v_data_2585_; lean_object* v_fst_2588_; lean_object* v_snd_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___y_2593_; lean_object* v_a_2594_; uint8_t v___y_2609_; double v___y_2641_; 
v_fst_2580_ = lean_ctor_get(v_resStartStop_2574_, 0);
lean_inc(v_fst_2580_);
v_snd_2581_ = lean_ctor_get(v_resStartStop_2574_, 1);
lean_inc(v_snd_2581_);
lean_dec_ref(v_resStartStop_2574_);
v_fst_2588_ = lean_ctor_get(v_snd_2581_, 0);
lean_inc(v_fst_2588_);
v_snd_2589_ = lean_ctor_get(v_snd_2581_, 1);
lean_inc(v_snd_2589_);
lean_dec(v_snd_2581_);
v___x_2590_ = l_Lean_trace_profiler;
v___x_2591_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2570_, v___x_2590_);
if (v___x_2591_ == 0)
{
v___y_2609_ = v___x_2591_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2647_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2570_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; double v___x_2650_; double v___x_2651_; double v___x_2652_; 
v___x_2648_ = l_Lean_trace_profiler_threshold;
v___x_2649_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2570_, v___x_2648_);
v___x_2650_ = lean_float_of_nat(v___x_2649_);
v___x_2651_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2);
v___x_2652_ = lean_float_div(v___x_2650_, v___x_2651_);
v___y_2641_ = v___x_2652_;
goto v___jp_2640_;
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; double v___x_2655_; 
v___x_2653_ = l_Lean_trace_profiler_threshold;
v___x_2654_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2570_, v___x_2653_);
v___x_2655_ = lean_float_of_nat(v___x_2654_);
v___y_2641_ = v___x_2655_;
goto v___jp_2640_;
}
}
v___jp_2582_:
{
lean_object* v___x_2586_; 
lean_inc(v___y_2584_);
v___x_2586_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2572_, v_data_2585_, v___y_2584_, v___y_2583_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v___x_2587_; 
lean_dec_ref_known(v___x_2586_, 1);
v___x_2587_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2580_);
return v___x_2587_;
}
else
{
lean_dec(v_fst_2580_);
return v___x_2586_;
}
}
v___jp_2592_:
{
uint8_t v_result_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; double v___x_2598_; lean_object* v_data_2599_; 
v_result_2595_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_fst_2580_);
v___x_2596_ = lean_box(v_result_2595_);
v___x_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
v___x_2598_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2569_);
lean_inc_ref(v___x_2597_);
lean_inc(v_cls_2567_);
v_data_2599_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2599_, 0, v_cls_2567_);
lean_ctor_set(v_data_2599_, 1, v___x_2597_);
lean_ctor_set(v_data_2599_, 2, v_tag_2569_);
lean_ctor_set_float(v_data_2599_, sizeof(void*)*3, v___x_2598_);
lean_ctor_set_float(v_data_2599_, sizeof(void*)*3 + 8, v___x_2598_);
lean_ctor_set_uint8(v_data_2599_, sizeof(void*)*3 + 16, v_collapsed_2568_);
if (v___x_2591_ == 0)
{
lean_dec_ref_known(v___x_2597_, 1);
lean_dec(v_snd_2589_);
lean_dec(v_fst_2588_);
lean_dec_ref(v_tag_2569_);
lean_dec(v_cls_2567_);
v___y_2583_ = v_a_2594_;
v___y_2584_ = v___y_2593_;
v_data_2585_ = v_data_2599_;
goto v___jp_2582_;
}
else
{
lean_object* v_data_2600_; double v___x_2601_; double v___x_2602_; 
lean_dec_ref_known(v_data_2599_, 3);
v_data_2600_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2600_, 0, v_cls_2567_);
lean_ctor_set(v_data_2600_, 1, v___x_2597_);
lean_ctor_set(v_data_2600_, 2, v_tag_2569_);
v___x_2601_ = lean_unbox_float(v_fst_2588_);
lean_dec(v_fst_2588_);
lean_ctor_set_float(v_data_2600_, sizeof(void*)*3, v___x_2601_);
v___x_2602_ = lean_unbox_float(v_snd_2589_);
lean_dec(v_snd_2589_);
lean_ctor_set_float(v_data_2600_, sizeof(void*)*3 + 8, v___x_2602_);
lean_ctor_set_uint8(v_data_2600_, sizeof(void*)*3 + 16, v_collapsed_2568_);
v___y_2583_ = v_a_2594_;
v___y_2584_ = v___y_2593_;
v_data_2585_ = v_data_2600_;
goto v___jp_2582_;
}
}
v___jp_2603_:
{
lean_object* v_ref_2604_; lean_object* v___x_2605_; 
v_ref_2604_ = lean_ctor_get(v___y_2577_, 2);
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v_fst_2580_);
v___x_2605_ = lean_apply_6(v_msg_2573_, v_fst_2580_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, lean_box(0));
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___y_2593_ = v_ref_2604_;
v_a_2594_ = v_a_2606_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2607_; 
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
v___y_2593_ = v_ref_2604_;
v_a_2594_ = v___x_2607_;
goto v___jp_2592_;
}
}
v___jp_2608_:
{
if (v_clsEnabled_2571_ == 0)
{
if (v___y_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v_traceState_2611_; lean_object* v_env_2612_; lean_object* v_nextMacroScope_2613_; lean_object* v_ngen_2614_; lean_object* v_auxDeclNGen_2615_; lean_object* v_cache_2616_; lean_object* v_recordedDeps_2617_; lean_object* v_messages_2618_; lean_object* v_infoState_2619_; lean_object* v_snapshotTasks_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_snd_2589_);
lean_dec(v_fst_2588_);
lean_dec_ref(v_msg_2573_);
lean_dec_ref(v_tag_2569_);
lean_dec(v_cls_2567_);
v___x_2610_ = lean_st_ref_take(v___y_2578_);
v_traceState_2611_ = lean_ctor_get(v___x_2610_, 4);
v_env_2612_ = lean_ctor_get(v___x_2610_, 0);
v_nextMacroScope_2613_ = lean_ctor_get(v___x_2610_, 1);
v_ngen_2614_ = lean_ctor_get(v___x_2610_, 2);
v_auxDeclNGen_2615_ = lean_ctor_get(v___x_2610_, 3);
v_cache_2616_ = lean_ctor_get(v___x_2610_, 5);
v_recordedDeps_2617_ = lean_ctor_get(v___x_2610_, 6);
v_messages_2618_ = lean_ctor_get(v___x_2610_, 7);
v_infoState_2619_ = lean_ctor_get(v___x_2610_, 8);
v_snapshotTasks_2620_ = lean_ctor_get(v___x_2610_, 9);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2622_ = v___x_2610_;
v_isShared_2623_ = v_isSharedCheck_2639_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_snapshotTasks_2620_);
lean_inc(v_infoState_2619_);
lean_inc(v_messages_2618_);
lean_inc(v_recordedDeps_2617_);
lean_inc(v_cache_2616_);
lean_inc(v_traceState_2611_);
lean_inc(v_auxDeclNGen_2615_);
lean_inc(v_ngen_2614_);
lean_inc(v_nextMacroScope_2613_);
lean_inc(v_env_2612_);
lean_dec(v___x_2610_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2639_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
uint64_t v_tid_2624_; lean_object* v_traces_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2638_; 
v_tid_2624_ = lean_ctor_get_uint64(v_traceState_2611_, sizeof(void*)*1);
v_traces_2625_ = lean_ctor_get(v_traceState_2611_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_traceState_2611_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2627_ = v_traceState_2611_;
v_isShared_2628_ = v_isSharedCheck_2638_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_traces_2625_);
lean_dec(v_traceState_2611_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2638_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2629_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2572_, v_traces_2625_);
lean_dec_ref(v_traces_2625_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2629_);
v___x_2631_ = v___x_2627_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2629_);
lean_ctor_set_uint64(v_reuseFailAlloc_2637_, sizeof(void*)*1, v_tid_2624_);
v___x_2631_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v___x_2631_);
v___x_2633_ = v___x_2622_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_env_2612_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_nextMacroScope_2613_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_ngen_2614_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_auxDeclNGen_2615_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2636_, 5, v_cache_2616_);
lean_ctor_set(v_reuseFailAlloc_2636_, 6, v_recordedDeps_2617_);
lean_ctor_set(v_reuseFailAlloc_2636_, 7, v_messages_2618_);
lean_ctor_set(v_reuseFailAlloc_2636_, 8, v_infoState_2619_);
lean_ctor_set(v_reuseFailAlloc_2636_, 9, v_snapshotTasks_2620_);
v___x_2633_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_st_ref_put(v___y_2578_, v___x_2633_);
v___x_2635_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2580_);
return v___x_2635_;
}
}
}
}
}
else
{
goto v___jp_2603_;
}
}
else
{
goto v___jp_2603_;
}
}
v___jp_2640_:
{
double v___x_2642_; double v___x_2643_; double v___x_2644_; uint8_t v___x_2645_; 
v___x_2642_ = lean_unbox_float(v_snd_2589_);
v___x_2643_ = lean_unbox_float(v_fst_2588_);
v___x_2644_ = lean_float_sub(v___x_2642_, v___x_2643_);
v___x_2645_ = lean_float_decLt(v___y_2641_, v___x_2644_);
v___y_2609_ = v___x_2645_;
goto v___jp_2608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2656_, lean_object* v_collapsed_2657_, lean_object* v_tag_2658_, lean_object* v_opts_2659_, lean_object* v_clsEnabled_2660_, lean_object* v_oldTraces_2661_, lean_object* v_msg_2662_, lean_object* v_resStartStop_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v_collapsed_boxed_2669_; uint8_t v_clsEnabled_boxed_2670_; lean_object* v_res_2671_; 
v_collapsed_boxed_2669_ = lean_unbox(v_collapsed_2657_);
v_clsEnabled_boxed_2670_ = lean_unbox(v_clsEnabled_2660_);
v_res_2671_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2656_, v_collapsed_boxed_2669_, v_tag_2658_, v_opts_2659_, v_clsEnabled_boxed_2670_, v_oldTraces_2661_, v_msg_2662_, v_resStartStop_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec_ref(v_opts_2659_);
return v_res_2671_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2672_; double v___x_2673_; 
v___x_2672_ = lean_unsigned_to_nat(1000000000u);
v___x_2673_ = lean_float_of_nat(v___x_2672_);
return v___x_2673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2676_ = l_Lean_stringToMessageData(v___x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_toConstantVal_2683_; lean_object* v_toCold_2684_; lean_object* v_options_2685_; lean_object* v_name_2686_; lean_object* v_levelParams_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2898_; 
v_toConstantVal_2683_ = lean_ctor_get(v_ctorVal_2677_, 0);
lean_inc_ref(v_toConstantVal_2683_);
v_toCold_2684_ = lean_ctor_get(v_a_2680_, 0);
v_options_2685_ = lean_ctor_get(v_toCold_2684_, 2);
v_name_2686_ = lean_ctor_get(v_toConstantVal_2683_, 0);
v_levelParams_2687_ = lean_ctor_get(v_toConstantVal_2683_, 1);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_toConstantVal_2683_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v_toConstantVal_2683_, 2);
lean_dec(v_unused_2899_);
v___x_2689_ = v_toConstantVal_2683_;
v_isShared_2690_ = v_isSharedCheck_2898_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_levelParams_2687_);
lean_inc(v_name_2686_);
lean_dec(v_toConstantVal_2683_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2898_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v_inheritedTraceOptions_2691_; uint8_t v_hasTrace_2692_; lean_object* v_name_2693_; 
v_inheritedTraceOptions_2691_ = lean_ctor_get(v_toCold_2684_, 11);
v_hasTrace_2692_ = lean_ctor_get_uint8(v_options_2685_, sizeof(void*)*1);
lean_inc(v_name_2686_);
v_name_2693_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2686_);
if (v_hasTrace_2692_ == 0)
{
lean_object* v___x_2694_; 
v___x_2694_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2732_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2732_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2732_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
if (lean_obj_tag(v_a_2695_) == 1)
{
lean_object* v_val_2699_; lean_object* v___x_2700_; 
lean_del_object(v___x_2697_);
v_val_2699_ = lean_ctor_get(v_a_2695_, 0);
lean_inc_n(v_val_2699_, 2);
lean_dec_ref_known(v_a_2695_, 1);
v___x_2700_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2686_, v_val_2699_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2702_; lean_object* v_a_2703_; lean_object* v___x_2704_; lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2719_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
v___x_2702_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2699_, v_a_2679_);
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref(v___x_2702_);
v___x_2704_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2701_, v_a_2679_);
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2707_ = v___x_2704_;
v_isShared_2708_ = v_isSharedCheck_2719_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2719_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
lean_inc(v_name_2693_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 2, v_a_2703_);
lean_ctor_set(v___x_2689_, 0, v_name_2693_);
v___x_2710_ = v___x_2689_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_name_2693_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_levelParams_2687_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v_a_2703_);
v___x_2710_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_name_2693_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2710_);
lean_ctor_set(v___x_2713_, 1, v_a_2705_);
lean_ctor_set(v___x_2713_, 2, v___x_2712_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set_tag(v___x_2707_, 2);
lean_ctor_set(v___x_2707_, 0, v___x_2713_);
v___x_2715_ = v___x_2707_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_addDecl(v___x_2715_, v_hasTrace_2692_, v_a_2680_, v_a_2681_);
return v___x_2716_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_val_2699_);
lean_dec(v_name_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_levelParams_2687_);
v_a_2720_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2700_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2700_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2730_; 
lean_dec(v_a_2695_);
lean_dec(v_name_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v___x_2728_ = lean_box(0);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2728_);
v___x_2730_ = v___x_2697_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_name_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v_a_2733_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2694_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2694_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v___f_2741_; lean_object* v_cls_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v_a_2749_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v_a_2761_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v_a_2766_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v_a_2777_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v_a_2792_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v_a_2797_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; 
lean_inc(v_name_2693_);
v___f_2741_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2741_, 0, v_name_2693_);
v_cls_2742_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2743_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2744_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2745_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2691_, v_options_2685_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2840_ = l_Lean_trace_profiler;
v___x_2841_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2685_, v___x_2840_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
lean_dec_ref(v___f_2741_);
v___x_2842_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2889_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2889_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2889_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
if (lean_obj_tag(v_a_2843_) == 1)
{
lean_object* v_val_2847_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; 
lean_del_object(v___x_2845_);
v_val_2847_ = lean_ctor_get(v_a_2843_, 0);
lean_inc(v_val_2847_);
lean_dec_ref_known(v_a_2843_, 1);
if (v___x_2745_ == 0)
{
v___y_2849_ = v_a_2678_;
v___y_2850_ = v_a_2679_;
v___y_2851_ = v_a_2680_;
v___y_2852_ = v_a_2681_;
goto v___jp_2848_;
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2881_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2847_);
v___x_2882_ = l_Lean_MessageData_ofExpr(v_val_2847_);
v___x_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2742_, v___x_2883_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_dec_ref_known(v___x_2884_, 1);
v___y_2849_ = v_a_2678_;
v___y_2850_ = v_a_2679_;
v___y_2851_ = v_a_2680_;
v___y_2852_ = v_a_2681_;
goto v___jp_2848_;
}
else
{
lean_dec(v_val_2847_);
lean_dec(v_name_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
return v___x_2884_;
}
}
v___jp_2848_:
{
lean_object* v___x_2853_; 
lean_inc(v_val_2847_);
v___x_2853_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2686_, v_val_2847_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2855_; lean_object* v_a_2856_; lean_object* v___x_2857_; lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2872_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2855_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2847_, v___y_2850_);
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2855_);
v___x_2857_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2854_, v___y_2850_);
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2872_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2872_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
lean_inc(v_name_2693_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 2, v_a_2856_);
lean_ctor_set(v___x_2689_, 0, v_name_2693_);
v___x_2863_ = v___x_2689_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_name_2693_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_levelParams_2687_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_a_2856_);
v___x_2863_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2865_, 0, v_name_2693_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2863_);
lean_ctor_set(v___x_2866_, 1, v_a_2858_);
lean_ctor_set(v___x_2866_, 2, v___x_2865_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 2);
lean_ctor_set(v___x_2860_, 0, v___x_2866_);
v___x_2868_ = v___x_2860_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_addDecl(v___x_2868_, v___x_2841_, v___y_2851_, v___y_2852_);
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec(v_val_2847_);
lean_dec(v_name_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_levelParams_2687_);
v_a_2873_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2853_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2853_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
else
{
lean_object* v___x_2885_; lean_object* v___x_2887_; 
lean_dec(v_a_2843_);
lean_dec(v_name_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v___x_2885_ = lean_box(0);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2885_);
v___x_2887_ = v___x_2845_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2885_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_name_2693_);
lean_del_object(v___x_2689_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v_a_2890_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2842_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2842_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_del_object(v___x_2689_);
goto v___jp_2805_;
}
}
else
{
lean_del_object(v___x_2689_);
goto v___jp_2805_;
}
v___jp_2746_:
{
lean_object* v___x_2750_; double v___x_2751_; double v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2750_ = lean_io_get_num_heartbeats();
v___x_2751_ = lean_float_of_nat(v___y_2748_);
v___x_2752_ = lean_float_of_nat(v___x_2750_);
v___x_2753_ = lean_box_float(v___x_2751_);
v___x_2754_ = lean_box_float(v___x_2752_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_a_2749_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2742_, v_hasTrace_2692_, v___x_2743_, v_options_2685_, v___x_2745_, v___y_2747_, v___f_2741_, v___x_2756_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
return v___x_2757_;
}
v___jp_2758_:
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v_a_2761_);
v___y_2747_ = v___y_2759_;
v___y_2748_ = v___y_2760_;
v_a_2749_ = v___x_2762_;
goto v___jp_2746_;
}
v___jp_2763_:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v_a_2766_);
v___y_2747_ = v___y_2764_;
v___y_2748_ = v___y_2765_;
v_a_2749_ = v___x_2767_;
goto v___jp_2746_;
}
v___jp_2768_:
{
if (lean_obj_tag(v___y_2771_) == 0)
{
lean_object* v_a_2772_; 
v_a_2772_ = lean_ctor_get(v___y_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___y_2771_, 1);
v___y_2764_ = v___y_2769_;
v___y_2765_ = v___y_2770_;
v_a_2766_ = v_a_2772_;
goto v___jp_2763_;
}
else
{
lean_object* v_a_2773_; 
v_a_2773_ = lean_ctor_get(v___y_2771_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___y_2771_, 1);
v___y_2759_ = v___y_2769_;
v___y_2760_ = v___y_2770_;
v_a_2761_ = v_a_2773_;
goto v___jp_2758_;
}
}
v___jp_2774_:
{
lean_object* v___x_2778_; double v___x_2779_; double v___x_2780_; double v___x_2781_; double v___x_2782_; double v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2778_ = lean_io_mono_nanos_now();
v___x_2779_ = lean_float_of_nat(v___y_2776_);
v___x_2780_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2781_ = lean_float_div(v___x_2779_, v___x_2780_);
v___x_2782_ = lean_float_of_nat(v___x_2778_);
v___x_2783_ = lean_float_div(v___x_2782_, v___x_2780_);
v___x_2784_ = lean_box_float(v___x_2781_);
v___x_2785_ = lean_box_float(v___x_2783_);
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v_a_2777_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2742_, v_hasTrace_2692_, v___x_2743_, v_options_2685_, v___x_2745_, v___y_2775_, v___f_2741_, v___x_2787_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
return v___x_2788_;
}
v___jp_2789_:
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_a_2792_);
v___y_2775_ = v___y_2790_;
v___y_2776_ = v___y_2791_;
v_a_2777_ = v___x_2793_;
goto v___jp_2774_;
}
v___jp_2794_:
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2798_, 0, v_a_2797_);
v___y_2775_ = v___y_2795_;
v___y_2776_ = v___y_2796_;
v_a_2777_ = v___x_2798_;
goto v___jp_2774_;
}
v___jp_2799_:
{
if (lean_obj_tag(v___y_2802_) == 0)
{
lean_object* v_a_2803_; 
v_a_2803_ = lean_ctor_get(v___y_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___y_2802_, 1);
v___y_2790_ = v___y_2800_;
v___y_2791_ = v___y_2801_;
v_a_2792_ = v_a_2803_;
goto v___jp_2789_;
}
else
{
lean_object* v_a_2804_; 
v_a_2804_ = lean_ctor_get(v___y_2802_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___y_2802_, 1);
v___y_2795_ = v___y_2800_;
v___y_2796_ = v___y_2801_;
v_a_2797_ = v_a_2804_;
goto v___jp_2794_;
}
}
v___jp_2805_:
{
lean_object* v___x_2806_; lean_object* v_a_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2806_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2681_);
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref(v___x_2806_);
v___x_2808_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2809_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2685_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_io_mono_nanos_now();
v___x_2811_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
if (lean_obj_tag(v_a_2812_) == 1)
{
if (v___x_2745_ == 0)
{
lean_object* v_val_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_val_2813_ = lean_ctor_get(v_a_2812_, 0);
lean_inc(v_val_2813_);
lean_dec_ref_known(v_a_2812_, 1);
v___x_2814_ = lean_box(0);
v___x_2815_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2686_, v_val_2813_, v_name_2693_, v_levelParams_2687_, v___x_2809_, v___x_2814_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
v___y_2800_ = v_a_2807_;
v___y_2801_ = v___x_2810_;
v___y_2802_ = v___x_2815_;
goto v___jp_2799_;
}
else
{
lean_object* v_val_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_val_2816_ = lean_ctor_get(v_a_2812_, 0);
lean_inc_n(v_val_2816_, 2);
lean_dec_ref_known(v_a_2812_, 1);
v___x_2817_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2818_ = l_Lean_MessageData_ofExpr(v_val_2816_);
v___x_2819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2742_, v___x_2819_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2686_, v_val_2816_, v_name_2693_, v_levelParams_2687_, v___x_2809_, v_a_2821_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
v___y_2800_ = v_a_2807_;
v___y_2801_ = v___x_2810_;
v___y_2802_ = v___x_2822_;
goto v___jp_2799_;
}
else
{
lean_dec(v_val_2816_);
lean_dec(v_name_2693_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v___y_2800_ = v_a_2807_;
v___y_2801_ = v___x_2810_;
v___y_2802_ = v___x_2820_;
goto v___jp_2799_;
}
}
}
else
{
lean_object* v___x_2823_; 
lean_dec(v_a_2812_);
lean_dec(v_name_2693_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v___x_2823_ = lean_box(0);
v___y_2790_ = v_a_2807_;
v___y_2791_ = v___x_2810_;
v_a_2792_ = v___x_2823_;
goto v___jp_2789_;
}
}
else
{
lean_object* v_a_2824_; 
lean_dec(v_name_2693_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v_a_2824_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2811_, 1);
v___y_2795_ = v_a_2807_;
v___y_2796_ = v___x_2810_;
v_a_2797_ = v_a_2824_;
goto v___jp_2794_;
}
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_io_get_num_heartbeats();
v___x_2826_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
if (lean_obj_tag(v_a_2827_) == 1)
{
if (v___x_2745_ == 0)
{
lean_object* v_val_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_val_2828_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_val_2828_);
lean_dec_ref_known(v_a_2827_, 1);
v___x_2829_ = lean_box(0);
v___x_2830_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2686_, v_val_2828_, v_name_2693_, v_levelParams_2687_, v___x_2829_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
v___y_2769_ = v_a_2807_;
v___y_2770_ = v___x_2825_;
v___y_2771_ = v___x_2830_;
goto v___jp_2768_;
}
else
{
lean_object* v_val_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_val_2831_ = lean_ctor_get(v_a_2827_, 0);
lean_inc_n(v_val_2831_, 2);
lean_dec_ref_known(v_a_2827_, 1);
v___x_2832_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2833_ = l_Lean_MessageData_ofExpr(v_val_2831_);
v___x_2834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2832_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2742_, v___x_2834_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v___x_2837_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2686_, v_val_2831_, v_name_2693_, v_levelParams_2687_, v_a_2836_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
v___y_2769_ = v_a_2807_;
v___y_2770_ = v___x_2825_;
v___y_2771_ = v___x_2837_;
goto v___jp_2768_;
}
else
{
lean_dec(v_val_2831_);
lean_dec(v_name_2693_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v___y_2769_ = v_a_2807_;
v___y_2770_ = v___x_2825_;
v___y_2771_ = v___x_2835_;
goto v___jp_2768_;
}
}
}
else
{
lean_object* v___x_2838_; 
lean_dec(v_a_2827_);
lean_dec(v_name_2693_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v___x_2838_ = lean_box(0);
v___y_2764_ = v_a_2807_;
v___y_2765_ = v___x_2825_;
v_a_2766_ = v___x_2838_;
goto v___jp_2763_;
}
}
else
{
lean_object* v_a_2839_; 
lean_dec(v_name_2693_);
lean_dec(v_levelParams_2687_);
lean_dec(v_name_2686_);
v_a_2839_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2826_, 1);
v___y_2759_ = v_a_2807_;
v___y_2760_ = v___x_2825_;
v_a_2761_ = v_a_2839_;
goto v___jp_2758_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_00_u03b1_2907_, lean_object* v_x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2908_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2915_, lean_object* v_x_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_00_u03b1_2915_, v_x_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2926_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2928_ = l_Lean_Name_append(v_ctorName_2926_, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
uint8_t v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = 1;
v___x_2936_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2929_, v___x_2935_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2944_, lean_object* v_t_2945_, lean_object* v_acc_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2945_, v_a_2947_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2954_ = l_Lean_Expr_cleanupAnnotations(v_a_2953_);
v___x_2955_ = l_Lean_Expr_isApp(v___x_2954_);
if (v___x_2955_ == 0)
{
lean_dec_ref(v___x_2954_);
goto v___jp_2949_;
}
else
{
lean_object* v_arg_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v_arg_2956_ = lean_ctor_get(v___x_2954_, 1);
lean_inc_ref(v_arg_2956_);
v___x_2957_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2954_);
v___x_2958_ = l_Lean_Expr_isApp(v___x_2957_);
if (v___x_2958_ == 0)
{
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_arg_2956_);
goto v___jp_2949_;
}
else
{
lean_object* v_arg_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v_arg_2959_ = lean_ctor_get(v___x_2957_, 1);
lean_inc_ref(v_arg_2959_);
v___x_2960_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2957_);
v___x_2961_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_2962_ = l_Lean_Expr_isConstOf(v___x_2960_, v___x_2961_);
lean_dec_ref(v___x_2960_);
if (v___x_2962_ == 0)
{
lean_dec_ref(v_arg_2959_);
lean_dec_ref(v_arg_2956_);
goto v___jp_2949_;
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_unsigned_to_nat(0u);
v___x_2964_ = l_Lean_mkProj(v___x_2961_, v___x_2963_, v_e_2944_);
lean_inc_ref(v___x_2964_);
v___x_2965_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2964_, v_arg_2959_, v_acc_2946_, v_a_2947_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v_e_2944_ = v___x_2964_;
v_t_2945_ = v_arg_2956_;
v_acc_2946_ = v_a_2966_;
goto _start;
}
else
{
lean_dec_ref(v___x_2964_);
lean_dec_ref(v_arg_2956_);
return v___x_2965_;
}
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec_ref(v_acc_2946_);
lean_dec_ref(v_e_2944_);
v_a_2968_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2952_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2952_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
v___jp_2949_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_array_push(v_acc_2946_, v_e_2944_);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_2976_, lean_object* v_t_2977_, lean_object* v_acc_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2976_, v_t_2977_, v_acc_2978_, v_a_2979_);
lean_dec(v_a_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_2982_, lean_object* v_t_2983_, lean_object* v_acc_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2982_, v_t_2983_, v_acc_2984_, v_a_2986_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_2991_, lean_object* v_t_2992_, lean_object* v_acc_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_2991_, v_t_2992_, v_acc_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v___x_3006_; 
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
lean_inc_ref(v_e_3000_);
v___x_3006_ = lean_infer_type(v_e_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3009_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3000_, v_a_3007_, v___x_3008_, v_a_3002_);
return v___x_3009_;
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref(v_e_3000_);
v_a_3010_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3006_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3006_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3025_, lean_object* v_x_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_){
_start:
{
lean_object* v_ks_3029_; lean_object* v_vs_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3054_; 
v_ks_3029_ = lean_ctor_get(v_x_3025_, 0);
v_vs_3030_ = lean_ctor_get(v_x_3025_, 1);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_x_3025_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3032_ = v_x_3025_;
v_isShared_3033_ = v_isSharedCheck_3054_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_vs_3030_);
lean_inc(v_ks_3029_);
lean_dec(v_x_3025_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3054_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; uint8_t v___x_3035_; 
v___x_3034_ = lean_array_get_size(v_ks_3029_);
v___x_3035_ = lean_nat_dec_lt(v_x_3026_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec(v_x_3026_);
v___x_3036_ = lean_array_push(v_ks_3029_, v_x_3027_);
v___x_3037_ = lean_array_push(v_vs_3030_, v_x_3028_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v___x_3037_);
lean_ctor_set(v___x_3032_, 0, v___x_3036_);
v___x_3039_ = v___x_3032_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v___x_3037_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
else
{
lean_object* v_k_x27_3041_; uint8_t v___x_3042_; 
v_k_x27_3041_ = lean_array_fget_borrowed(v_ks_3029_, v_x_3026_);
v___x_3042_ = l_Lean_instBEqMVarId_beq(v_x_3027_, v_k_x27_3041_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3044_; 
if (v_isShared_3033_ == 0)
{
v___x_3044_ = v___x_3032_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_ks_3029_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_vs_3030_);
v___x_3044_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = lean_unsigned_to_nat(1u);
v___x_3046_ = lean_nat_add(v_x_3026_, v___x_3045_);
lean_dec(v_x_3026_);
v_x_3025_ = v___x_3044_;
v_x_3026_ = v___x_3046_;
goto _start;
}
}
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3049_ = lean_array_fset(v_ks_3029_, v_x_3026_, v_x_3027_);
v___x_3050_ = lean_array_fset(v_vs_3030_, v_x_3026_, v_x_3028_);
lean_dec(v_x_3026_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v___x_3050_);
lean_ctor_set(v___x_3032_, 0, v___x_3049_);
v___x_3052_ = v___x_3032_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3055_, lean_object* v_k_3056_, lean_object* v_v_3057_){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_unsigned_to_nat(0u);
v___x_3059_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3055_, v___x_3058_, v_k_3056_, v_v_3057_);
return v___x_3059_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3061_, size_t v_x_3062_, size_t v_x_3063_, lean_object* v_x_3064_, lean_object* v_x_3065_){
_start:
{
if (lean_obj_tag(v_x_3061_) == 0)
{
lean_object* v_es_3066_; size_t v___x_3067_; size_t v___x_3068_; lean_object* v_j_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v_es_3066_ = lean_ctor_get(v_x_3061_, 0);
v___x_3067_ = ((size_t)31ULL);
v___x_3068_ = lean_usize_land(v_x_3062_, v___x_3067_);
v_j_3069_ = lean_usize_to_nat(v___x_3068_);
v___x_3070_ = lean_array_get_size(v_es_3066_);
v___x_3071_ = lean_nat_dec_lt(v_j_3069_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_dec(v_j_3069_);
lean_dec(v_x_3065_);
lean_dec(v_x_3064_);
return v_x_3061_;
}
else
{
lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3110_; 
lean_inc_ref(v_es_3066_);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_x_3061_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; 
v_unused_3111_ = lean_ctor_get(v_x_3061_, 0);
lean_dec(v_unused_3111_);
v___x_3073_ = v_x_3061_;
v_isShared_3074_ = v_isSharedCheck_3110_;
goto v_resetjp_3072_;
}
else
{
lean_dec(v_x_3061_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3110_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v_v_3075_; lean_object* v___x_3076_; lean_object* v_xs_x27_3077_; lean_object* v___y_3079_; 
v_v_3075_ = lean_array_fget(v_es_3066_, v_j_3069_);
v___x_3076_ = lean_box(0);
v_xs_x27_3077_ = lean_array_fset(v_es_3066_, v_j_3069_, v___x_3076_);
switch(lean_obj_tag(v_v_3075_))
{
case 0:
{
lean_object* v_key_3084_; lean_object* v_val_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3095_; 
v_key_3084_ = lean_ctor_get(v_v_3075_, 0);
v_val_3085_ = lean_ctor_get(v_v_3075_, 1);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_v_3075_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3087_ = v_v_3075_;
v_isShared_3088_ = v_isSharedCheck_3095_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_val_3085_);
lean_inc(v_key_3084_);
lean_dec(v_v_3075_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3095_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
uint8_t v___x_3089_; 
v___x_3089_ = l_Lean_instBEqMVarId_beq(v_x_3064_, v_key_3084_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_del_object(v___x_3087_);
v___x_3090_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3084_, v_val_3085_, v_x_3064_, v_x_3065_);
v___x_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
v___y_3079_ = v___x_3091_;
goto v___jp_3078_;
}
else
{
lean_object* v___x_3093_; 
lean_dec(v_val_3085_);
lean_dec(v_key_3084_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 1, v_x_3065_);
lean_ctor_set(v___x_3087_, 0, v_x_3064_);
v___x_3093_ = v___x_3087_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_x_3064_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_x_3065_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
v___y_3079_ = v___x_3093_;
goto v___jp_3078_;
}
}
}
}
case 1:
{
lean_object* v_node_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3108_; 
v_node_3096_ = lean_ctor_get(v_v_3075_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_v_3075_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3098_ = v_v_3075_;
v_isShared_3099_ = v_isSharedCheck_3108_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_node_3096_);
lean_dec(v_v_3075_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3108_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
size_t v___x_3100_; size_t v___x_3101_; size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3100_ = ((size_t)5ULL);
v___x_3101_ = lean_usize_shift_right(v_x_3062_, v___x_3100_);
v___x_3102_ = ((size_t)1ULL);
v___x_3103_ = lean_usize_add(v_x_3063_, v___x_3102_);
v___x_3104_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3096_, v___x_3101_, v___x_3103_, v_x_3064_, v_x_3065_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3104_);
v___x_3106_ = v___x_3098_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
v___y_3079_ = v___x_3106_;
goto v___jp_3078_;
}
}
}
default: 
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v_x_3064_);
lean_ctor_set(v___x_3109_, 1, v_x_3065_);
v___y_3079_ = v___x_3109_;
goto v___jp_3078_;
}
}
v___jp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = lean_array_fset(v_xs_x27_3077_, v_j_3069_, v___y_3079_);
lean_dec(v_j_3069_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3080_);
v___x_3082_ = v___x_3073_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
else
{
lean_object* v_ks_3112_; lean_object* v_vs_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3131_; 
v_ks_3112_ = lean_ctor_get(v_x_3061_, 0);
v_vs_3113_ = lean_ctor_get(v_x_3061_, 1);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_x_3061_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3115_ = v_x_3061_;
v_isShared_3116_ = v_isSharedCheck_3131_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_vs_3113_);
lean_inc(v_ks_3112_);
lean_dec(v_x_3061_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3131_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_ks_3112_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_vs_3113_);
v___x_3118_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v_newNode_3119_; size_t v___x_3120_; uint8_t v___x_3121_; 
v_newNode_3119_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3118_, v_x_3064_, v_x_3065_);
v___x_3120_ = ((size_t)7ULL);
v___x_3121_ = lean_usize_dec_le(v___x_3120_, v_x_3063_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v___x_3122_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3119_);
v___x_3123_ = lean_unsigned_to_nat(4u);
v___x_3124_ = lean_nat_dec_lt(v___x_3122_, v___x_3123_);
lean_dec(v___x_3122_);
if (v___x_3124_ == 0)
{
lean_object* v_ks_3125_; lean_object* v_vs_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v_ks_3125_ = lean_ctor_get(v_newNode_3119_, 0);
lean_inc_ref(v_ks_3125_);
v_vs_3126_ = lean_ctor_get(v_newNode_3119_, 1);
lean_inc_ref(v_vs_3126_);
lean_dec_ref(v_newNode_3119_);
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3129_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3063_, v_ks_3125_, v_vs_3126_, v___x_3127_, v___x_3128_);
lean_dec_ref(v_vs_3126_);
lean_dec_ref(v_ks_3125_);
return v___x_3129_;
}
else
{
return v_newNode_3119_;
}
}
else
{
return v_newNode_3119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3132_, lean_object* v_keys_3133_, lean_object* v_vals_3134_, lean_object* v_i_3135_, lean_object* v_entries_3136_){
_start:
{
lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3137_ = lean_array_get_size(v_keys_3133_);
v___x_3138_ = lean_nat_dec_lt(v_i_3135_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_dec(v_i_3135_);
return v_entries_3136_;
}
else
{
lean_object* v_k_3139_; lean_object* v_v_3140_; uint64_t v___x_3141_; size_t v_h_3142_; size_t v___x_3143_; lean_object* v___x_3144_; size_t v___x_3145_; size_t v___x_3146_; size_t v___x_3147_; size_t v_h_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v_k_3139_ = lean_array_fget_borrowed(v_keys_3133_, v_i_3135_);
v_v_3140_ = lean_array_fget_borrowed(v_vals_3134_, v_i_3135_);
v___x_3141_ = l_Lean_instHashableMVarId_hash(v_k_3139_);
v_h_3142_ = lean_uint64_to_usize(v___x_3141_);
v___x_3143_ = ((size_t)5ULL);
v___x_3144_ = lean_unsigned_to_nat(1u);
v___x_3145_ = ((size_t)1ULL);
v___x_3146_ = lean_usize_sub(v_depth_3132_, v___x_3145_);
v___x_3147_ = lean_usize_mul(v___x_3143_, v___x_3146_);
v_h_3148_ = lean_usize_shift_right(v_h_3142_, v___x_3147_);
v___x_3149_ = lean_nat_add(v_i_3135_, v___x_3144_);
lean_dec(v_i_3135_);
lean_inc(v_v_3140_);
lean_inc(v_k_3139_);
v___x_3150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3136_, v_h_3148_, v_depth_3132_, v_k_3139_, v_v_3140_);
v_i_3135_ = v___x_3149_;
v_entries_3136_ = v___x_3150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3152_, lean_object* v_keys_3153_, lean_object* v_vals_3154_, lean_object* v_i_3155_, lean_object* v_entries_3156_){
_start:
{
size_t v_depth_boxed_3157_; lean_object* v_res_3158_; 
v_depth_boxed_3157_ = lean_unbox_usize(v_depth_3152_);
lean_dec(v_depth_3152_);
v_res_3158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3157_, v_keys_3153_, v_vals_3154_, v_i_3155_, v_entries_3156_);
lean_dec_ref(v_vals_3154_);
lean_dec_ref(v_keys_3153_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3159_, lean_object* v_x_3160_, lean_object* v_x_3161_, lean_object* v_x_3162_, lean_object* v_x_3163_){
_start:
{
size_t v_x_4996__boxed_3164_; size_t v_x_4997__boxed_3165_; lean_object* v_res_3166_; 
v_x_4996__boxed_3164_ = lean_unbox_usize(v_x_3160_);
lean_dec(v_x_3160_);
v_x_4997__boxed_3165_ = lean_unbox_usize(v_x_3161_);
lean_dec(v_x_3161_);
v_res_3166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3159_, v_x_4996__boxed_3164_, v_x_4997__boxed_3165_, v_x_3162_, v_x_3163_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3167_, lean_object* v_x_3168_, lean_object* v_x_3169_){
_start:
{
uint64_t v___x_3170_; size_t v___x_3171_; size_t v___x_3172_; lean_object* v___x_3173_; 
v___x_3170_ = l_Lean_instHashableMVarId_hash(v_x_3168_);
v___x_3171_ = lean_uint64_to_usize(v___x_3170_);
v___x_3172_ = ((size_t)1ULL);
v___x_3173_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3167_, v___x_3171_, v___x_3172_, v_x_3168_, v_x_3169_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3174_, lean_object* v_val_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; lean_object* v_mctx_3179_; lean_object* v_cache_3180_; lean_object* v_zetaDeltaFVarIds_3181_; lean_object* v_postponed_3182_; lean_object* v_diag_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3213_; 
v___x_3178_ = lean_st_ref_take(v___y_3176_);
v_mctx_3179_ = lean_ctor_get(v___x_3178_, 0);
v_cache_3180_ = lean_ctor_get(v___x_3178_, 1);
v_zetaDeltaFVarIds_3181_ = lean_ctor_get(v___x_3178_, 2);
v_postponed_3182_ = lean_ctor_get(v___x_3178_, 3);
v_diag_3183_ = lean_ctor_get(v___x_3178_, 4);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3185_ = v___x_3178_;
v_isShared_3186_ = v_isSharedCheck_3213_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_diag_3183_);
lean_inc(v_postponed_3182_);
lean_inc(v_zetaDeltaFVarIds_3181_);
lean_inc(v_cache_3180_);
lean_inc(v_mctx_3179_);
lean_dec(v___x_3178_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3213_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_depth_3187_; lean_object* v_levelAssignDepth_3188_; lean_object* v_lmvarCounter_3189_; lean_object* v_mvarCounter_3190_; lean_object* v_lDecls_3191_; lean_object* v_decls_3192_; lean_object* v_userNames_3193_; lean_object* v_lAssignment_3194_; lean_object* v_eAssignment_3195_; lean_object* v_dAssignment_3196_; lean_object* v_instanceTypedMVars_3197_; lean_object* v_synthNormMemo_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3212_; 
v_depth_3187_ = lean_ctor_get(v_mctx_3179_, 0);
v_levelAssignDepth_3188_ = lean_ctor_get(v_mctx_3179_, 1);
v_lmvarCounter_3189_ = lean_ctor_get(v_mctx_3179_, 2);
v_mvarCounter_3190_ = lean_ctor_get(v_mctx_3179_, 3);
v_lDecls_3191_ = lean_ctor_get(v_mctx_3179_, 4);
v_decls_3192_ = lean_ctor_get(v_mctx_3179_, 5);
v_userNames_3193_ = lean_ctor_get(v_mctx_3179_, 6);
v_lAssignment_3194_ = lean_ctor_get(v_mctx_3179_, 7);
v_eAssignment_3195_ = lean_ctor_get(v_mctx_3179_, 8);
v_dAssignment_3196_ = lean_ctor_get(v_mctx_3179_, 9);
v_instanceTypedMVars_3197_ = lean_ctor_get(v_mctx_3179_, 10);
v_synthNormMemo_3198_ = lean_ctor_get(v_mctx_3179_, 11);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_mctx_3179_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3200_ = v_mctx_3179_;
v_isShared_3201_ = v_isSharedCheck_3212_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_synthNormMemo_3198_);
lean_inc(v_instanceTypedMVars_3197_);
lean_inc(v_dAssignment_3196_);
lean_inc(v_eAssignment_3195_);
lean_inc(v_lAssignment_3194_);
lean_inc(v_userNames_3193_);
lean_inc(v_decls_3192_);
lean_inc(v_lDecls_3191_);
lean_inc(v_mvarCounter_3190_);
lean_inc(v_lmvarCounter_3189_);
lean_inc(v_levelAssignDepth_3188_);
lean_inc(v_depth_3187_);
lean_dec(v_mctx_3179_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3212_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3202_ = lean_box(0);
v___x_3203_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3195_, v_mvarId_3174_, v_val_3175_);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 8, v___x_3203_);
v___x_3205_ = v___x_3200_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_depth_3187_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_levelAssignDepth_3188_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_lmvarCounter_3189_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v_mvarCounter_3190_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v_lDecls_3191_);
lean_ctor_set(v_reuseFailAlloc_3211_, 5, v_decls_3192_);
lean_ctor_set(v_reuseFailAlloc_3211_, 6, v_userNames_3193_);
lean_ctor_set(v_reuseFailAlloc_3211_, 7, v_lAssignment_3194_);
lean_ctor_set(v_reuseFailAlloc_3211_, 8, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3211_, 9, v_dAssignment_3196_);
lean_ctor_set(v_reuseFailAlloc_3211_, 10, v_instanceTypedMVars_3197_);
lean_ctor_set(v_reuseFailAlloc_3211_, 11, v_synthNormMemo_3198_);
v___x_3205_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 0, v___x_3205_);
v___x_3207_ = v___x_3185_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_cache_3180_);
lean_ctor_set(v_reuseFailAlloc_3210_, 2, v_zetaDeltaFVarIds_3181_);
lean_ctor_set(v_reuseFailAlloc_3210_, 3, v_postponed_3182_);
lean_ctor_set(v_reuseFailAlloc_3210_, 4, v_diag_3183_);
v___x_3207_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_st_ref_put(v___y_3176_, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3202_);
return v___x_3209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3214_, lean_object* v_val_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3214_, v_val_3215_, v___y_3216_);
lean_dec(v___y_3216_);
return v_res_3218_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0));
v___x_3221_ = l_Lean_stringToMessageData(v___x_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3222_, lean_object* v_a_3223_, lean_object* v_x_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1);
v___x_3231_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3230_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
lean_inc(v___y_3228_);
lean_inc_ref(v___y_3227_);
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3225_);
v___x_3233_ = lean_apply_7(v___f_3222_, v_a_3232_, v_a_3223_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, lean_box(0));
return v___x_3233_;
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_a_3223_);
lean_dec_ref(v___f_3222_);
v_a_3234_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3231_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3231_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3242_, lean_object* v_a_3243_, lean_object* v_x_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3242_, v_a_3243_, v_x_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v_x_3244_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3251_, lean_object* v_a_3252_, lean_object* v_x_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = lean_box(0);
lean_inc(v___y_3257_);
lean_inc_ref(v___y_3256_);
lean_inc(v___y_3255_);
lean_inc_ref(v___y_3254_);
v___x_3260_ = lean_apply_7(v___f_3251_, v___x_3259_, v_a_3252_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, lean_box(0));
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3261_, lean_object* v_a_3262_, lean_object* v_x_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3261_, v_a_3262_, v_x_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3270_, lean_object* v_____r_3271_, lean_object* v_mvarId_u2082_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3272_, v___x_3270_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3288_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3288_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3288_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v_snd_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v_snd_3283_ = lean_ctor_get(v_a_3279_, 1);
lean_inc(v_snd_3283_);
lean_dec(v_a_3279_);
v___x_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3284_, 0, v_snd_3283_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v___x_3284_);
v___x_3286_ = v___x_3281_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
v_a_3289_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3278_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3278_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3297_, lean_object* v_____r_3298_, lean_object* v_mvarId_u2082_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
uint8_t v___x_5284__boxed_3305_; lean_object* v_res_3306_; 
v___x_5284__boxed_3305_ = lean_unbox(v___x_3297_);
v_res_3306_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5284__boxed_3305_, v_____r_3298_, v_mvarId_u2082_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
return v_res_3306_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3315_ = lean_box(0);
v___x_3316_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3));
v___x_3317_ = l_Lean_mkConst(v___x_3316_, v___x_3315_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___y_3325_; uint8_t v___x_3345_; lean_object* v___f_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3345_ = 0;
v___f_3346_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0));
v___x_3347_ = 1;
lean_inc(v_a_3318_);
v___x_3348_ = l_Lean_MVarId_getType(v_a_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3406_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3351_ = v___x_3348_;
v_isShared_3352_ = v_isSharedCheck_3406_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3406_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
if (lean_obj_tag(v_a_3349_) == 7)
{
lean_object* v_binderType_3353_; lean_object* v_body_3354_; uint8_t v___x_3355_; 
v_binderType_3353_ = lean_ctor_get(v_a_3349_, 1);
lean_inc_ref(v_binderType_3353_);
v_body_3354_ = lean_ctor_get(v_a_3349_, 2);
lean_inc_ref(v_body_3354_);
lean_dec_ref_known(v_a_3349_, 3);
v___x_3355_ = l_Lean_Expr_hasLooseBVars(v_body_3354_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
lean_del_object(v___x_3351_);
v___x_3356_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3353_, v___y_3320_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v___x_3358_ = l_Lean_Expr_cleanupAnnotations(v_a_3357_);
v___x_3359_ = l_Lean_Expr_isApp(v___x_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_dec_ref(v___x_3358_);
lean_dec_ref(v_body_3354_);
v___x_3360_ = lean_box(0);
v___x_3361_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3346_, v_a_3318_, v___x_3360_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
v___y_3325_ = v___x_3361_;
goto v___jp_3324_;
}
else
{
lean_object* v_arg_3362_; lean_object* v___x_3363_; uint8_t v___x_3364_; 
v_arg_3362_ = lean_ctor_get(v___x_3358_, 1);
lean_inc_ref(v_arg_3362_);
v___x_3363_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3358_);
v___x_3364_ = l_Lean_Expr_isApp(v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec_ref(v___x_3363_);
lean_dec_ref(v_arg_3362_);
lean_dec_ref(v_body_3354_);
v___x_3365_ = lean_box(0);
v___x_3366_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3346_, v_a_3318_, v___x_3365_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
v___y_3325_ = v___x_3366_;
goto v___jp_3324_;
}
else
{
lean_object* v_arg_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v_arg_3367_ = lean_ctor_get(v___x_3363_, 1);
lean_inc_ref(v_arg_3367_);
v___x_3368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3363_);
v___x_3369_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3370_ = l_Lean_Expr_isConstOf(v___x_3368_, v___x_3369_);
lean_dec_ref(v___x_3368_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec_ref(v_arg_3367_);
lean_dec_ref(v_arg_3362_);
lean_dec_ref(v_body_3354_);
v___x_3371_ = lean_box(0);
v___x_3372_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3346_, v_a_3318_, v___x_3371_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
v___y_3325_ = v___x_3372_;
goto v___jp_3324_;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3373_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4);
v___x_3374_ = l_Lean_mkApp3(v___x_3373_, v_arg_3367_, v_arg_3362_, v_body_3354_);
v___x_3375_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3318_);
v___x_3376_ = l_Lean_MVarId_applyN(v_a_3318_, v___x_3374_, v___x_3375_, v___x_3347_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
if (lean_obj_tag(v_a_3377_) == 1)
{
lean_object* v_tail_3378_; 
v_tail_3378_ = lean_ctor_get(v_a_3377_, 1);
if (lean_obj_tag(v_tail_3378_) == 0)
{
lean_object* v_head_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec(v_a_3318_);
v_head_3379_ = lean_ctor_get(v_a_3377_, 0);
lean_inc(v_head_3379_);
lean_dec_ref_known(v_a_3377_, 2);
v___x_3380_ = lean_box(0);
v___x_3381_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3345_, v___x_3380_, v_head_3379_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
v___y_3325_ = v___x_3381_;
goto v___jp_3324_;
}
else
{
lean_object* v___x_3382_; 
v___x_3382_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3346_, v_a_3318_, v_a_3377_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec_ref_known(v_a_3377_, 2);
v___y_3325_ = v___x_3382_;
goto v___jp_3324_;
}
}
else
{
lean_object* v___x_3383_; 
v___x_3383_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3346_, v_a_3318_, v_a_3377_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v_a_3377_);
v___y_3325_ = v___x_3383_;
goto v___jp_3324_;
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec(v_a_3318_);
v_a_3384_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3376_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3376_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec_ref(v_body_3354_);
lean_dec(v_a_3318_);
v_a_3392_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3356_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3356_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
else
{
lean_object* v___x_3401_; 
lean_dec_ref(v_body_3354_);
lean_dec_ref(v_binderType_3353_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v_a_3318_);
v___x_3401_ = v___x_3351_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3318_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_object* v___x_3404_; 
lean_dec(v_a_3349_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v_a_3318_);
v___x_3404_ = v___x_3351_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3318_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec(v_a_3318_);
v_a_3407_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3348_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3348_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
v___jp_3324_:
{
if (lean_obj_tag(v___y_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3336_; 
v_a_3326_ = lean_ctor_get(v___y_3325_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___y_3325_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3328_ = v___y_3325_;
v_isShared_3329_ = v_isSharedCheck_3336_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___y_3325_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3336_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
if (lean_obj_tag(v_a_3326_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3332_; 
v_a_3330_ = lean_ctor_get(v_a_3326_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v_a_3326_, 1);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v_a_3330_);
v___x_3332_ = v___x_3328_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
else
{
lean_object* v_a_3334_; 
lean_del_object(v___x_3328_);
v_a_3334_ = lean_ctor_get(v_a_3326_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v_a_3326_, 1);
v_a_3318_ = v_a_3334_;
goto _start;
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
v_a_3337_ = lean_ctor_get(v___y_3325_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___y_3325_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___y_3325_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___y_3325_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
return v_res_3421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0));
v___x_3424_ = l_Lean_stringToMessageData(v___x_3423_);
return v___x_3424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3430_ = lean_box(0);
v___x_3431_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3432_ = l_Lean_mkConst(v___x_3431_, v___x_3430_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3437_, lean_object* v_xs_3438_, lean_object* v_type_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = lean_box(0);
v___x_3455_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3439_, v___x_3454_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; uint8_t v___x_3460_; uint8_t v___x_3461_; lean_object* v___y_3463_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v___x_3457_ = l_Lean_Expr_mvarId_x21(v_a_3456_);
v___x_3458_ = lean_box(0);
v___x_3459_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5);
v___x_3460_ = 1;
v___x_3461_ = 0;
v___x_3474_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6));
v___x_3475_ = lean_box(0);
v___x_3476_ = l_Lean_MVarId_apply(v___x_3457_, v___x_3459_, v___x_3474_, v___x_3475_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3476_, 1);
if (lean_obj_tag(v_a_3477_) == 1)
{
lean_object* v_tail_3478_; 
v_tail_3478_ = lean_ctor_get(v_a_3477_, 1);
lean_inc(v_tail_3478_);
if (lean_obj_tag(v_tail_3478_) == 1)
{
lean_object* v_tail_3479_; 
v_tail_3479_ = lean_ctor_get(v_tail_3478_, 1);
if (lean_obj_tag(v_tail_3479_) == 0)
{
lean_object* v_toConstantVal_3480_; lean_object* v_head_3481_; lean_object* v_head_3482_; lean_object* v_name_3483_; lean_object* v_levelParams_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v_toConstantVal_3480_ = lean_ctor_get(v_ctorVal_3437_, 0);
lean_inc_ref(v_toConstantVal_3480_);
lean_dec_ref(v_ctorVal_3437_);
v_head_3481_ = lean_ctor_get(v_a_3477_, 0);
lean_inc(v_head_3481_);
lean_dec_ref_known(v_a_3477_, 2);
v_head_3482_ = lean_ctor_get(v_tail_3478_, 0);
lean_inc(v_head_3482_);
lean_dec_ref_known(v_tail_3478_, 2);
v_name_3483_ = lean_ctor_get(v_toConstantVal_3480_, 0);
lean_inc_n(v_name_3483_, 2);
v_levelParams_3484_ = lean_ctor_get(v_toConstantVal_3480_, 1);
lean_inc(v_levelParams_3484_);
lean_dec_ref(v_toConstantVal_3480_);
v___x_3485_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3483_);
v___x_3486_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3484_, v___x_3458_);
v___x_3487_ = l_Lean_mkConst(v___x_3485_, v___x_3486_);
v___x_3488_ = l_Lean_mkAppN(v___x_3487_, v_xs_3438_);
v___x_3489_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3481_, v___x_3488_, v___y_3441_);
lean_dec_ref(v___x_3489_);
v___x_3490_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3482_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3492_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v___x_3492_ = l_Lean_MVarId_refl(v_a_3491_, v___x_3460_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_dec(v_name_3483_);
v___y_3463_ = v___x_3492_;
goto v___jp_3462_;
}
else
{
lean_object* v_a_3493_; uint8_t v___y_3495_; uint8_t v___x_3498_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v___x_3498_ = l_Lean_Exception_isInterrupt(v_a_3493_);
if (v___x_3498_ == 0)
{
uint8_t v___x_3499_; 
lean_inc(v_a_3493_);
v___x_3499_ = l_Lean_Exception_isRuntime(v_a_3493_);
v___y_3495_ = v___x_3499_;
goto v___jp_3494_;
}
else
{
v___y_3495_ = v___x_3498_;
goto v___jp_3494_;
}
v___jp_3494_:
{
if (v___y_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
lean_dec_ref_known(v___x_3492_, 1);
v___x_3496_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3483_);
v___x_3497_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3496_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
v___y_3463_ = v___x_3497_;
goto v___jp_3462_;
}
else
{
lean_dec(v_name_3483_);
v___y_3463_ = v___x_3492_;
goto v___jp_3462_;
}
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec(v_name_3483_);
lean_dec(v_a_3456_);
v_a_3500_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3490_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3490_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3478_, 2);
lean_dec_ref_known(v_a_3477_, 2);
lean_dec(v_a_3456_);
goto v___jp_3445_;
}
}
else
{
lean_dec_ref_known(v_a_3477_, 2);
lean_dec(v_tail_3478_);
lean_dec(v_a_3456_);
goto v___jp_3445_;
}
}
else
{
lean_dec(v_a_3477_);
lean_dec(v_a_3456_);
goto v___jp_3445_;
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec(v_a_3456_);
lean_dec_ref(v_ctorVal_3437_);
v_a_3508_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3476_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3476_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
v___jp_3462_:
{
if (lean_obj_tag(v___y_3463_) == 0)
{
uint8_t v___x_3464_; lean_object* v___x_3465_; 
lean_dec_ref_known(v___y_3463_, 1);
v___x_3464_ = 1;
v___x_3465_ = l_Lean_Meta_mkLambdaFVars(v_xs_3438_, v_a_3456_, v___x_3461_, v___x_3460_, v___x_3461_, v___x_3460_, v___x_3464_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
return v___x_3465_;
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_dec(v_a_3456_);
v_a_3466_ = lean_ctor_get(v___y_3463_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___y_3463_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___y_3463_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___y_3463_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorVal_3437_);
return v___x_3455_;
}
v___jp_3445_:
{
lean_object* v_toConstantVal_3446_; lean_object* v_name_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v_toConstantVal_3446_ = lean_ctor_get(v_ctorVal_3437_, 0);
lean_inc_ref(v_toConstantVal_3446_);
lean_dec_ref(v_ctorVal_3437_);
v_name_3447_ = lean_ctor_get(v_toConstantVal_3446_, 0);
lean_inc(v_name_3447_);
lean_dec_ref(v_toConstantVal_3446_);
v___x_3448_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1);
v___x_3449_ = l_Lean_MessageData_ofName(v_name_3447_);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3452_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
return v___x_3453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3516_, lean_object* v_xs_3517_, lean_object* v_type_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3516_, v_xs_3517_, v_type_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v_xs_3517_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3525_, lean_object* v_targetType_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_){
_start:
{
lean_object* v___f_3532_; uint8_t v___x_3533_; lean_object* v___x_3534_; 
v___f_3532_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3532_, 0, v_ctorVal_3525_);
v___x_3533_ = 0;
v___x_3534_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3526_, v___f_3532_, v___x_3533_, v___x_3533_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3535_, lean_object* v_targetType_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3535_, v_targetType_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3543_, lean_object* v_val_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3543_, v_val_3544_, v___y_3546_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3551_, lean_object* v_val_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3551_, v_val_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3559_, lean_object* v_a_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3567_, lean_object* v_a_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3567_, v_a_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3575_, lean_object* v_x_3576_, lean_object* v_x_3577_, lean_object* v_x_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3576_, v_x_3577_, v_x_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3580_, lean_object* v_x_3581_, size_t v_x_3582_, size_t v_x_3583_, lean_object* v_x_3584_, lean_object* v_x_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3581_, v_x_3582_, v_x_3583_, v_x_3584_, v_x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_){
_start:
{
size_t v_x_5837__boxed_3593_; size_t v_x_5838__boxed_3594_; lean_object* v_res_3595_; 
v_x_5837__boxed_3593_ = lean_unbox_usize(v_x_3589_);
lean_dec(v_x_3589_);
v_x_5838__boxed_3594_ = lean_unbox_usize(v_x_3590_);
lean_dec(v_x_3590_);
v_res_3595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3587_, v_x_3588_, v_x_5837__boxed_3593_, v_x_5838__boxed_3594_, v_x_3591_, v_x_3592_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3596_, lean_object* v_n_3597_, lean_object* v_k_3598_, lean_object* v_v_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3597_, v_k_3598_, v_v_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3601_, size_t v_depth_3602_, lean_object* v_keys_3603_, lean_object* v_vals_3604_, lean_object* v_heq_3605_, lean_object* v_i_3606_, lean_object* v_entries_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3602_, v_keys_3603_, v_vals_3604_, v_i_3606_, v_entries_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3609_, lean_object* v_depth_3610_, lean_object* v_keys_3611_, lean_object* v_vals_3612_, lean_object* v_heq_3613_, lean_object* v_i_3614_, lean_object* v_entries_3615_){
_start:
{
size_t v_depth_boxed_3616_; lean_object* v_res_3617_; 
v_depth_boxed_3616_ = lean_unbox_usize(v_depth_3610_);
lean_dec(v_depth_3610_);
v_res_3617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3609_, v_depth_boxed_3616_, v_keys_3611_, v_vals_3612_, v_heq_3613_, v_i_3614_, v_entries_3615_);
lean_dec_ref(v_vals_3612_);
lean_dec_ref(v_keys_3611_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_, lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3619_, v_x_3620_, v_x_3621_, v_x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3624_, lean_object* v_val_3625_, lean_object* v_name_3626_, lean_object* v_levelParams_3627_, uint8_t v___x_3628_, uint8_t v_hasTrace_3629_, lean_object* v_____r_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; 
lean_inc_ref(v_val_3625_);
v___x_3636_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3624_, v_val_3625_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v_a_3639_; lean_object* v___x_3640_; lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3657_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3625_, v___y_3632_);
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref(v___x_3638_);
v___x_3640_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3637_, v___y_3632_);
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3643_ = v___x_3640_;
v_isShared_3644_ = v_isSharedCheck_3657_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3640_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3657_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
lean_inc_n(v_name_3626_, 2);
v___x_3645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3645_, 0, v_name_3626_);
lean_ctor_set(v___x_3645_, 1, v_levelParams_3627_);
lean_ctor_set(v___x_3645_, 2, v_a_3639_);
v___x_3646_ = lean_box(0);
v___x_3647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3647_, 0, v_name_3626_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3645_);
lean_ctor_set(v___x_3648_, 1, v_a_3641_);
lean_ctor_set(v___x_3648_, 2, v___x_3647_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set_tag(v___x_3643_, 2);
lean_ctor_set(v___x_3643_, 0, v___x_3648_);
v___x_3650_ = v___x_3643_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_addDecl(v___x_3650_, v___x_3628_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v___x_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec_ref_known(v___x_3651_, 1);
v___x_3652_ = l_Lean_Meta_simpExtension;
v___x_3653_ = 0;
v___x_3654_ = lean_unsigned_to_nat(1000u);
v___x_3655_ = l_Lean_Meta_addSimpTheorem(v___x_3652_, v_name_3626_, v_hasTrace_3629_, v___x_3628_, v___x_3653_, v___x_3654_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
return v___x_3655_;
}
else
{
lean_dec(v_name_3626_);
return v___x_3651_;
}
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v_levelParams_3627_);
lean_dec(v_name_3626_);
lean_dec_ref(v_val_3625_);
v_a_3658_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3636_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3636_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3666_, lean_object* v_val_3667_, lean_object* v_name_3668_, lean_object* v_levelParams_3669_, lean_object* v___x_3670_, lean_object* v_hasTrace_3671_, lean_object* v_____r_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v___x_8728__boxed_3678_; uint8_t v_hasTrace_boxed_3679_; lean_object* v_res_3680_; 
v___x_8728__boxed_3678_ = lean_unbox(v___x_3670_);
v_hasTrace_boxed_3679_ = lean_unbox(v_hasTrace_3671_);
v_res_3680_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3666_, v_val_3667_, v_name_3668_, v_levelParams_3669_, v___x_8728__boxed_3678_, v_hasTrace_boxed_3679_, v_____r_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3681_, lean_object* v_val_3682_, lean_object* v_name_3683_, lean_object* v_levelParams_3684_, uint8_t v___x_3685_, lean_object* v_____r_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; 
lean_inc_ref(v_val_3682_);
v___x_3692_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3681_, v_val_3682_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3694_; lean_object* v_a_3695_; lean_object* v___x_3696_; lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3714_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
v___x_3694_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3682_, v___y_3688_);
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref(v___x_3694_);
v___x_3696_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3693_, v___y_3688_);
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3714_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3714_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3706_; 
lean_inc_n(v_name_3683_, 2);
v___x_3701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3701_, 0, v_name_3683_);
lean_ctor_set(v___x_3701_, 1, v_levelParams_3684_);
lean_ctor_set(v___x_3701_, 2, v_a_3695_);
v___x_3702_ = lean_box(0);
v___x_3703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3703_, 0, v_name_3683_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3701_);
lean_ctor_set(v___x_3704_, 1, v_a_3697_);
lean_ctor_set(v___x_3704_, 2, v___x_3703_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set_tag(v___x_3699_, 2);
lean_ctor_set(v___x_3699_, 0, v___x_3704_);
v___x_3706_ = v___x_3699_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
uint8_t v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = 0;
v___x_3708_ = l_Lean_addDecl(v___x_3706_, v___x_3707_, v___y_3689_, v___y_3690_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v___x_3709_; uint8_t v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_dec_ref_known(v___x_3708_, 1);
v___x_3709_ = l_Lean_Meta_simpExtension;
v___x_3710_ = 0;
v___x_3711_ = lean_unsigned_to_nat(1000u);
v___x_3712_ = l_Lean_Meta_addSimpTheorem(v___x_3709_, v_name_3683_, v___x_3685_, v___x_3707_, v___x_3710_, v___x_3711_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
return v___x_3712_;
}
else
{
lean_dec(v_name_3683_);
return v___x_3708_;
}
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v_levelParams_3684_);
lean_dec(v_name_3683_);
lean_dec_ref(v_val_3682_);
v_a_3715_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3692_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3692_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3723_, lean_object* v_val_3724_, lean_object* v_name_3725_, lean_object* v_levelParams_3726_, lean_object* v___x_3727_, lean_object* v_____r_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
uint8_t v___x_8816__boxed_3734_; lean_object* v_res_3735_; 
v___x_8816__boxed_3734_ = lean_unbox(v___x_3727_);
v_res_3735_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3723_, v_val_3724_, v_name_3725_, v_levelParams_3726_, v___x_8816__boxed_3734_, v_____r_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v_toConstantVal_3742_; lean_object* v_toCold_3743_; lean_object* v_options_3744_; lean_object* v_name_3745_; lean_object* v_levelParams_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3966_; 
v_toConstantVal_3742_ = lean_ctor_get(v_ctorVal_3736_, 0);
lean_inc_ref(v_toConstantVal_3742_);
v_toCold_3743_ = lean_ctor_get(v_a_3739_, 0);
v_options_3744_ = lean_ctor_get(v_toCold_3743_, 2);
v_name_3745_ = lean_ctor_get(v_toConstantVal_3742_, 0);
v_levelParams_3746_ = lean_ctor_get(v_toConstantVal_3742_, 1);
v_isSharedCheck_3966_ = !lean_is_exclusive(v_toConstantVal_3742_);
if (v_isSharedCheck_3966_ == 0)
{
lean_object* v_unused_3967_; 
v_unused_3967_ = lean_ctor_get(v_toConstantVal_3742_, 2);
lean_dec(v_unused_3967_);
v___x_3748_ = v_toConstantVal_3742_;
v_isShared_3749_ = v_isSharedCheck_3966_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_levelParams_3746_);
lean_inc(v_name_3745_);
lean_dec(v_toConstantVal_3742_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3966_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v_inheritedTraceOptions_3750_; uint8_t v_hasTrace_3751_; lean_object* v_name_3752_; 
v_inheritedTraceOptions_3750_ = lean_ctor_get(v_toCold_3743_, 11);
v_hasTrace_3751_ = lean_ctor_get_uint8(v_options_3744_, sizeof(void*)*1);
v_name_3752_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3745_);
if (v_hasTrace_3751_ == 0)
{
lean_object* v___x_3753_; 
lean_inc_ref(v_ctorVal_3736_);
v___x_3753_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3796_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3756_ = v___x_3753_;
v_isShared_3757_ = v_isSharedCheck_3796_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3753_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3796_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
if (lean_obj_tag(v_a_3754_) == 1)
{
lean_object* v_val_3758_; lean_object* v___x_3759_; 
lean_del_object(v___x_3756_);
v_val_3758_ = lean_ctor_get(v_a_3754_, 0);
lean_inc_n(v_val_3758_, 2);
lean_dec_ref_known(v_a_3754_, 1);
v___x_3759_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3736_, v_val_3758_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3761_; lean_object* v_a_3762_; lean_object* v___x_3763_; lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3783_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3758_, v_a_3738_);
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref(v___x_3761_);
v___x_3763_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3760_, v_a_3738_);
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3766_ = v___x_3763_;
v_isShared_3767_ = v_isSharedCheck_3783_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3763_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3783_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
lean_inc(v_name_3752_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 2, v_a_3762_);
lean_ctor_set(v___x_3748_, 0, v_name_3752_);
v___x_3769_ = v___x_3748_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_name_3752_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_levelParams_3746_);
lean_ctor_set(v_reuseFailAlloc_3782_, 2, v_a_3762_);
v___x_3769_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3774_; 
v___x_3770_ = lean_box(0);
lean_inc(v_name_3752_);
v___x_3771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3771_, 0, v_name_3752_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3769_);
lean_ctor_set(v___x_3772_, 1, v_a_3764_);
lean_ctor_set(v___x_3772_, 2, v___x_3771_);
if (v_isShared_3767_ == 0)
{
lean_ctor_set_tag(v___x_3766_, 2);
lean_ctor_set(v___x_3766_, 0, v___x_3772_);
v___x_3774_ = v___x_3766_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_addDecl(v___x_3774_, v_hasTrace_3751_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v___x_3776_; uint8_t v___x_3777_; uint8_t v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
lean_dec_ref_known(v___x_3775_, 1);
v___x_3776_ = l_Lean_Meta_simpExtension;
v___x_3777_ = 1;
v___x_3778_ = 0;
v___x_3779_ = lean_unsigned_to_nat(1000u);
v___x_3780_ = l_Lean_Meta_addSimpTheorem(v___x_3776_, v_name_3752_, v___x_3777_, v_hasTrace_3751_, v___x_3778_, v___x_3779_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
return v___x_3780_;
}
else
{
lean_dec(v_name_3752_);
return v___x_3775_;
}
}
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec(v_val_3758_);
lean_dec(v_name_3752_);
lean_del_object(v___x_3748_);
lean_dec(v_levelParams_3746_);
v_a_3784_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3759_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3759_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3794_; 
lean_dec(v_a_3754_);
lean_dec(v_name_3752_);
lean_del_object(v___x_3748_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v___x_3792_ = lean_box(0);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 0, v___x_3792_);
v___x_3794_ = v___x_3756_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_name_3752_);
lean_del_object(v___x_3748_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v_a_3797_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3753_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3753_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
else
{
lean_object* v___f_3805_; lean_object* v_cls_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v_a_3813_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v_a_3825_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v_a_3830_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v_a_3841_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v_a_3856_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v_a_3861_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; 
lean_inc(v_name_3752_);
v___f_3805_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3805_, 0, v_name_3752_);
v_cls_3806_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3807_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3808_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3809_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3750_, v_options_3744_, v___x_3808_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3904_; uint8_t v___x_3905_; 
v___x_3904_ = l_Lean_trace_profiler;
v___x_3905_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3744_, v___x_3904_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; 
lean_dec_ref(v___f_3805_);
lean_inc_ref(v_ctorVal_3736_);
v___x_3906_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3957_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3909_ = v___x_3906_;
v_isShared_3910_ = v_isSharedCheck_3957_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3906_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3957_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
if (lean_obj_tag(v_a_3907_) == 1)
{
lean_object* v_val_3911_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; 
lean_del_object(v___x_3909_);
v_val_3911_ = lean_ctor_get(v_a_3907_, 0);
lean_inc(v_val_3911_);
lean_dec_ref_known(v_a_3907_, 1);
if (v___x_3809_ == 0)
{
v___y_3913_ = v_a_3737_;
v___y_3914_ = v_a_3738_;
v___y_3915_ = v_a_3739_;
v___y_3916_ = v_a_3740_;
goto v___jp_3912_;
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3949_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3911_);
v___x_3950_ = l_Lean_MessageData_ofExpr(v_val_3911_);
v___x_3951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3949_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3806_, v___x_3951_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_dec_ref_known(v___x_3952_, 1);
v___y_3913_ = v_a_3737_;
v___y_3914_ = v_a_3738_;
v___y_3915_ = v_a_3739_;
v___y_3916_ = v_a_3740_;
goto v___jp_3912_;
}
else
{
lean_dec(v_val_3911_);
lean_dec(v_name_3752_);
lean_del_object(v___x_3748_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
return v___x_3952_;
}
}
v___jp_3912_:
{
lean_object* v___x_3917_; 
lean_inc(v_val_3911_);
v___x_3917_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3736_, v_val_3911_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3919_; lean_object* v_a_3920_; lean_object* v___x_3921_; lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3940_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
v___x_3919_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3911_, v___y_3914_);
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref(v___x_3919_);
v___x_3921_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3918_, v___y_3914_);
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3924_ = v___x_3921_;
v_isShared_3925_ = v_isSharedCheck_3940_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3921_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3940_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
lean_inc(v_name_3752_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 2, v_a_3920_);
lean_ctor_set(v___x_3748_, 0, v_name_3752_);
v___x_3927_ = v___x_3748_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_name_3752_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v_levelParams_3746_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_a_3920_);
v___x_3927_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
v___x_3928_ = lean_box(0);
lean_inc(v_name_3752_);
v___x_3929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3929_, 0, v_name_3752_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3927_);
lean_ctor_set(v___x_3930_, 1, v_a_3922_);
lean_ctor_set(v___x_3930_, 2, v___x_3929_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set_tag(v___x_3924_, 2);
lean_ctor_set(v___x_3924_, 0, v___x_3930_);
v___x_3932_ = v___x_3924_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_addDecl(v___x_3932_, v___x_3905_, v___y_3915_, v___y_3916_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v___x_3934_; uint8_t v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec_ref_known(v___x_3933_, 1);
v___x_3934_ = l_Lean_Meta_simpExtension;
v___x_3935_ = 0;
v___x_3936_ = lean_unsigned_to_nat(1000u);
v___x_3937_ = l_Lean_Meta_addSimpTheorem(v___x_3934_, v_name_3752_, v_hasTrace_3751_, v___x_3905_, v___x_3935_, v___x_3936_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
return v___x_3937_;
}
else
{
lean_dec(v_name_3752_);
return v___x_3933_;
}
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec(v_val_3911_);
lean_dec(v_name_3752_);
lean_del_object(v___x_3748_);
lean_dec(v_levelParams_3746_);
v_a_3941_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3917_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3917_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
}
else
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
lean_dec(v_a_3907_);
lean_dec(v_name_3752_);
lean_del_object(v___x_3748_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v___x_3953_ = lean_box(0);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3953_);
v___x_3955_ = v___x_3909_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec(v_name_3752_);
lean_del_object(v___x_3748_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v_a_3958_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3906_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3906_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
else
{
lean_del_object(v___x_3748_);
goto v___jp_3869_;
}
}
else
{
lean_del_object(v___x_3748_);
goto v___jp_3869_;
}
v___jp_3810_:
{
lean_object* v___x_3814_; double v___x_3815_; double v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3814_ = lean_io_get_num_heartbeats();
v___x_3815_ = lean_float_of_nat(v___y_3812_);
v___x_3816_ = lean_float_of_nat(v___x_3814_);
v___x_3817_ = lean_box_float(v___x_3815_);
v___x_3818_ = lean_box_float(v___x_3816_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v_a_3813_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3806_, v_hasTrace_3751_, v___x_3807_, v_options_3744_, v___x_3809_, v___y_3811_, v___f_3805_, v___x_3820_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
return v___x_3821_;
}
v___jp_3822_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v_a_3825_);
v___y_3811_ = v___y_3823_;
v___y_3812_ = v___y_3824_;
v_a_3813_ = v___x_3826_;
goto v___jp_3810_;
}
v___jp_3827_:
{
lean_object* v___x_3831_; 
v___x_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3831_, 0, v_a_3830_);
v___y_3811_ = v___y_3828_;
v___y_3812_ = v___y_3829_;
v_a_3813_ = v___x_3831_;
goto v___jp_3810_;
}
v___jp_3832_:
{
if (lean_obj_tag(v___y_3835_) == 0)
{
lean_object* v_a_3836_; 
v_a_3836_ = lean_ctor_get(v___y_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref_known(v___y_3835_, 1);
v___y_3828_ = v___y_3833_;
v___y_3829_ = v___y_3834_;
v_a_3830_ = v_a_3836_;
goto v___jp_3827_;
}
else
{
lean_object* v_a_3837_; 
v_a_3837_ = lean_ctor_get(v___y_3835_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v___y_3835_, 1);
v___y_3823_ = v___y_3833_;
v___y_3824_ = v___y_3834_;
v_a_3825_ = v_a_3837_;
goto v___jp_3822_;
}
}
v___jp_3838_:
{
lean_object* v___x_3842_; double v___x_3843_; double v___x_3844_; double v___x_3845_; double v___x_3846_; double v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3842_ = lean_io_mono_nanos_now();
v___x_3843_ = lean_float_of_nat(v___y_3840_);
v___x_3844_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3845_ = lean_float_div(v___x_3843_, v___x_3844_);
v___x_3846_ = lean_float_of_nat(v___x_3842_);
v___x_3847_ = lean_float_div(v___x_3846_, v___x_3844_);
v___x_3848_ = lean_box_float(v___x_3845_);
v___x_3849_ = lean_box_float(v___x_3847_);
v___x_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3851_, 0, v_a_3841_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3806_, v_hasTrace_3751_, v___x_3807_, v_options_3744_, v___x_3809_, v___y_3839_, v___f_3805_, v___x_3851_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
return v___x_3852_;
}
v___jp_3853_:
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3857_, 0, v_a_3856_);
v___y_3839_ = v___y_3854_;
v___y_3840_ = v___y_3855_;
v_a_3841_ = v___x_3857_;
goto v___jp_3838_;
}
v___jp_3858_:
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v_a_3861_);
v___y_3839_ = v___y_3859_;
v___y_3840_ = v___y_3860_;
v_a_3841_ = v___x_3862_;
goto v___jp_3838_;
}
v___jp_3863_:
{
if (lean_obj_tag(v___y_3866_) == 0)
{
lean_object* v_a_3867_; 
v_a_3867_ = lean_ctor_get(v___y_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___y_3866_, 1);
v___y_3854_ = v___y_3864_;
v___y_3855_ = v___y_3865_;
v_a_3856_ = v_a_3867_;
goto v___jp_3853_;
}
else
{
lean_object* v_a_3868_; 
v_a_3868_ = lean_ctor_get(v___y_3866_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___y_3866_, 1);
v___y_3859_ = v___y_3864_;
v___y_3860_ = v___y_3865_;
v_a_3861_ = v_a_3868_;
goto v___jp_3858_;
}
}
v___jp_3869_:
{
lean_object* v___x_3870_; lean_object* v_a_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v___x_3870_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3740_);
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3870_);
v___x_3872_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3873_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3744_, v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3736_);
v___x_3875_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 1);
if (lean_obj_tag(v_a_3876_) == 1)
{
if (v___x_3809_ == 0)
{
lean_object* v_val_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v_val_3877_ = lean_ctor_get(v_a_3876_, 0);
lean_inc(v_val_3877_);
lean_dec_ref_known(v_a_3876_, 1);
v___x_3878_ = lean_box(0);
v___x_3879_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3736_, v_val_3877_, v_name_3752_, v_levelParams_3746_, v___x_3873_, v_hasTrace_3751_, v___x_3878_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
v___y_3864_ = v_a_3871_;
v___y_3865_ = v___x_3874_;
v___y_3866_ = v___x_3879_;
goto v___jp_3863_;
}
else
{
lean_object* v_val_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_val_3880_ = lean_ctor_get(v_a_3876_, 0);
lean_inc_n(v_val_3880_, 2);
lean_dec_ref_known(v_a_3876_, 1);
v___x_3881_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3882_ = l_Lean_MessageData_ofExpr(v_val_3880_);
v___x_3883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3881_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
v___x_3884_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3806_, v___x_3883_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3886_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
v___x_3886_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3736_, v_val_3880_, v_name_3752_, v_levelParams_3746_, v___x_3873_, v_hasTrace_3751_, v_a_3885_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
v___y_3864_ = v_a_3871_;
v___y_3865_ = v___x_3874_;
v___y_3866_ = v___x_3886_;
goto v___jp_3863_;
}
else
{
lean_dec(v_val_3880_);
lean_dec(v_name_3752_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v___y_3864_ = v_a_3871_;
v___y_3865_ = v___x_3874_;
v___y_3866_ = v___x_3884_;
goto v___jp_3863_;
}
}
}
else
{
lean_object* v___x_3887_; 
lean_dec(v_a_3876_);
lean_dec(v_name_3752_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v___x_3887_ = lean_box(0);
v___y_3854_ = v_a_3871_;
v___y_3855_ = v___x_3874_;
v_a_3856_ = v___x_3887_;
goto v___jp_3853_;
}
}
else
{
lean_object* v_a_3888_; 
lean_dec(v_name_3752_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v_a_3888_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3875_, 1);
v___y_3859_ = v_a_3871_;
v___y_3860_ = v___x_3874_;
v_a_3861_ = v_a_3888_;
goto v___jp_3858_;
}
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3736_);
v___x_3890_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
if (lean_obj_tag(v_a_3891_) == 1)
{
if (v___x_3809_ == 0)
{
lean_object* v_val_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_val_3892_ = lean_ctor_get(v_a_3891_, 0);
lean_inc(v_val_3892_);
lean_dec_ref_known(v_a_3891_, 1);
v___x_3893_ = lean_box(0);
v___x_3894_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3736_, v_val_3892_, v_name_3752_, v_levelParams_3746_, v___x_3873_, v___x_3893_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
v___y_3833_ = v_a_3871_;
v___y_3834_ = v___x_3889_;
v___y_3835_ = v___x_3894_;
goto v___jp_3832_;
}
else
{
lean_object* v_val_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_val_3895_ = lean_ctor_get(v_a_3891_, 0);
lean_inc_n(v_val_3895_, 2);
lean_dec_ref_known(v_a_3891_, 1);
v___x_3896_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3897_ = l_Lean_MessageData_ofExpr(v_val_3895_);
v___x_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3896_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3806_, v___x_3898_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3901_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v___x_3901_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3736_, v_val_3895_, v_name_3752_, v_levelParams_3746_, v___x_3873_, v_a_3900_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
v___y_3833_ = v_a_3871_;
v___y_3834_ = v___x_3889_;
v___y_3835_ = v___x_3901_;
goto v___jp_3832_;
}
else
{
lean_dec(v_val_3895_);
lean_dec(v_name_3752_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v___y_3833_ = v_a_3871_;
v___y_3834_ = v___x_3889_;
v___y_3835_ = v___x_3899_;
goto v___jp_3832_;
}
}
}
else
{
lean_object* v___x_3902_; 
lean_dec(v_a_3891_);
lean_dec(v_name_3752_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v___x_3902_ = lean_box(0);
v___y_3828_ = v_a_3871_;
v___y_3829_ = v___x_3889_;
v_a_3830_ = v___x_3902_;
goto v___jp_3827_;
}
}
else
{
lean_object* v_a_3903_; 
lean_dec(v_name_3752_);
lean_dec(v_levelParams_3746_);
lean_dec_ref(v_ctorVal_3736_);
v_a_3903_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3890_, 1);
v___y_3823_ = v_a_3871_;
v___y_3824_ = v___x_3889_;
v_a_3825_ = v_a_3903_;
goto v___jp_3822_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_);
lean_dec(v_a_3972_);
lean_dec_ref(v_a_3971_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3975_, lean_object* v_decl_3976_, lean_object* v_ref_3977_){
_start:
{
lean_object* v_defValue_3979_; lean_object* v_descr_3980_; lean_object* v_deprecation_x3f_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v_defValue_3979_ = lean_ctor_get(v_decl_3976_, 0);
v_descr_3980_ = lean_ctor_get(v_decl_3976_, 1);
v_deprecation_x3f_3981_ = lean_ctor_get(v_decl_3976_, 2);
v___x_3982_ = lean_alloc_ctor(1, 0, 1);
v___x_3983_ = lean_unbox(v_defValue_3979_);
lean_ctor_set_uint8(v___x_3982_, 0, v___x_3983_);
lean_inc(v_deprecation_x3f_3981_);
lean_inc_ref(v_descr_3980_);
lean_inc_n(v_name_3975_, 2);
v___x_3984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3984_, 0, v_name_3975_);
lean_ctor_set(v___x_3984_, 1, v_ref_3977_);
lean_ctor_set(v___x_3984_, 2, v___x_3982_);
lean_ctor_set(v___x_3984_, 3, v_descr_3980_);
lean_ctor_set(v___x_3984_, 4, v_deprecation_x3f_3981_);
v___x_3985_ = lean_register_option(v_name_3975_, v___x_3984_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3993_; 
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_3993_ == 0)
{
lean_object* v_unused_3994_; 
v_unused_3994_ = lean_ctor_get(v___x_3985_, 0);
lean_dec(v_unused_3994_);
v___x_3987_ = v___x_3985_;
v_isShared_3988_ = v_isSharedCheck_3993_;
goto v_resetjp_3986_;
}
else
{
lean_dec(v___x_3985_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3993_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
lean_inc(v_defValue_3979_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v_name_3975_);
lean_ctor_set(v___x_3989_, 1, v_defValue_3979_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3989_);
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec(v_name_3975_);
v_a_3995_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3985_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3985_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4003_, lean_object* v_decl_4004_, lean_object* v_ref_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4003_, v_decl_4004_, v_ref_4005_);
lean_dec_ref(v_decl_4004_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4022_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4023_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4024_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4025_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4022_, v___x_4023_, v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4028_, uint8_t v_isExporting_4029_, lean_object* v___x_4030_, lean_object* v___y_4031_, lean_object* v___x_4032_, lean_object* v_a_x3f_4033_){
_start:
{
lean_object* v___x_4035_; lean_object* v_env_4036_; lean_object* v_nextMacroScope_4037_; lean_object* v_ngen_4038_; lean_object* v_auxDeclNGen_4039_; lean_object* v_traceState_4040_; lean_object* v_recordedDeps_4041_; lean_object* v_messages_4042_; lean_object* v_infoState_4043_; lean_object* v_snapshotTasks_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4069_; 
v___x_4035_ = lean_st_ref_take(v___y_4028_);
v_env_4036_ = lean_ctor_get(v___x_4035_, 0);
v_nextMacroScope_4037_ = lean_ctor_get(v___x_4035_, 1);
v_ngen_4038_ = lean_ctor_get(v___x_4035_, 2);
v_auxDeclNGen_4039_ = lean_ctor_get(v___x_4035_, 3);
v_traceState_4040_ = lean_ctor_get(v___x_4035_, 4);
v_recordedDeps_4041_ = lean_ctor_get(v___x_4035_, 6);
v_messages_4042_ = lean_ctor_get(v___x_4035_, 7);
v_infoState_4043_ = lean_ctor_get(v___x_4035_, 8);
v_snapshotTasks_4044_ = lean_ctor_get(v___x_4035_, 9);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4069_ == 0)
{
lean_object* v_unused_4070_; 
v_unused_4070_ = lean_ctor_get(v___x_4035_, 5);
lean_dec(v_unused_4070_);
v___x_4046_ = v___x_4035_;
v_isShared_4047_ = v_isSharedCheck_4069_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_snapshotTasks_4044_);
lean_inc(v_infoState_4043_);
lean_inc(v_messages_4042_);
lean_inc(v_recordedDeps_4041_);
lean_inc(v_traceState_4040_);
lean_inc(v_auxDeclNGen_4039_);
lean_inc(v_ngen_4038_);
lean_inc(v_nextMacroScope_4037_);
lean_inc(v_env_4036_);
lean_dec(v___x_4035_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4069_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4048_; lean_object* v___x_4050_; 
v___x_4048_ = l_Lean_Environment_setExporting(v_env_4036_, v_isExporting_4029_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 5, v___x_4030_);
lean_ctor_set(v___x_4046_, 0, v___x_4048_);
v___x_4050_ = v___x_4046_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4048_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v_nextMacroScope_4037_);
lean_ctor_set(v_reuseFailAlloc_4068_, 2, v_ngen_4038_);
lean_ctor_set(v_reuseFailAlloc_4068_, 3, v_auxDeclNGen_4039_);
lean_ctor_set(v_reuseFailAlloc_4068_, 4, v_traceState_4040_);
lean_ctor_set(v_reuseFailAlloc_4068_, 5, v___x_4030_);
lean_ctor_set(v_reuseFailAlloc_4068_, 6, v_recordedDeps_4041_);
lean_ctor_set(v_reuseFailAlloc_4068_, 7, v_messages_4042_);
lean_ctor_set(v_reuseFailAlloc_4068_, 8, v_infoState_4043_);
lean_ctor_set(v_reuseFailAlloc_4068_, 9, v_snapshotTasks_4044_);
v___x_4050_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v_mctx_4053_; lean_object* v_zetaDeltaFVarIds_4054_; lean_object* v_postponed_4055_; lean_object* v_diag_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4066_; 
v___x_4051_ = lean_st_ref_put(v___y_4028_, v___x_4050_);
v___x_4052_ = lean_st_ref_take(v___y_4031_);
v_mctx_4053_ = lean_ctor_get(v___x_4052_, 0);
v_zetaDeltaFVarIds_4054_ = lean_ctor_get(v___x_4052_, 2);
v_postponed_4055_ = lean_ctor_get(v___x_4052_, 3);
v_diag_4056_ = lean_ctor_get(v___x_4052_, 4);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; 
v_unused_4067_ = lean_ctor_get(v___x_4052_, 1);
lean_dec(v_unused_4067_);
v___x_4058_ = v___x_4052_;
v_isShared_4059_ = v_isSharedCheck_4066_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_diag_4056_);
lean_inc(v_postponed_4055_);
lean_inc(v_zetaDeltaFVarIds_4054_);
lean_inc(v_mctx_4053_);
lean_dec(v___x_4052_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4066_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4060_; lean_object* v___x_4062_; 
v___x_4060_ = lean_box(0);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v___x_4032_);
v___x_4062_ = v___x_4058_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_mctx_4053_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_zetaDeltaFVarIds_4054_);
lean_ctor_set(v_reuseFailAlloc_4065_, 3, v_postponed_4055_);
lean_ctor_set(v_reuseFailAlloc_4065_, 4, v_diag_4056_);
v___x_4062_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_st_ref_put(v___y_4031_, v___x_4062_);
v___x_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4060_);
return v___x_4064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4071_, lean_object* v_isExporting_4072_, lean_object* v___x_4073_, lean_object* v___y_4074_, lean_object* v___x_4075_, lean_object* v_a_x3f_4076_, lean_object* v___y_4077_){
_start:
{
uint8_t v_isExporting_boxed_4078_; lean_object* v_res_4079_; 
v_isExporting_boxed_4078_ = lean_unbox(v_isExporting_4072_);
v_res_4079_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4071_, v_isExporting_boxed_4078_, v___x_4073_, v___y_4074_, v___x_4075_, v_a_x3f_4076_);
lean_dec(v_a_x3f_4076_);
lean_dec(v___y_4074_);
lean_dec(v___y_4071_);
return v_res_4079_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4080_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
return v___x_4082_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
lean_ctor_set(v___x_4084_, 1, v___x_4083_);
return v___x_4084_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4086_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
lean_ctor_set(v___x_4086_, 2, v___x_4085_);
lean_ctor_set(v___x_4086_, 3, v___x_4085_);
lean_ctor_set(v___x_4086_, 4, v___x_4085_);
lean_ctor_set(v___x_4086_, 5, v___x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4087_, uint8_t v_isExporting_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v___x_4094_; lean_object* v_env_4095_; lean_object* v___x_4096_; uint8_t v_isModule_4097_; 
v___x_4094_ = lean_st_ref_get(v___y_4092_);
v_env_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc_ref(v_env_4095_);
lean_dec(v___x_4094_);
v___x_4096_ = l_Lean_Environment_header(v_env_4095_);
v_isModule_4097_ = lean_ctor_get_uint8(v___x_4096_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4096_);
if (v_isModule_4097_ == 0)
{
lean_object* v___x_4098_; 
lean_dec_ref(v_env_4095_);
lean_inc(v___y_4092_);
lean_inc_ref(v___y_4091_);
lean_inc(v___y_4090_);
lean_inc_ref(v___y_4089_);
v___x_4098_ = lean_apply_5(v_x_4087_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, lean_box(0));
return v___x_4098_;
}
else
{
uint8_t v_isExporting_4099_; 
v_isExporting_4099_ = lean_ctor_get_uint8(v_env_4095_, sizeof(void*)*13);
lean_dec_ref(v_env_4095_);
if (v_isExporting_4088_ == 0)
{
if (v_isExporting_4099_ == 0)
{
lean_object* v___x_4166_; 
lean_inc(v___y_4092_);
lean_inc_ref(v___y_4091_);
lean_inc(v___y_4090_);
lean_inc_ref(v___y_4089_);
v___x_4166_ = lean_apply_5(v_x_4087_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, lean_box(0));
return v___x_4166_;
}
else
{
goto v___jp_4100_;
}
}
else
{
if (v_isExporting_4099_ == 0)
{
goto v___jp_4100_;
}
else
{
lean_object* v___x_4167_; 
lean_inc(v___y_4092_);
lean_inc_ref(v___y_4091_);
lean_inc(v___y_4090_);
lean_inc_ref(v___y_4089_);
v___x_4167_ = lean_apply_5(v_x_4087_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, lean_box(0));
return v___x_4167_;
}
}
v___jp_4100_:
{
lean_object* v___x_4101_; lean_object* v_env_4102_; lean_object* v_nextMacroScope_4103_; lean_object* v_ngen_4104_; lean_object* v_auxDeclNGen_4105_; lean_object* v_traceState_4106_; lean_object* v_recordedDeps_4107_; lean_object* v_messages_4108_; lean_object* v_infoState_4109_; lean_object* v_snapshotTasks_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4164_; 
v___x_4101_ = lean_st_ref_take(v___y_4092_);
v_env_4102_ = lean_ctor_get(v___x_4101_, 0);
v_nextMacroScope_4103_ = lean_ctor_get(v___x_4101_, 1);
v_ngen_4104_ = lean_ctor_get(v___x_4101_, 2);
v_auxDeclNGen_4105_ = lean_ctor_get(v___x_4101_, 3);
v_traceState_4106_ = lean_ctor_get(v___x_4101_, 4);
v_recordedDeps_4107_ = lean_ctor_get(v___x_4101_, 6);
v_messages_4108_ = lean_ctor_get(v___x_4101_, 7);
v_infoState_4109_ = lean_ctor_get(v___x_4101_, 8);
v_snapshotTasks_4110_ = lean_ctor_get(v___x_4101_, 9);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; 
v_unused_4165_ = lean_ctor_get(v___x_4101_, 5);
lean_dec(v_unused_4165_);
v___x_4112_ = v___x_4101_;
v_isShared_4113_ = v_isSharedCheck_4164_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_snapshotTasks_4110_);
lean_inc(v_infoState_4109_);
lean_inc(v_messages_4108_);
lean_inc(v_recordedDeps_4107_);
lean_inc(v_traceState_4106_);
lean_inc(v_auxDeclNGen_4105_);
lean_inc(v_ngen_4104_);
lean_inc(v_nextMacroScope_4103_);
lean_inc(v_env_4102_);
lean_dec(v___x_4101_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4164_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4117_; 
v___x_4114_ = l_Lean_Environment_setExporting(v_env_4102_, v_isExporting_4088_);
v___x_4115_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4113_ == 0)
{
lean_ctor_set(v___x_4112_, 5, v___x_4115_);
lean_ctor_set(v___x_4112_, 0, v___x_4114_);
v___x_4117_ = v___x_4112_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4114_);
lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_nextMacroScope_4103_);
lean_ctor_set(v_reuseFailAlloc_4163_, 2, v_ngen_4104_);
lean_ctor_set(v_reuseFailAlloc_4163_, 3, v_auxDeclNGen_4105_);
lean_ctor_set(v_reuseFailAlloc_4163_, 4, v_traceState_4106_);
lean_ctor_set(v_reuseFailAlloc_4163_, 5, v___x_4115_);
lean_ctor_set(v_reuseFailAlloc_4163_, 6, v_recordedDeps_4107_);
lean_ctor_set(v_reuseFailAlloc_4163_, 7, v_messages_4108_);
lean_ctor_set(v_reuseFailAlloc_4163_, 8, v_infoState_4109_);
lean_ctor_set(v_reuseFailAlloc_4163_, 9, v_snapshotTasks_4110_);
v___x_4117_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v_mctx_4120_; lean_object* v_zetaDeltaFVarIds_4121_; lean_object* v_postponed_4122_; lean_object* v_diag_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4161_; 
v___x_4118_ = lean_st_ref_put(v___y_4092_, v___x_4117_);
v___x_4119_ = lean_st_ref_take(v___y_4090_);
v_mctx_4120_ = lean_ctor_get(v___x_4119_, 0);
v_zetaDeltaFVarIds_4121_ = lean_ctor_get(v___x_4119_, 2);
v_postponed_4122_ = lean_ctor_get(v___x_4119_, 3);
v_diag_4123_ = lean_ctor_get(v___x_4119_, 4);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; 
v_unused_4162_ = lean_ctor_get(v___x_4119_, 1);
lean_dec(v_unused_4162_);
v___x_4125_ = v___x_4119_;
v_isShared_4126_ = v_isSharedCheck_4161_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_diag_4123_);
lean_inc(v_postponed_4122_);
lean_inc(v_zetaDeltaFVarIds_4121_);
lean_inc(v_mctx_4120_);
lean_dec(v___x_4119_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4161_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___x_4129_; 
v___x_4127_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 1, v___x_4127_);
v___x_4129_ = v___x_4125_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_mctx_4120_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v___x_4127_);
lean_ctor_set(v_reuseFailAlloc_4160_, 2, v_zetaDeltaFVarIds_4121_);
lean_ctor_set(v_reuseFailAlloc_4160_, 3, v_postponed_4122_);
lean_ctor_set(v_reuseFailAlloc_4160_, 4, v_diag_4123_);
v___x_4129_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4130_; lean_object* v_r_4131_; 
v___x_4130_ = lean_st_ref_put(v___y_4090_, v___x_4129_);
lean_inc(v___y_4092_);
lean_inc_ref(v___y_4091_);
lean_inc(v___y_4090_);
lean_inc_ref(v___y_4089_);
v_r_4131_ = lean_apply_5(v_x_4087_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, lean_box(0));
if (lean_obj_tag(v_r_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4148_; 
v_a_4132_ = lean_ctor_get(v_r_4131_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_r_4131_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4134_ = v_r_4131_;
v_isShared_4135_ = v_isSharedCheck_4148_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v_r_4131_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4148_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
lean_inc(v_a_4132_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set_tag(v___x_4134_, 1);
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
v___x_4138_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4092_, v_isExporting_4099_, v___x_4115_, v___y_4090_, v___x_4127_, v___x_4137_);
lean_dec_ref(v___x_4137_);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4145_ == 0)
{
lean_object* v_unused_4146_; 
v_unused_4146_ = lean_ctor_get(v___x_4138_, 0);
lean_dec(v_unused_4146_);
v___x_4140_ = v___x_4138_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_dec(v___x_4138_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 0, v_a_4132_);
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4132_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
v_a_4149_ = lean_ctor_get(v_r_4131_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v_r_4131_, 1);
v___x_4150_ = lean_box(0);
v___x_4151_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4092_, v_isExporting_4099_, v___x_4115_, v___y_4090_, v___x_4127_, v___x_4150_);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4158_ == 0)
{
lean_object* v_unused_4159_; 
v_unused_4159_ = lean_ctor_get(v___x_4151_, 0);
lean_dec(v_unused_4159_);
v___x_4153_ = v___x_4151_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_dec(v___x_4151_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
lean_ctor_set_tag(v___x_4153_, 1);
lean_ctor_set(v___x_4153_, 0, v_a_4149_);
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4149_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
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
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4168_, lean_object* v_isExporting_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
uint8_t v_isExporting_boxed_4175_; lean_object* v_res_4176_; 
v_isExporting_boxed_4175_ = lean_unbox(v_isExporting_4169_);
v_res_4176_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4168_, v_isExporting_boxed_4175_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4177_, lean_object* v_x_4178_, uint8_t v_isExporting_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4178_, v_isExporting_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4186_, lean_object* v_x_4187_, lean_object* v_isExporting_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
uint8_t v_isExporting_boxed_4194_; lean_object* v_res_4195_; 
v_isExporting_boxed_4194_ = lean_unbox(v_isExporting_4188_);
v_res_4195_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4186_, v_x_4187_, v_isExporting_boxed_4194_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4196_, lean_object* v_localInsts_4197_, lean_object* v_x_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4196_, v_localInsts_4197_, v_x_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
v_a_4213_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4204_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4204_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4221_, lean_object* v_localInsts_4222_, lean_object* v_x_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4221_, v_localInsts_4222_, v_x_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4230_, lean_object* v_lctx_4231_, lean_object* v_localInsts_4232_, lean_object* v_x_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4231_, v_localInsts_4232_, v_x_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4240_, lean_object* v_lctx_4241_, lean_object* v_localInsts_4242_, lean_object* v_x_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4240_, v_lctx_4241_, v_localInsts_4242_, v_x_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4250_, lean_object* v_x_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4257_ = l_Lean_MessageData_ofName(v_declName_4250_);
v___x_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4257_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4259_, lean_object* v_x_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4259_, v_x_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec_ref(v_x_4260_);
return v_res_4266_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_instMonadEIO___redArg();
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v_toApplicative_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4341_; 
v___x_4278_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4279_ = l_StateRefT_x27_instMonad___redArg(v___x_4278_);
v_toApplicative_4280_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4341_ == 0)
{
lean_object* v_unused_4342_; 
v_unused_4342_ = lean_ctor_get(v___x_4279_, 1);
lean_dec(v_unused_4342_);
v___x_4282_ = v___x_4279_;
v_isShared_4283_ = v_isSharedCheck_4341_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_toApplicative_4280_);
lean_dec(v___x_4279_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4341_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v_toFunctor_4284_; lean_object* v_toSeq_4285_; lean_object* v_toSeqLeft_4286_; lean_object* v_toSeqRight_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4339_; 
v_toFunctor_4284_ = lean_ctor_get(v_toApplicative_4280_, 0);
v_toSeq_4285_ = lean_ctor_get(v_toApplicative_4280_, 2);
v_toSeqLeft_4286_ = lean_ctor_get(v_toApplicative_4280_, 3);
v_toSeqRight_4287_ = lean_ctor_get(v_toApplicative_4280_, 4);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_toApplicative_4280_);
if (v_isSharedCheck_4339_ == 0)
{
lean_object* v_unused_4340_; 
v_unused_4340_ = lean_ctor_get(v_toApplicative_4280_, 1);
lean_dec(v_unused_4340_);
v___x_4289_ = v_toApplicative_4280_;
v_isShared_4290_ = v_isSharedCheck_4339_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_toSeqRight_4287_);
lean_inc(v_toSeqLeft_4286_);
lean_inc(v_toSeq_4285_);
lean_inc(v_toFunctor_4284_);
lean_dec(v_toApplicative_4280_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4339_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___f_4291_; lean_object* v___f_4292_; lean_object* v___f_4293_; lean_object* v___f_4294_; lean_object* v___x_4295_; lean_object* v___f_4296_; lean_object* v___f_4297_; lean_object* v___f_4298_; lean_object* v___x_4300_; 
v___f_4291_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4292_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4284_);
v___f_4293_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4293_, 0, v_toFunctor_4284_);
v___f_4294_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4294_, 0, v_toFunctor_4284_);
v___x_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___f_4293_);
lean_ctor_set(v___x_4295_, 1, v___f_4294_);
v___f_4296_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4296_, 0, v_toSeqRight_4287_);
v___f_4297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4297_, 0, v_toSeqLeft_4286_);
v___f_4298_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4298_, 0, v_toSeq_4285_);
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 4, v___f_4296_);
lean_ctor_set(v___x_4289_, 3, v___f_4297_);
lean_ctor_set(v___x_4289_, 2, v___f_4298_);
lean_ctor_set(v___x_4289_, 1, v___f_4291_);
lean_ctor_set(v___x_4289_, 0, v___x_4295_);
v___x_4300_ = v___x_4289_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4295_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v___f_4291_);
lean_ctor_set(v_reuseFailAlloc_4338_, 2, v___f_4298_);
lean_ctor_set(v_reuseFailAlloc_4338_, 3, v___f_4297_);
lean_ctor_set(v_reuseFailAlloc_4338_, 4, v___f_4296_);
v___x_4300_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
lean_object* v___x_4302_; 
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 1, v___f_4292_);
lean_ctor_set(v___x_4282_, 0, v___x_4300_);
v___x_4302_ = v___x_4282_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4300_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v___f_4292_);
v___x_4302_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
lean_object* v___x_4303_; lean_object* v_toApplicative_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4335_; 
v___x_4303_ = l_StateRefT_x27_instMonad___redArg(v___x_4302_);
v_toApplicative_4304_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4335_ == 0)
{
lean_object* v_unused_4336_; 
v_unused_4336_ = lean_ctor_get(v___x_4303_, 1);
lean_dec(v_unused_4336_);
v___x_4306_ = v___x_4303_;
v_isShared_4307_ = v_isSharedCheck_4335_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_toApplicative_4304_);
lean_dec(v___x_4303_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4335_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v_toFunctor_4308_; lean_object* v_toSeq_4309_; lean_object* v_toSeqLeft_4310_; lean_object* v_toSeqRight_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4333_; 
v_toFunctor_4308_ = lean_ctor_get(v_toApplicative_4304_, 0);
v_toSeq_4309_ = lean_ctor_get(v_toApplicative_4304_, 2);
v_toSeqLeft_4310_ = lean_ctor_get(v_toApplicative_4304_, 3);
v_toSeqRight_4311_ = lean_ctor_get(v_toApplicative_4304_, 4);
v_isSharedCheck_4333_ = !lean_is_exclusive(v_toApplicative_4304_);
if (v_isSharedCheck_4333_ == 0)
{
lean_object* v_unused_4334_; 
v_unused_4334_ = lean_ctor_get(v_toApplicative_4304_, 1);
lean_dec(v_unused_4334_);
v___x_4313_ = v_toApplicative_4304_;
v_isShared_4314_ = v_isSharedCheck_4333_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_toSeqRight_4311_);
lean_inc(v_toSeqLeft_4310_);
lean_inc(v_toSeq_4309_);
lean_inc(v_toFunctor_4308_);
lean_dec(v_toApplicative_4304_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4333_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___f_4315_; lean_object* v___f_4316_; lean_object* v___f_4317_; lean_object* v___f_4318_; lean_object* v___x_4319_; lean_object* v___f_4320_; lean_object* v___f_4321_; lean_object* v___f_4322_; lean_object* v___x_4324_; 
v___f_4315_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4316_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4308_);
v___f_4317_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4317_, 0, v_toFunctor_4308_);
v___f_4318_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4318_, 0, v_toFunctor_4308_);
v___x_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___f_4317_);
lean_ctor_set(v___x_4319_, 1, v___f_4318_);
v___f_4320_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4320_, 0, v_toSeqRight_4311_);
v___f_4321_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4321_, 0, v_toSeqLeft_4310_);
v___f_4322_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4322_, 0, v_toSeq_4309_);
if (v_isShared_4314_ == 0)
{
lean_ctor_set(v___x_4313_, 4, v___f_4320_);
lean_ctor_set(v___x_4313_, 3, v___f_4321_);
lean_ctor_set(v___x_4313_, 2, v___f_4322_);
lean_ctor_set(v___x_4313_, 1, v___f_4315_);
lean_ctor_set(v___x_4313_, 0, v___x_4319_);
v___x_4324_ = v___x_4313_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4319_);
lean_ctor_set(v_reuseFailAlloc_4332_, 1, v___f_4315_);
lean_ctor_set(v_reuseFailAlloc_4332_, 2, v___f_4322_);
lean_ctor_set(v_reuseFailAlloc_4332_, 3, v___f_4321_);
lean_ctor_set(v_reuseFailAlloc_4332_, 4, v___f_4320_);
v___x_4324_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
lean_object* v___x_4326_; 
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 1, v___f_4316_);
lean_ctor_set(v___x_4306_, 0, v___x_4324_);
v___x_4326_ = v___x_4306_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4324_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v___f_4316_);
v___x_4326_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_15720__overap_4329_; lean_object* v___x_4330_; 
v___x_4327_ = lean_box(0);
v___x_4328_ = l_instInhabitedOfMonad___redArg(v___x_4326_, v___x_4327_);
v___x_15720__overap_4329_ = lean_panic_fn_borrowed(v___x_4328_, v_msg_4272_);
lean_dec(v___x_4328_);
lean_inc(v___y_4276_);
lean_inc_ref(v___y_4275_);
lean_inc(v___y_4274_);
lean_inc_ref(v___y_4273_);
v___x_4330_ = lean_apply_5(v___x_15720__overap_4329_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, lean_box(0));
return v___x_4330_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
return v_res_4349_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4352_ = l_Lean_stringToMessageData(v___x_4351_);
return v___x_4352_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4355_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4356_ = lean_unsigned_to_nat(11u);
v___x_4357_ = lean_unsigned_to_nat(122u);
v___x_4358_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4359_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4360_ = l_mkPanicMessageWithDecl(v___x_4359_, v___x_4358_, v___x_4357_, v___x_4356_, v___x_4355_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v___x_4375_; lean_object* v_env_4376_; uint8_t v___x_4377_; lean_object* v___x_4378_; 
v___x_4375_ = lean_st_ref_get(v___y_4365_);
v_env_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc_ref(v_env_4376_);
lean_dec(v___x_4375_);
v___x_4377_ = 0;
lean_inc(v_constName_4361_);
v___x_4378_ = l_Lean_Environment_findAsync_x3f(v_env_4376_, v_constName_4361_, v___x_4377_);
if (lean_obj_tag(v___x_4378_) == 1)
{
lean_object* v_val_4379_; uint8_t v_kind_4380_; 
v_val_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_val_4379_);
lean_dec_ref_known(v___x_4378_, 1);
v_kind_4380_ = lean_ctor_get_uint8(v_val_4379_, sizeof(void*)*3);
if (v_kind_4380_ == 6)
{
lean_object* v___x_4381_; 
v___x_4381_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4379_);
if (lean_obj_tag(v___x_4381_) == 6)
{
lean_object* v_val_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_dec(v_constName_4361_);
v_val_4382_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4381_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_val_4382_);
lean_dec(v___x_4381_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set_tag(v___x_4384_, 0);
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_val_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
else
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
lean_dec_ref(v___x_4381_);
v___x_4390_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4391_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4390_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4400_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4394_ = v___x_4391_;
v_isShared_4395_ = v_isSharedCheck_4400_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4400_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
if (lean_obj_tag(v_a_4392_) == 0)
{
lean_del_object(v___x_4394_);
goto v___jp_4367_;
}
else
{
lean_object* v_val_4396_; lean_object* v___x_4398_; 
lean_dec(v_constName_4361_);
v_val_4396_ = lean_ctor_get(v_a_4392_, 0);
lean_inc(v_val_4396_);
lean_dec_ref_known(v_a_4392_, 1);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v_val_4396_);
v___x_4398_ = v___x_4394_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_val_4396_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_constName_4361_);
v_a_4401_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4391_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4391_);
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
}
else
{
lean_dec(v_val_4379_);
goto v___jp_4367_;
}
}
else
{
lean_dec(v___x_4378_);
goto v___jp_4367_;
}
v___jp_4367_:
{
lean_object* v___x_4368_; uint8_t v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4368_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4369_ = 0;
v___x_4370_ = l_Lean_MessageData_ofConstName(v_constName_4361_, v___x_4369_);
v___x_4371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4368_);
lean_ctor_set(v___x_4371_, 1, v___x_4370_);
v___x_4372_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4371_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4373_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
return v___x_4374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4416_, lean_object* v___x_4417_, lean_object* v___x_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4416_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4436_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4427_ = v___x_4424_;
v_isShared_4428_ = v_isSharedCheck_4436_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4436_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v_numFields_4429_; uint8_t v___x_4430_; 
v_numFields_4429_ = lean_ctor_get(v_a_4425_, 4);
v___x_4430_ = lean_nat_dec_lt(v___x_4417_, v_numFields_4429_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4432_; 
lean_dec(v_a_4425_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___x_4418_);
v___x_4432_ = v___x_4427_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4418_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
else
{
lean_object* v___x_4434_; 
lean_del_object(v___x_4427_);
lean_inc(v_a_4425_);
v___x_4434_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4425_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_object* v___x_4435_; 
lean_dec_ref_known(v___x_4434_, 1);
v___x_4435_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4425_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
return v___x_4435_;
}
else
{
lean_dec(v_a_4425_);
return v___x_4434_;
}
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
v_a_4437_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4424_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4424_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4445_, lean_object* v___x_4446_, lean_object* v___x_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4445_, v___x_4446_, v___x_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___x_4446_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4454_, uint8_t v___x_4455_, lean_object* v_as_x27_4456_, lean_object* v_b_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
if (lean_obj_tag(v_as_x27_4456_) == 0)
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v_b_4457_);
return v___x_4463_;
}
else
{
lean_object* v_head_4464_; lean_object* v_tail_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___f_4468_; uint8_t v___y_4470_; uint8_t v___x_4473_; 
v_head_4464_ = lean_ctor_get(v_as_x27_4456_, 0);
v_tail_4465_ = lean_ctor_get(v_as_x27_4456_, 1);
v___x_4466_ = lean_unsigned_to_nat(0u);
v___x_4467_ = lean_box(0);
lean_inc(v_head_4464_);
v___f_4468_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4468_, 0, v_head_4464_);
lean_closure_set(v___f_4468_, 1, v___x_4466_);
lean_closure_set(v___f_4468_, 2, v___x_4467_);
v___x_4473_ = l_Lean_isPrivateName(v_head_4464_);
if (v___x_4473_ == 0)
{
v___y_4470_ = v___y_4454_;
goto v___jp_4469_;
}
else
{
v___y_4470_ = v___x_4455_;
goto v___jp_4469_;
}
v___jp_4469_:
{
lean_object* v___x_4471_; 
v___x_4471_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4468_, v___y_4470_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_dec_ref_known(v___x_4471_, 1);
v_as_x27_4456_ = v_tail_4465_;
v_b_4457_ = v___x_4467_;
goto _start;
}
else
{
return v___x_4471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4474_, lean_object* v___x_4475_, lean_object* v_as_x27_4476_, lean_object* v_b_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
uint8_t v___y_16840__boxed_4483_; uint8_t v___x_16841__boxed_4484_; lean_object* v_res_4485_; 
v___y_16840__boxed_4483_ = lean_unbox(v___y_4474_);
v___x_16841__boxed_4484_ = lean_unbox(v___x_4475_);
v_res_4485_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_16840__boxed_4483_, v___x_16841__boxed_4484_, v_as_x27_4476_, v_b_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v_as_x27_4476_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4486_, uint8_t v_isUnsafe_4487_, lean_object* v_ctors_4488_, lean_object* v___x_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4486_, v_isUnsafe_4487_, v_ctors_4488_, v___x_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; 
v_unused_4503_ = lean_ctor_get(v___x_4495_, 0);
lean_dec(v_unused_4503_);
v___x_4497_ = v___x_4495_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_dec(v___x_4495_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4489_);
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4489_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
else
{
return v___x_4495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4504_, lean_object* v_isUnsafe_4505_, lean_object* v_ctors_4506_, lean_object* v___x_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
uint8_t v___y_16885__boxed_4513_; uint8_t v_isUnsafe_boxed_4514_; lean_object* v_res_4515_; 
v___y_16885__boxed_4513_ = lean_unbox(v___y_4504_);
v_isUnsafe_boxed_4514_ = lean_unbox(v_isUnsafe_4505_);
v_res_4515_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_16885__boxed_4513_, v_isUnsafe_boxed_4514_, v_ctors_4506_, v___x_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v_ctors_4506_);
return v_res_4515_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4518_ = l_Lean_stringToMessageData(v___x_4517_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v___x_4525_; lean_object* v_env_4526_; lean_object* v___x_4527_; 
v___x_4525_ = lean_st_ref_get(v___y_4523_);
v_env_4526_ = lean_ctor_get(v___x_4525_, 0);
lean_inc_ref(v_env_4526_);
lean_dec(v___x_4525_);
lean_inc(v_constName_4519_);
v___x_4527_ = l_Lean_isInductiveCore_x3f(v_env_4526_, v_constName_4519_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v___x_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4528_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4529_ = 0;
v___x_4530_ = l_Lean_MessageData_ofConstName(v_constName_4519_, v___x_4529_);
v___x_4531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4528_);
lean_ctor_set(v___x_4531_, 1, v___x_4530_);
v___x_4532_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4531_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
v___x_4534_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4533_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
return v___x_4534_;
}
else
{
lean_object* v_val_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
lean_dec(v_constName_4519_);
v_val_4535_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4527_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_val_4535_);
lean_dec(v___x_4527_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
lean_ctor_set_tag(v___x_4537_, 0);
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_val_4535_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
return v_res_4549_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4550_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4550_);
return v___x_4551_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4552_ = lean_unsigned_to_nat(32u);
v___x_4553_ = lean_mk_empty_array_with_capacity(v___x_4552_);
v___x_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
return v___x_4554_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
size_t v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4555_ = ((size_t)5ULL);
v___x_4556_ = lean_unsigned_to_nat(0u);
v___x_4557_ = lean_unsigned_to_nat(32u);
v___x_4558_ = lean_mk_empty_array_with_capacity(v___x_4557_);
v___x_4559_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4560_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
lean_ctor_set(v___x_4560_, 1, v___x_4558_);
lean_ctor_set(v___x_4560_, 2, v___x_4556_);
lean_ctor_set(v___x_4560_, 3, v___x_4556_);
lean_ctor_set_usize(v___x_4560_, 4, v___x_4555_);
return v___x_4560_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4561_ = lean_box(1);
v___x_4562_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4563_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
lean_ctor_set(v___x_4564_, 1, v___x_4562_);
lean_ctor_set(v___x_4564_, 2, v___x_4561_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
lean_object* v___f_4573_; lean_object* v___x_4574_; lean_object* v_env_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
lean_inc_n(v_declName_4567_, 2);
v___f_4573_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4573_, 0, v_declName_4567_);
v___x_4574_ = lean_st_ref_get(v_a_4571_);
v_env_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc_ref(v_env_4575_);
lean_dec(v___x_4574_);
v___x_4576_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4570_);
v___x_4577_ = l_Lean_Meta_isInductivePredicate(v_declName_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4772_; 
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4580_ = v___x_4577_;
v_isShared_4581_ = v_isSharedCheck_4772_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4577_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4772_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4587_; uint8_t v___x_4588_; lean_object* v___y_4590_; uint8_t v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v_a_4596_; lean_object* v___y_4606_; lean_object* v___y_4607_; uint8_t v___y_4608_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v_a_4612_; lean_object* v___y_4615_; lean_object* v___y_4616_; uint8_t v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v_a_4621_; lean_object* v___y_4624_; uint8_t v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v_a_4630_; lean_object* v___y_4643_; uint8_t v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v_a_4649_; lean_object* v___y_4652_; uint8_t v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v_a_4658_; uint8_t v___y_4661_; lean_object* v___y_4662_; uint8_t v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; uint8_t v___y_4703_; uint8_t v___x_4769_; 
v___x_4587_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_4588_ = 1;
v___x_4769_ = l_Lean_Environment_contains(v_env_4575_, v___x_4587_, v___x_4588_);
if (v___x_4769_ == 0)
{
lean_dec_ref(v___x_4576_);
v___y_4703_ = v___x_4769_;
goto v___jp_4702_;
}
else
{
lean_object* v___x_4770_; uint8_t v___x_4771_; 
v___x_4770_ = l_Lean_Meta_genInjectivity;
v___x_4771_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___x_4576_, v___x_4770_);
lean_dec_ref(v___x_4576_);
v___y_4703_ = v___x_4771_;
goto v___jp_4702_;
}
v___jp_4582_:
{
lean_object* v___x_4583_; lean_object* v___x_4585_; 
v___x_4583_ = lean_box(0);
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 0, v___x_4583_);
v___x_4585_ = v___x_4580_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4583_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
v___jp_4589_:
{
lean_object* v___x_4597_; double v___x_4598_; double v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; 
v___x_4597_ = lean_io_get_num_heartbeats();
v___x_4598_ = lean_float_of_nat(v___y_4592_);
v___x_4599_ = lean_float_of_nat(v___x_4597_);
v___x_4600_ = lean_box_float(v___x_4598_);
v___x_4601_ = lean_box_float(v___x_4599_);
v___x_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4600_);
lean_ctor_set(v___x_4602_, 1, v___x_4601_);
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v_a_4596_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
lean_inc_ref(v___y_4590_);
lean_inc(v___y_4595_);
v___x_4604_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4595_, v___x_4588_, v___y_4590_, v___y_4593_, v___y_4591_, v___y_4594_, v___f_4573_, v___x_4603_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4604_;
}
v___jp_4605_:
{
lean_object* v___x_4613_; 
v___x_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4613_, 0, v_a_4612_);
v___y_4590_ = v___y_4606_;
v___y_4591_ = v___y_4608_;
v___y_4592_ = v___y_4607_;
v___y_4593_ = v___y_4609_;
v___y_4594_ = v___y_4610_;
v___y_4595_ = v___y_4611_;
v_a_4596_ = v___x_4613_;
goto v___jp_4589_;
}
v___jp_4614_:
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v_a_4621_);
v___y_4590_ = v___y_4615_;
v___y_4591_ = v___y_4617_;
v___y_4592_ = v___y_4616_;
v___y_4593_ = v___y_4618_;
v___y_4594_ = v___y_4619_;
v___y_4595_ = v___y_4620_;
v_a_4596_ = v___x_4622_;
goto v___jp_4589_;
}
v___jp_4623_:
{
lean_object* v___x_4631_; double v___x_4632_; double v___x_4633_; double v___x_4634_; double v___x_4635_; double v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4631_ = lean_io_mono_nanos_now();
v___x_4632_ = lean_float_of_nat(v___y_4626_);
v___x_4633_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4634_ = lean_float_div(v___x_4632_, v___x_4633_);
v___x_4635_ = lean_float_of_nat(v___x_4631_);
v___x_4636_ = lean_float_div(v___x_4635_, v___x_4633_);
v___x_4637_ = lean_box_float(v___x_4634_);
v___x_4638_ = lean_box_float(v___x_4636_);
v___x_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4637_);
lean_ctor_set(v___x_4639_, 1, v___x_4638_);
v___x_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4640_, 0, v_a_4630_);
lean_ctor_set(v___x_4640_, 1, v___x_4639_);
lean_inc_ref(v___y_4624_);
lean_inc(v___y_4629_);
v___x_4641_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4629_, v___x_4588_, v___y_4624_, v___y_4627_, v___y_4625_, v___y_4628_, v___f_4573_, v___x_4640_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4641_;
}
v___jp_4642_:
{
lean_object* v___x_4650_; 
v___x_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4650_, 0, v_a_4649_);
v___y_4624_ = v___y_4643_;
v___y_4625_ = v___y_4644_;
v___y_4626_ = v___y_4645_;
v___y_4627_ = v___y_4646_;
v___y_4628_ = v___y_4647_;
v___y_4629_ = v___y_4648_;
v_a_4630_ = v___x_4650_;
goto v___jp_4623_;
}
v___jp_4651_:
{
lean_object* v___x_4659_; 
v___x_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4659_, 0, v_a_4658_);
v___y_4624_ = v___y_4652_;
v___y_4625_ = v___y_4653_;
v___y_4626_ = v___y_4654_;
v___y_4627_ = v___y_4655_;
v___y_4628_ = v___y_4656_;
v___y_4629_ = v___y_4657_;
v_a_4630_ = v___x_4659_;
goto v___jp_4623_;
}
v___jp_4660_:
{
lean_object* v___x_4666_; lean_object* v_a_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; 
v___x_4666_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4571_);
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc(v_a_4667_);
lean_dec_ref(v___x_4666_);
v___x_4668_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4669_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4664_, v___x_4668_);
if (v___x_4669_ == 0)
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = lean_io_mono_nanos_now();
v___x_4671_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; uint8_t v_isUnsafe_4673_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v___x_4671_, 1);
v_isUnsafe_4673_ = lean_ctor_get_uint8(v_a_4672_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4673_ == 0)
{
lean_object* v_ctors_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___f_4680_; lean_object* v___x_4681_; 
v_ctors_4674_ = lean_ctor_get(v_a_4672_, 4);
lean_inc(v_ctors_4674_);
lean_dec(v_a_4672_);
v___x_4675_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4676_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4677_ = lean_box(0);
v___x_4678_ = lean_box(v___y_4661_);
v___x_4679_ = lean_box(v_isUnsafe_4673_);
v___f_4680_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4680_, 0, v___x_4678_);
lean_closure_set(v___f_4680_, 1, v___x_4679_);
lean_closure_set(v___f_4680_, 2, v_ctors_4674_);
lean_closure_set(v___f_4680_, 3, v___x_4677_);
v___x_4681_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4675_, v___x_4676_, v___f_4680_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4681_, 1);
v___y_4643_ = v___y_4662_;
v___y_4644_ = v___y_4663_;
v___y_4645_ = v___x_4670_;
v___y_4646_ = v___y_4664_;
v___y_4647_ = v_a_4667_;
v___y_4648_ = v___y_4665_;
v_a_4649_ = v_a_4682_;
goto v___jp_4642_;
}
else
{
lean_object* v_a_4683_; 
v_a_4683_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4683_);
lean_dec_ref_known(v___x_4681_, 1);
v___y_4652_ = v___y_4662_;
v___y_4653_ = v___y_4663_;
v___y_4654_ = v___x_4670_;
v___y_4655_ = v___y_4664_;
v___y_4656_ = v_a_4667_;
v___y_4657_ = v___y_4665_;
v_a_4658_ = v_a_4683_;
goto v___jp_4651_;
}
}
else
{
lean_object* v___x_4684_; 
lean_dec(v_a_4672_);
v___x_4684_ = lean_box(0);
v___y_4643_ = v___y_4662_;
v___y_4644_ = v___y_4663_;
v___y_4645_ = v___x_4670_;
v___y_4646_ = v___y_4664_;
v___y_4647_ = v_a_4667_;
v___y_4648_ = v___y_4665_;
v_a_4649_ = v___x_4684_;
goto v___jp_4642_;
}
}
else
{
lean_object* v_a_4685_; 
v_a_4685_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4671_, 1);
v___y_4652_ = v___y_4662_;
v___y_4653_ = v___y_4663_;
v___y_4654_ = v___x_4670_;
v___y_4655_ = v___y_4664_;
v___y_4656_ = v_a_4667_;
v___y_4657_ = v___y_4665_;
v_a_4658_ = v_a_4685_;
goto v___jp_4651_;
}
}
else
{
lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4686_ = lean_io_get_num_heartbeats();
v___x_4687_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; uint8_t v_isUnsafe_4689_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref_known(v___x_4687_, 1);
v_isUnsafe_4689_ = lean_ctor_get_uint8(v_a_4688_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4689_ == 0)
{
lean_object* v_ctors_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___f_4696_; lean_object* v___x_4697_; 
v_ctors_4690_ = lean_ctor_get(v_a_4688_, 4);
lean_inc(v_ctors_4690_);
lean_dec(v_a_4688_);
v___x_4691_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4692_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4693_ = lean_box(0);
v___x_4694_ = lean_box(v___y_4661_);
v___x_4695_ = lean_box(v_isUnsafe_4689_);
v___f_4696_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4696_, 0, v___x_4694_);
lean_closure_set(v___f_4696_, 1, v___x_4695_);
lean_closure_set(v___f_4696_, 2, v_ctors_4690_);
lean_closure_set(v___f_4696_, 3, v___x_4693_);
v___x_4697_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4691_, v___x_4692_, v___f_4696_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4698_);
lean_dec_ref_known(v___x_4697_, 1);
v___y_4606_ = v___y_4662_;
v___y_4607_ = v___x_4686_;
v___y_4608_ = v___y_4663_;
v___y_4609_ = v___y_4664_;
v___y_4610_ = v_a_4667_;
v___y_4611_ = v___y_4665_;
v_a_4612_ = v_a_4698_;
goto v___jp_4605_;
}
else
{
lean_object* v_a_4699_; 
v_a_4699_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4699_);
lean_dec_ref_known(v___x_4697_, 1);
v___y_4615_ = v___y_4662_;
v___y_4616_ = v___x_4686_;
v___y_4617_ = v___y_4663_;
v___y_4618_ = v___y_4664_;
v___y_4619_ = v_a_4667_;
v___y_4620_ = v___y_4665_;
v_a_4621_ = v_a_4699_;
goto v___jp_4614_;
}
}
else
{
lean_object* v___x_4700_; 
lean_dec(v_a_4688_);
v___x_4700_ = lean_box(0);
v___y_4606_ = v___y_4662_;
v___y_4607_ = v___x_4686_;
v___y_4608_ = v___y_4663_;
v___y_4609_ = v___y_4664_;
v___y_4610_ = v_a_4667_;
v___y_4611_ = v___y_4665_;
v_a_4612_ = v___x_4700_;
goto v___jp_4605_;
}
}
else
{
lean_object* v_a_4701_; 
v_a_4701_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4687_, 1);
v___y_4615_ = v___y_4662_;
v___y_4616_ = v___x_4686_;
v___y_4617_ = v___y_4663_;
v___y_4618_ = v___y_4664_;
v___y_4619_ = v_a_4667_;
v___y_4620_ = v___y_4665_;
v_a_4621_ = v_a_4701_;
goto v___jp_4614_;
}
}
}
v___jp_4702_:
{
if (v___y_4703_ == 0)
{
lean_dec(v_a_4578_);
lean_dec_ref(v___f_4573_);
lean_dec(v_declName_4567_);
goto v___jp_4582_;
}
else
{
uint8_t v___x_4704_; 
v___x_4704_ = lean_unbox(v_a_4578_);
lean_dec(v_a_4578_);
if (v___x_4704_ == 0)
{
lean_object* v_toCold_4705_; lean_object* v_options_4706_; uint8_t v_hasTrace_4707_; 
lean_del_object(v___x_4580_);
v_toCold_4705_ = lean_ctor_get(v_a_4570_, 0);
v_options_4706_ = lean_ctor_get(v_toCold_4705_, 2);
v_hasTrace_4707_ = lean_ctor_get_uint8(v_options_4706_, sizeof(void*)*1);
if (v_hasTrace_4707_ == 0)
{
lean_object* v___x_4708_; 
lean_dec_ref(v___f_4573_);
v___x_4708_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4726_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4711_ = v___x_4708_;
v_isShared_4712_ = v_isSharedCheck_4726_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4708_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4726_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
uint8_t v_isUnsafe_4713_; 
v_isUnsafe_4713_ = lean_ctor_get_uint8(v_a_4709_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4713_ == 0)
{
lean_object* v_ctors_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___f_4720_; lean_object* v___x_4721_; 
lean_del_object(v___x_4711_);
v_ctors_4714_ = lean_ctor_get(v_a_4709_, 4);
lean_inc(v_ctors_4714_);
lean_dec(v_a_4709_);
v___x_4715_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4716_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4717_ = lean_box(0);
v___x_4718_ = lean_box(v___y_4703_);
v___x_4719_ = lean_box(v_isUnsafe_4713_);
v___f_4720_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4720_, 0, v___x_4718_);
lean_closure_set(v___f_4720_, 1, v___x_4719_);
lean_closure_set(v___f_4720_, 2, v_ctors_4714_);
lean_closure_set(v___f_4720_, 3, v___x_4717_);
v___x_4721_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4715_, v___x_4716_, v___f_4720_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4721_;
}
else
{
lean_object* v___x_4722_; lean_object* v___x_4724_; 
lean_dec(v_a_4709_);
v___x_4722_ = lean_box(0);
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 0, v___x_4722_);
v___x_4724_ = v___x_4711_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4722_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
v_a_4727_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4729_ = v___x_4708_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4708_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; uint8_t v___x_4739_; 
v_inheritedTraceOptions_4735_ = lean_ctor_get(v_toCold_4705_, 11);
v___x_4736_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4737_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4738_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4739_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4735_, v_options_4706_, v___x_4738_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4740_; uint8_t v___x_4741_; 
v___x_4740_ = l_Lean_trace_profiler;
v___x_4741_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4706_, v___x_4740_);
if (v___x_4741_ == 0)
{
lean_object* v___x_4742_; 
lean_dec_ref(v___f_4573_);
v___x_4742_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
if (lean_obj_tag(v___x_4742_) == 0)
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4760_; 
v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4745_ = v___x_4742_;
v_isShared_4746_ = v_isSharedCheck_4760_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4742_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4760_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
uint8_t v_isUnsafe_4747_; 
v_isUnsafe_4747_ = lean_ctor_get_uint8(v_a_4743_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4747_ == 0)
{
lean_object* v_ctors_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___f_4754_; lean_object* v___x_4755_; 
lean_del_object(v___x_4745_);
v_ctors_4748_ = lean_ctor_get(v_a_4743_, 4);
lean_inc(v_ctors_4748_);
lean_dec(v_a_4743_);
v___x_4749_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4750_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4751_ = lean_box(0);
v___x_4752_ = lean_box(v___y_4703_);
v___x_4753_ = lean_box(v_isUnsafe_4747_);
v___f_4754_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4754_, 0, v___x_4752_);
lean_closure_set(v___f_4754_, 1, v___x_4753_);
lean_closure_set(v___f_4754_, 2, v_ctors_4748_);
lean_closure_set(v___f_4754_, 3, v___x_4751_);
v___x_4755_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4749_, v___x_4750_, v___f_4754_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
return v___x_4755_;
}
else
{
lean_object* v___x_4756_; lean_object* v___x_4758_; 
lean_dec(v_a_4743_);
v___x_4756_ = lean_box(0);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 0, v___x_4756_);
v___x_4758_ = v___x_4745_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v___x_4756_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
v_a_4761_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4742_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4742_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
else
{
v___y_4661_ = v___y_4703_;
v___y_4662_ = v___x_4737_;
v___y_4663_ = v___x_4739_;
v___y_4664_ = v_options_4706_;
v___y_4665_ = v___x_4736_;
goto v___jp_4660_;
}
}
else
{
v___y_4661_ = v___y_4703_;
v___y_4662_ = v___x_4737_;
v___y_4663_ = v___x_4739_;
v___y_4664_ = v_options_4706_;
v___y_4665_ = v___x_4736_;
goto v___jp_4660_;
}
}
}
else
{
lean_dec_ref(v___f_4573_);
lean_dec(v_declName_4567_);
goto v___jp_4582_;
}
}
}
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4780_; 
lean_dec_ref(v___x_4576_);
lean_dec_ref(v_env_4575_);
lean_dec_ref(v___f_4573_);
lean_dec(v_declName_4567_);
v_a_4773_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4775_ = v___x_4577_;
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4577_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
lean_dec(v_a_4785_);
lean_dec_ref(v_a_4784_);
lean_dec(v_a_4783_);
lean_dec_ref(v_a_4782_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4788_, uint8_t v___x_4789_, lean_object* v_as_4790_, lean_object* v_as_x27_4791_, lean_object* v_b_4792_, lean_object* v_a_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4788_, v___x_4789_, v_as_x27_4791_, v_b_4792_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4800_, lean_object* v___x_4801_, lean_object* v_as_4802_, lean_object* v_as_x27_4803_, lean_object* v_b_4804_, lean_object* v_a_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
uint8_t v___y_17512__boxed_4811_; uint8_t v___x_17513__boxed_4812_; lean_object* v_res_4813_; 
v___y_17512__boxed_4811_ = lean_unbox(v___y_4800_);
v___x_17513__boxed_4812_ = lean_unbox(v___x_4801_);
v_res_4813_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_17512__boxed_4811_, v___x_17513__boxed_4812_, v_as_4802_, v_as_x27_4803_, v_b_4804_, v_a_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_);
lean_dec(v___y_4809_);
lean_dec_ref(v___y_4808_);
lean_dec(v___y_4807_);
lean_dec_ref(v___y_4806_);
lean_dec(v_as_x27_4803_);
lean_dec(v_as_4802_);
return v_res_4813_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4854_ = lean_unsigned_to_nat(4172903888u);
v___x_4855_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4856_ = l_Lean_Name_num___override(v___x_4855_, v___x_4854_);
return v___x_4856_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4858_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4859_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4860_ = l_Lean_Name_str___override(v___x_4859_, v___x_4858_);
return v___x_4860_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4862_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4863_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4864_ = l_Lean_Name_str___override(v___x_4863_, v___x_4862_);
return v___x_4864_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4865_ = lean_unsigned_to_nat(2u);
v___x_4866_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4867_ = l_Lean_Name_num___override(v___x_4866_, v___x_4865_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4869_; uint8_t v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4869_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4870_ = 0;
v___x_4871_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4872_ = l_Lean_registerTraceClass(v___x_4869_, v___x_4870_, v___x_4871_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4875_, lean_object* v_b_4876_){
_start:
{
lean_object* v_array_4877_; lean_object* v_start_4878_; lean_object* v_stop_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4892_; 
v_array_4877_ = lean_ctor_get(v_a_4875_, 0);
v_start_4878_ = lean_ctor_get(v_a_4875_, 1);
v_stop_4879_ = lean_ctor_get(v_a_4875_, 2);
v_isSharedCheck_4892_ = !lean_is_exclusive(v_a_4875_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4881_ = v_a_4875_;
v_isShared_4882_ = v_isSharedCheck_4892_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_stop_4879_);
lean_inc(v_start_4878_);
lean_inc(v_array_4877_);
lean_dec(v_a_4875_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4892_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
uint8_t v___x_4883_; 
v___x_4883_ = lean_nat_dec_lt(v_start_4878_, v_stop_4879_);
if (v___x_4883_ == 0)
{
lean_del_object(v___x_4881_);
lean_dec(v_stop_4879_);
lean_dec(v_start_4878_);
lean_dec_ref(v_array_4877_);
return v_b_4876_;
}
else
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4884_ = lean_unsigned_to_nat(1u);
v___x_4885_ = lean_nat_add(v_start_4878_, v___x_4884_);
lean_inc_ref(v_array_4877_);
if (v_isShared_4882_ == 0)
{
lean_ctor_set(v___x_4881_, 1, v___x_4885_);
v___x_4887_ = v___x_4881_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_array_4877_);
lean_ctor_set(v_reuseFailAlloc_4891_, 1, v___x_4885_);
lean_ctor_set(v_reuseFailAlloc_4891_, 2, v_stop_4879_);
v___x_4887_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4888_ = lean_array_fget(v_array_4877_, v_start_4878_);
lean_dec(v_start_4878_);
lean_dec_ref(v_array_4877_);
v___x_4889_ = lean_array_push(v_b_4876_, v___x_4888_);
v_a_4875_ = v___x_4887_;
v_b_4876_ = v___x_4889_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4893_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4893_);
return v___x_4894_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4895_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4896_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4897_ = lean_unsigned_to_nat(0u);
v___x_4898_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4897_);
lean_ctor_set(v___x_4898_, 1, v___x_4897_);
lean_ctor_set(v___x_4898_, 2, v___x_4897_);
lean_ctor_set(v___x_4898_, 3, v___x_4897_);
lean_ctor_set(v___x_4898_, 4, v___x_4896_);
lean_ctor_set(v___x_4898_, 5, v___x_4896_);
lean_ctor_set(v___x_4898_, 6, v___x_4896_);
lean_ctor_set(v___x_4898_, 7, v___x_4896_);
lean_ctor_set(v___x_4898_, 8, v___x_4896_);
lean_ctor_set(v___x_4898_, 9, v___x_4896_);
lean_ctor_set(v___x_4898_, 10, v___x_4896_);
lean_ctor_set(v___x_4898_, 11, v___x_4895_);
return v___x_4898_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4899_ = lean_box(1);
v___x_4900_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4901_);
lean_ctor_set(v___x_4902_, 1, v___x_4900_);
lean_ctor_set(v___x_4902_, 2, v___x_4899_);
return v___x_4902_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4904_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3));
v___x_4905_ = l_Lean_stringToMessageData(v___x_4904_);
return v___x_4905_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4907_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5));
v___x_4908_ = l_Lean_stringToMessageData(v___x_4907_);
return v___x_4908_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
v___x_4910_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7));
v___x_4911_ = l_Lean_stringToMessageData(v___x_4910_);
return v___x_4911_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10(void){
_start:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; 
v___x_4913_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9));
v___x_4914_ = l_Lean_stringToMessageData(v___x_4913_);
return v___x_4914_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12(void){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4916_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11));
v___x_4917_ = l_Lean_stringToMessageData(v___x_4916_);
return v___x_4917_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14(void){
_start:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4919_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13));
v___x_4920_ = l_Lean_stringToMessageData(v___x_4919_);
return v___x_4920_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16(void){
_start:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4922_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15));
v___x_4923_ = l_Lean_stringToMessageData(v___x_4922_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4924_, lean_object* v_declHint_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v_env_4930_; uint8_t v___x_4931_; 
v___x_4928_ = lean_box(0);
v___x_4929_ = lean_st_ref_get(v___y_4926_);
v_env_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc_ref(v_env_4930_);
lean_dec(v___x_4929_);
v___x_4931_ = l_Lean_Name_isAnonymous(v_declHint_4925_);
if (v___x_4931_ == 0)
{
uint8_t v_isExporting_4932_; 
v_isExporting_4932_ = lean_ctor_get_uint8(v_env_4930_, sizeof(void*)*13);
if (v_isExporting_4932_ == 0)
{
lean_object* v___x_4933_; 
lean_dec_ref(v_env_4930_);
lean_dec(v_declHint_4925_);
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v_msg_4924_);
return v___x_4933_;
}
else
{
lean_object* v___x_4934_; uint8_t v___x_4935_; 
lean_inc_ref(v_env_4930_);
v___x_4934_ = l_Lean_Environment_setExporting(v_env_4930_, v___x_4931_);
lean_inc(v_declHint_4925_);
lean_inc_ref(v___x_4934_);
v___x_4935_ = l_Lean_Environment_contains(v___x_4934_, v_declHint_4925_, v_isExporting_4932_);
if (v___x_4935_ == 0)
{
lean_object* v___x_4936_; 
lean_dec_ref(v___x_4934_);
lean_dec_ref(v_env_4930_);
lean_dec(v_declHint_4925_);
v___x_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4936_, 0, v_msg_4924_);
return v___x_4936_;
}
else
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v_c_4942_; lean_object* v___x_4943_; 
v___x_4937_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4938_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4939_ = l_Lean_Options_empty;
v___x_4940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4934_);
lean_ctor_set(v___x_4940_, 1, v___x_4937_);
lean_ctor_set(v___x_4940_, 2, v___x_4938_);
lean_ctor_set(v___x_4940_, 3, v___x_4939_);
lean_inc(v_declHint_4925_);
v___x_4941_ = l_Lean_MessageData_ofConstName(v_declHint_4925_, v___x_4931_);
v_c_4942_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4942_, 0, v___x_4940_);
lean_ctor_set(v_c_4942_, 1, v___x_4941_);
v___x_4943_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4930_, v_declHint_4925_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
lean_dec_ref(v_env_4930_);
lean_dec(v_declHint_4925_);
v___x_4944_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4944_);
lean_ctor_set(v___x_4945_, 1, v_c_4942_);
v___x_4946_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_4947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4945_);
lean_ctor_set(v___x_4947_, 1, v___x_4946_);
v___x_4948_ = l_Lean_MessageData_note(v___x_4947_);
v___x_4949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4949_, 0, v_msg_4924_);
lean_ctor_set(v___x_4949_, 1, v___x_4948_);
v___x_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4949_);
return v___x_4950_;
}
else
{
lean_object* v_val_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4985_; 
v_val_4951_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4953_ = v___x_4943_;
v_isShared_4954_ = v_isSharedCheck_4985_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_val_4951_);
lean_dec(v___x_4943_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4985_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v_mod_4957_; uint8_t v___x_4958_; 
v___x_4955_ = l_Lean_Environment_header(v_env_4930_);
lean_dec_ref(v_env_4930_);
v___x_4956_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4955_);
v_mod_4957_ = lean_array_get(v___x_4928_, v___x_4956_, v_val_4951_);
lean_dec(v_val_4951_);
lean_dec_ref(v___x_4956_);
v___x_4958_ = l_Lean_isPrivateName(v_declHint_4925_);
lean_dec(v_declHint_4925_);
if (v___x_4958_ == 0)
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4970_; 
v___x_4959_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8);
v___x_4960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4959_);
lean_ctor_set(v___x_4960_, 1, v_c_4942_);
v___x_4961_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10);
v___x_4962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4960_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = l_Lean_MessageData_ofName(v_mod_4957_);
v___x_4964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4964_, 0, v___x_4962_);
lean_ctor_set(v___x_4964_, 1, v___x_4963_);
v___x_4965_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12);
v___x_4966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4964_);
lean_ctor_set(v___x_4966_, 1, v___x_4965_);
v___x_4967_ = l_Lean_MessageData_note(v___x_4966_);
v___x_4968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4968_, 0, v_msg_4924_);
lean_ctor_set(v___x_4968_, 1, v___x_4967_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set_tag(v___x_4953_, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4968_);
v___x_4970_ = v___x_4953_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4968_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
else
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4983_; 
v___x_4972_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4972_);
lean_ctor_set(v___x_4973_, 1, v_c_4942_);
v___x_4974_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14);
v___x_4975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4973_);
lean_ctor_set(v___x_4975_, 1, v___x_4974_);
v___x_4976_ = l_Lean_MessageData_ofName(v_mod_4957_);
v___x_4977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4975_);
lean_ctor_set(v___x_4977_, 1, v___x_4976_);
v___x_4978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16);
v___x_4979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4977_);
lean_ctor_set(v___x_4979_, 1, v___x_4978_);
v___x_4980_ = l_Lean_MessageData_note(v___x_4979_);
v___x_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4981_, 0, v_msg_4924_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set_tag(v___x_4953_, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4981_);
v___x_4983_ = v___x_4953_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v___x_4981_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4986_; 
lean_dec_ref(v_env_4930_);
lean_dec(v_declHint_4925_);
v___x_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4986_, 0, v_msg_4924_);
return v___x_4986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_4987_, lean_object* v_declHint_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4987_, v_declHint_4988_, v___y_4989_);
lean_dec(v___y_4989_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_4992_, lean_object* v_declHint_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v___x_4999_; lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5009_; 
v___x_4999_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4992_, v_declHint_4993_, v___y_4997_);
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5002_ = v___x_4999_;
v_isShared_5003_ = v_isSharedCheck_5009_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4999_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5009_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5007_; 
v___x_5004_ = l_Lean_unknownIdentifierMessageTag;
v___x_5005_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5004_);
lean_ctor_set(v___x_5005_, 1, v_a_5000_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 0, v___x_5005_);
v___x_5007_ = v___x_5002_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v___x_5005_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5010_, lean_object* v_declHint_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5010_, v_declHint_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec(v___y_5013_);
lean_dec_ref(v___y_5012_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5018_, lean_object* v_msg_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
lean_object* v_toCold_5025_; lean_object* v_currRecDepth_5026_; lean_object* v_ref_5027_; uint16_t v_optionFlags_5028_; uint8_t v_suppressElabErrors_5029_; uint8_t v_isRecordingDeps_5030_; lean_object* v_ref_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v_toCold_5025_ = lean_ctor_get(v___y_5022_, 0);
v_currRecDepth_5026_ = lean_ctor_get(v___y_5022_, 1);
v_ref_5027_ = lean_ctor_get(v___y_5022_, 2);
v_optionFlags_5028_ = lean_ctor_get_uint16(v___y_5022_, sizeof(void*)*3);
v_suppressElabErrors_5029_ = lean_ctor_get_uint8(v___y_5022_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5030_ = lean_ctor_get_uint8(v___y_5022_, sizeof(void*)*3 + 3);
v_ref_5031_ = l_Lean_replaceRef(v_ref_5018_, v_ref_5027_);
lean_inc(v_currRecDepth_5026_);
lean_inc_ref(v_toCold_5025_);
v___x_5032_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5032_, 0, v_toCold_5025_);
lean_ctor_set(v___x_5032_, 1, v_currRecDepth_5026_);
lean_ctor_set(v___x_5032_, 2, v_ref_5031_);
lean_ctor_set_uint16(v___x_5032_, sizeof(void*)*3, v_optionFlags_5028_);
lean_ctor_set_uint8(v___x_5032_, sizeof(void*)*3 + 2, v_suppressElabErrors_5029_);
lean_ctor_set_uint8(v___x_5032_, sizeof(void*)*3 + 3, v_isRecordingDeps_5030_);
v___x_5033_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5019_, v___y_5020_, v___y_5021_, v___x_5032_, v___y_5023_);
lean_dec_ref_known(v___x_5032_, 3);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5034_, lean_object* v_msg_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5034_, v_msg_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
lean_dec(v___y_5039_);
lean_dec_ref(v___y_5038_);
lean_dec(v___y_5037_);
lean_dec_ref(v___y_5036_);
lean_dec(v_ref_5034_);
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5042_, lean_object* v_msg_5043_, lean_object* v_declHint_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_){
_start:
{
lean_object* v___x_5050_; lean_object* v_a_5051_; lean_object* v___x_5052_; 
v___x_5050_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5043_, v_declHint_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_a_5051_);
lean_dec_ref(v___x_5050_);
v___x_5052_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5042_, v_a_5051_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5053_, lean_object* v_msg_5054_, lean_object* v_declHint_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5053_, v_msg_5054_, v_declHint_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
lean_dec(v___y_5057_);
lean_dec_ref(v___y_5056_);
lean_dec(v_ref_5053_);
return v_res_5061_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5064_ = l_Lean_stringToMessageData(v___x_5063_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5065_, lean_object* v_constName_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_){
_start:
{
lean_object* v___x_5072_; uint8_t v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5072_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5073_ = 0;
lean_inc(v_constName_5066_);
v___x_5074_ = l_Lean_MessageData_ofConstName(v_constName_5066_, v___x_5073_);
v___x_5075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5075_, 0, v___x_5072_);
lean_ctor_set(v___x_5075_, 1, v___x_5074_);
v___x_5076_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5075_);
lean_ctor_set(v___x_5077_, 1, v___x_5076_);
v___x_5078_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5065_, v___x_5077_, v_constName_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5079_, lean_object* v_constName_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5079_, v_constName_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
lean_dec(v_ref_5079_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_){
_start:
{
lean_object* v_ref_5093_; lean_object* v___x_5094_; 
v_ref_5093_ = lean_ctor_get(v___y_5090_, 2);
v___x_5094_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5093_, v_constName_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_);
lean_dec(v___y_5099_);
lean_dec_ref(v___y_5098_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_){
_start:
{
lean_object* v___x_5108_; lean_object* v_env_5109_; uint8_t v___x_5110_; lean_object* v___x_5111_; 
v___x_5108_ = lean_st_ref_get(v___y_5106_);
v_env_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc_ref(v_env_5109_);
lean_dec(v___x_5108_);
v___x_5110_ = 0;
lean_inc(v_constName_5102_);
v___x_5111_ = l_Lean_Environment_find_x3f(v_env_5109_, v_constName_5102_, v___x_5110_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v___x_5112_; 
v___x_5112_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
return v___x_5112_;
}
else
{
lean_object* v_val_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
lean_dec(v_constName_5102_);
v_val_5113_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5111_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_val_5113_);
lean_dec(v___x_5111_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
lean_ctor_set_tag(v___x_5115_, 0);
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_val_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
lean_object* v_res_5127_; 
v_res_5127_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
lean_dec(v___y_5125_);
lean_dec_ref(v___y_5124_);
lean_dec(v___y_5123_);
lean_dec_ref(v___y_5122_);
return v_res_5127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5130_, lean_object* v_x_5131_, lean_object* v_x_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
if (lean_obj_tag(v_x_5130_) == 5)
{
lean_object* v_fn_5138_; lean_object* v_arg_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; 
v_fn_5138_ = lean_ctor_get(v_x_5130_, 0);
lean_inc_ref(v_fn_5138_);
v_arg_5139_ = lean_ctor_get(v_x_5130_, 1);
lean_inc_ref(v_arg_5139_);
lean_dec_ref_known(v_x_5130_, 2);
v___x_5140_ = lean_array_set(v_x_5131_, v_x_5132_, v_arg_5139_);
v___x_5141_ = lean_unsigned_to_nat(1u);
v___x_5142_ = lean_nat_sub(v_x_5132_, v___x_5141_);
lean_dec(v_x_5132_);
v_x_5130_ = v_fn_5138_;
v_x_5131_ = v___x_5140_;
v_x_5132_ = v___x_5142_;
goto _start;
}
else
{
lean_dec(v_x_5132_);
if (lean_obj_tag(v_x_5130_) == 4)
{
lean_object* v_declName_5144_; lean_object* v___x_5145_; 
v_declName_5144_ = lean_ctor_get(v_x_5130_, 0);
lean_inc(v_declName_5144_);
lean_dec_ref_known(v_x_5130_, 2);
v___x_5145_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5144_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5177_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5148_ = v___x_5145_;
v_isShared_5149_ = v_isSharedCheck_5177_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5145_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5177_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v_lower_5151_; lean_object* v_upper_5152_; 
if (lean_obj_tag(v_a_5146_) == 5)
{
lean_object* v_val_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5174_; 
v_val_5160_ = lean_ctor_get(v_a_5146_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v_a_5146_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5162_ = v_a_5146_;
v_isShared_5163_ = v_isSharedCheck_5174_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_val_5160_);
lean_dec(v_a_5146_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5174_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v_numParams_5164_; lean_object* v_numIndices_5165_; lean_object* v___x_5166_; uint8_t v___x_5167_; 
v_numParams_5164_ = lean_ctor_get(v_val_5160_, 1);
lean_inc(v_numParams_5164_);
v_numIndices_5165_ = lean_ctor_get(v_val_5160_, 2);
lean_inc(v_numIndices_5165_);
lean_dec_ref(v_val_5160_);
v___x_5166_ = lean_unsigned_to_nat(0u);
v___x_5167_ = lean_nat_dec_eq(v_numIndices_5165_, v___x_5166_);
lean_dec(v_numIndices_5165_);
if (v___x_5167_ == 0)
{
lean_object* v___x_5168_; uint8_t v___x_5169_; 
lean_del_object(v___x_5162_);
v___x_5168_ = lean_array_get_size(v_x_5131_);
v___x_5169_ = lean_nat_dec_le(v_numParams_5164_, v___x_5166_);
if (v___x_5169_ == 0)
{
v_lower_5151_ = v_numParams_5164_;
v_upper_5152_ = v___x_5168_;
goto v___jp_5150_;
}
else
{
lean_dec(v_numParams_5164_);
v_lower_5151_ = v___x_5166_;
v_upper_5152_ = v___x_5168_;
goto v___jp_5150_;
}
}
else
{
lean_object* v___x_5170_; lean_object* v___x_5172_; 
lean_dec(v_numParams_5164_);
lean_del_object(v___x_5148_);
lean_dec_ref(v_x_5131_);
v___x_5170_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5163_ == 0)
{
lean_ctor_set_tag(v___x_5162_, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5170_);
v___x_5172_ = v___x_5162_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5170_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
}
else
{
lean_object* v___x_5175_; lean_object* v___x_5176_; 
lean_del_object(v___x_5148_);
lean_dec(v_a_5146_);
lean_dec_ref(v_x_5131_);
v___x_5175_ = lean_box(0);
v___x_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5175_);
return v___x_5176_;
}
v___jp_5150_:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5158_; 
v___x_5153_ = l_Array_toSubarray___redArg(v_x_5131_, v_lower_5151_, v_upper_5152_);
v___x_5154_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5155_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5153_, v___x_5154_);
v___x_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5156_, 0, v___x_5155_);
if (v_isShared_5149_ == 0)
{
lean_ctor_set(v___x_5148_, 0, v___x_5156_);
v___x_5158_ = v___x_5148_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5156_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
}
else
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
lean_dec_ref(v_x_5131_);
v_a_5178_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5180_ = v___x_5145_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5145_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
}
else
{
lean_object* v___x_5186_; lean_object* v___x_5187_; 
lean_dec_ref(v_x_5131_);
lean_dec_ref(v_x_5130_);
v___x_5186_ = lean_box(0);
v___x_5187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5186_);
return v___x_5187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5188_, lean_object* v_x_5189_, lean_object* v_x_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_){
_start:
{
lean_object* v_res_5196_; 
v_res_5196_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5188_, v_x_5189_, v_x_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
lean_dec(v___y_5194_);
lean_dec_ref(v___y_5193_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_){
_start:
{
lean_object* v___x_5203_; 
lean_inc(v_a_5201_);
lean_inc_ref(v_a_5200_);
lean_inc(v_a_5199_);
lean_inc_ref(v_a_5198_);
v___x_5203_ = lean_infer_type(v_ctorApp_5197_, v_a_5198_, v_a_5199_, v_a_5200_, v_a_5201_);
if (lean_obj_tag(v___x_5203_) == 0)
{
lean_object* v_a_5204_; lean_object* v___x_5205_; 
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
lean_inc(v_a_5204_);
lean_dec_ref_known(v___x_5203_, 1);
v___x_5205_ = l_Lean_Meta_whnfD(v_a_5204_, v_a_5198_, v_a_5199_, v_a_5200_, v_a_5201_);
if (lean_obj_tag(v___x_5205_) == 0)
{
lean_object* v_a_5206_; lean_object* v_dummy_5207_; lean_object* v_nargs_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v_a_5206_ = lean_ctor_get(v___x_5205_, 0);
lean_inc(v_a_5206_);
lean_dec_ref_known(v___x_5205_, 1);
v_dummy_5207_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5208_ = l_Lean_Expr_getAppNumArgs(v_a_5206_);
lean_inc(v_nargs_5208_);
v___x_5209_ = lean_mk_array(v_nargs_5208_, v_dummy_5207_);
v___x_5210_ = lean_unsigned_to_nat(1u);
v___x_5211_ = lean_nat_sub(v_nargs_5208_, v___x_5210_);
lean_dec(v_nargs_5208_);
v___x_5212_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5206_, v___x_5209_, v___x_5211_, v_a_5198_, v_a_5199_, v_a_5200_, v_a_5201_);
return v___x_5212_;
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
v_a_5213_ = lean_ctor_get(v___x_5205_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5205_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5205_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5205_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
v_a_5221_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5203_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5203_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5229_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_);
lean_dec(v_a_5233_);
lean_dec_ref(v_a_5232_);
lean_dec(v_a_5231_);
lean_dec_ref(v_a_5230_);
return v_res_5235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5236_, lean_object* v_R_5237_, lean_object* v_a_5238_, lean_object* v_b_5239_){
_start:
{
lean_object* v___x_5240_; 
v___x_5240_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5238_, v_b_5239_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5241_, lean_object* v_constName_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_){
_start:
{
lean_object* v___x_5248_; 
v___x_5248_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_);
return v___x_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5249_, lean_object* v_constName_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_){
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5249_, v_constName_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5257_, lean_object* v_ref_5258_, lean_object* v_constName_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_){
_start:
{
lean_object* v___x_5265_; 
v___x_5265_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5258_, v_constName_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_);
return v___x_5265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5266_, lean_object* v_ref_5267_, lean_object* v_constName_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
lean_object* v_res_5274_; 
v_res_5274_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5266_, v_ref_5267_, v_constName_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v_ref_5267_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5275_, lean_object* v_ref_5276_, lean_object* v_msg_5277_, lean_object* v_declHint_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v___x_5284_; 
v___x_5284_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5276_, v_msg_5277_, v_declHint_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5285_, lean_object* v_ref_5286_, lean_object* v_msg_5287_, lean_object* v_declHint_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5285_, v_ref_5286_, v_msg_5287_, v_declHint_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v_ref_5286_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5295_, lean_object* v_declHint_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v___x_5302_; 
v___x_5302_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5295_, v_declHint_5296_, v___y_5300_);
return v___x_5302_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5303_, lean_object* v_declHint_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5303_, v_declHint_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5311_, lean_object* v_ref_5312_, lean_object* v_msg_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_){
_start:
{
lean_object* v___x_5319_; 
v___x_5319_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5312_, v_msg_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
return v___x_5319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5320_, lean_object* v_ref_5321_, lean_object* v_msg_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5320_, v_ref_5321_, v_msg_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v_ref_5321_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5329_, lean_object* v_body_5330_, lean_object* v_args2_5331_, lean_object* v_ctorVal_5332_, lean_object* v_args1_5333_, lean_object* v_k_5334_, lean_object* v_arg2_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_){
_start:
{
lean_object* v_res_5341_; 
v_res_5341_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5329_, v_body_5330_, v_args2_5331_, v_ctorVal_5332_, v_args1_5333_, v_k_5334_, v_arg2_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec_ref(v_body_5330_);
lean_dec(v_i_5329_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5342_, lean_object* v_args1_5343_, lean_object* v_k_5344_, lean_object* v_i_5345_, lean_object* v_type_5346_, lean_object* v_args2_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_){
_start:
{
lean_object* v___x_5353_; uint8_t v___x_5354_; 
v___x_5353_ = lean_array_get_size(v_args1_5343_);
v___x_5354_ = lean_nat_dec_lt(v_i_5345_, v___x_5353_);
if (v___x_5354_ == 0)
{
lean_object* v___x_5355_; 
lean_dec_ref(v_type_5346_);
lean_dec(v_i_5345_);
lean_dec_ref(v_args1_5343_);
lean_dec_ref(v_ctorVal_5342_);
lean_inc(v_a_5351_);
lean_inc_ref(v_a_5350_);
lean_inc(v_a_5349_);
lean_inc_ref(v_a_5348_);
v___x_5355_ = lean_apply_6(v_k_5344_, v_args2_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, lean_box(0));
return v___x_5355_;
}
else
{
lean_object* v___x_5356_; 
lean_inc(v_a_5351_);
lean_inc_ref(v_a_5350_);
lean_inc(v_a_5349_);
lean_inc_ref(v_a_5348_);
v___x_5356_ = lean_whnf(v_type_5346_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref_known(v___x_5356_, 1);
if (lean_obj_tag(v_a_5357_) == 7)
{
lean_object* v_binderName_5358_; lean_object* v_binderType_5359_; lean_object* v_body_5360_; lean_object* v___f_5361_; uint8_t v___x_5362_; uint8_t v___x_5363_; lean_object* v___x_5364_; 
v_binderName_5358_ = lean_ctor_get(v_a_5357_, 0);
lean_inc(v_binderName_5358_);
v_binderType_5359_ = lean_ctor_get(v_a_5357_, 1);
lean_inc_ref(v_binderType_5359_);
v_body_5360_ = lean_ctor_get(v_a_5357_, 2);
lean_inc_ref(v_body_5360_);
lean_dec_ref_known(v_a_5357_, 3);
v___f_5361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5361_, 0, v_i_5345_);
lean_closure_set(v___f_5361_, 1, v_body_5360_);
lean_closure_set(v___f_5361_, 2, v_args2_5347_);
lean_closure_set(v___f_5361_, 3, v_ctorVal_5342_);
lean_closure_set(v___f_5361_, 4, v_args1_5343_);
lean_closure_set(v___f_5361_, 5, v_k_5344_);
v___x_5362_ = 1;
v___x_5363_ = 0;
v___x_5364_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5358_, v___x_5362_, v_binderType_5359_, v___f_5361_, v___x_5363_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_);
return v___x_5364_;
}
else
{
lean_object* v_toConstantVal_5365_; lean_object* v_name_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; 
lean_dec(v_a_5357_);
lean_dec_ref(v_args2_5347_);
lean_dec(v_i_5345_);
lean_dec_ref(v_k_5344_);
lean_dec_ref(v_args1_5343_);
v_toConstantVal_5365_ = lean_ctor_get(v_ctorVal_5342_, 0);
lean_inc_ref(v_toConstantVal_5365_);
lean_dec_ref(v_ctorVal_5342_);
v_name_5366_ = lean_ctor_get(v_toConstantVal_5365_, 0);
lean_inc(v_name_5366_);
lean_dec_ref(v_toConstantVal_5365_);
v___x_5367_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5368_ = l_Lean_MessageData_ofName(v_name_5366_);
v___x_5369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5369_, 0, v___x_5367_);
lean_ctor_set(v___x_5369_, 1, v___x_5368_);
v___x_5370_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5371_, 0, v___x_5369_);
lean_ctor_set(v___x_5371_, 1, v___x_5370_);
v___x_5372_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5371_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_);
return v___x_5372_;
}
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
lean_dec_ref(v_args2_5347_);
lean_dec(v_i_5345_);
lean_dec_ref(v_k_5344_);
lean_dec_ref(v_args1_5343_);
lean_dec_ref(v_ctorVal_5342_);
v_a_5373_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5375_ = v___x_5356_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5356_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5381_, lean_object* v_body_5382_, lean_object* v_args2_5383_, lean_object* v_ctorVal_5384_, lean_object* v_args1_5385_, lean_object* v_k_5386_, lean_object* v_arg2_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_){
_start:
{
lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5393_ = lean_unsigned_to_nat(1u);
v___x_5394_ = lean_nat_add(v_i_5381_, v___x_5393_);
v___x_5395_ = lean_expr_instantiate1(v_body_5382_, v_arg2_5387_);
v___x_5396_ = lean_array_push(v_args2_5383_, v_arg2_5387_);
v___x_5397_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5384_, v_args1_5385_, v_k_5386_, v___x_5394_, v___x_5395_, v___x_5396_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5398_, lean_object* v_args1_5399_, lean_object* v_k_5400_, lean_object* v_i_5401_, lean_object* v_type_5402_, lean_object* v_args2_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_){
_start:
{
lean_object* v_res_5409_; 
v_res_5409_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5398_, v_args1_5399_, v_k_5400_, v_i_5401_, v_type_5402_, v_args2_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_);
lean_dec(v_a_5407_);
lean_dec_ref(v_a_5406_);
lean_dec(v_a_5405_);
lean_dec_ref(v_a_5404_);
return v_res_5409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v___x_5410_, lean_object* v_numParams_5411_, lean_object* v_name_5412_, lean_object* v_us_5413_, lean_object* v_args1_5414_, lean_object* v___x_5415_, lean_object* v_args2_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_){
_start:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
lean_inc_ref(v_args2_5416_);
v___x_5422_ = l_Array_toSubarray___redArg(v_args2_5416_, v___x_5410_, v_numParams_5411_);
lean_inc(v_us_5413_);
v___x_5423_ = l_Lean_mkConst(v_name_5412_, v_us_5413_);
lean_inc_ref(v___x_5423_);
v___x_5424_ = l_Lean_mkAppN(v___x_5423_, v_args1_5414_);
v___x_5425_ = l_Lean_mkAppN(v___x_5423_, v_args2_5416_);
lean_inc_ref(v___x_5425_);
lean_inc_ref(v___x_5424_);
v___x_5426_ = l_Lean_Meta_mkEqHEq(v___x_5424_, v___x_5425_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_object* v_a_5427_; uint8_t v___x_5428_; lean_object* v___x_5429_; 
v_a_5427_ = lean_ctor_get(v___x_5426_, 0);
lean_inc(v_a_5427_);
lean_dec_ref_known(v___x_5426_, 1);
v___x_5428_ = 1;
lean_inc_ref(v_args2_5416_);
v___x_5429_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5414_, v_args2_5416_, v___x_5428_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5550_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5432_ = v___x_5429_;
v_isShared_5433_ = v_isSharedCheck_5550_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5429_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5550_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5434_; 
v___x_5434_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5430_);
if (lean_obj_tag(v___x_5434_) == 1)
{
lean_object* v_val_5435_; lean_object* v___x_5436_; 
lean_del_object(v___x_5432_);
v_val_5435_ = lean_ctor_get(v___x_5434_, 0);
lean_inc(v_val_5435_);
lean_dec_ref_known(v___x_5434_, 1);
v___x_5436_ = l_Lean_mkArrow(v_a_5427_, v_val_5435_, v___y_5419_, v___y_5420_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5438_; 
v_a_5437_ = lean_ctor_get(v___x_5436_, 0);
lean_inc(v_a_5437_);
lean_dec_ref_known(v___x_5436_, 1);
v___x_5438_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5424_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5529_; 
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5441_ = v___x_5438_;
v_isShared_5442_ = v_isSharedCheck_5529_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5438_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5529_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
if (lean_obj_tag(v_a_5439_) == 1)
{
lean_object* v_val_5443_; lean_object* v___x_5444_; 
lean_del_object(v___x_5441_);
v_val_5443_ = lean_ctor_get(v_a_5439_, 0);
lean_inc(v_val_5443_);
lean_dec_ref_known(v_a_5439_, 1);
v___x_5444_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5425_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5516_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5447_ = v___x_5444_;
v_isShared_5448_ = v_isSharedCheck_5516_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5444_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5516_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
if (lean_obj_tag(v_a_5445_) == 1)
{
lean_object* v_val_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5511_; 
lean_del_object(v___x_5447_);
v_val_5449_ = lean_ctor_get(v_a_5445_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v_a_5445_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5451_ = v_a_5445_;
v_isShared_5452_ = v_isSharedCheck_5511_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_val_5449_);
lean_dec(v_a_5445_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5511_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; uint8_t v___x_5457_; lean_object* v___x_5458_; 
v___x_5453_ = l_Subarray_copy___redArg(v___x_5415_);
v___x_5454_ = l_Array_append___redArg(v___x_5453_, v_val_5443_);
v___x_5455_ = l_Subarray_copy___redArg(v___x_5422_);
v___x_5456_ = l_Array_append___redArg(v___x_5455_, v_val_5449_);
lean_dec(v_val_5449_);
v___x_5457_ = 0;
v___x_5458_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5454_, v___x_5456_, v___x_5457_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
lean_dec_ref(v___x_5454_);
if (lean_obj_tag(v___x_5458_) == 0)
{
lean_object* v_a_5459_; lean_object* v___x_5460_; 
v_a_5459_ = lean_ctor_get(v___x_5458_, 0);
lean_inc(v_a_5459_);
lean_dec_ref_known(v___x_5458_, 1);
v___x_5460_ = l_Lean_mkArrowN(v_a_5459_, v_a_5437_, v___y_5419_, v___y_5420_);
lean_dec(v_a_5459_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v_a_5461_; uint8_t v___x_5462_; lean_object* v___x_5463_; 
v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
lean_inc(v_a_5461_);
lean_dec_ref_known(v___x_5460_, 1);
v___x_5462_ = 1;
v___x_5463_ = l_Lean_Meta_mkForallFVars(v_args2_5416_, v_a_5461_, v___x_5457_, v___x_5428_, v___x_5428_, v___x_5462_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
lean_dec_ref(v_args2_5416_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; lean_object* v___x_5465_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc(v_a_5464_);
lean_dec_ref_known(v___x_5463_, 1);
v___x_5465_ = l_Lean_Meta_mkForallFVars(v_args1_5414_, v_a_5464_, v___x_5457_, v___x_5428_, v___x_5428_, v___x_5462_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5478_; 
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5468_ = v___x_5465_;
v_isShared_5469_ = v_isSharedCheck_5478_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5465_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5478_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5473_; 
v___x_5470_ = lean_array_get_size(v_val_5443_);
lean_dec(v_val_5443_);
v___x_5471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5471_, 0, v_a_5466_);
lean_ctor_set(v___x_5471_, 1, v_us_5413_);
lean_ctor_set(v___x_5471_, 2, v___x_5470_);
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 0, v___x_5471_);
v___x_5473_ = v___x_5451_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v___x_5471_);
v___x_5473_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
lean_object* v___x_5475_; 
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 0, v___x_5473_);
v___x_5475_ = v___x_5468_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v___x_5473_);
v___x_5475_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
return v___x_5475_;
}
}
}
}
else
{
lean_object* v_a_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5486_; 
lean_del_object(v___x_5451_);
lean_dec(v_val_5443_);
lean_dec(v_us_5413_);
v_a_5479_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5486_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5486_ == 0)
{
v___x_5481_ = v___x_5465_;
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_a_5479_);
lean_dec(v___x_5465_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v___x_5484_; 
if (v_isShared_5482_ == 0)
{
v___x_5484_ = v___x_5481_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v_a_5479_);
v___x_5484_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5483_;
}
v_reusejp_5483_:
{
return v___x_5484_;
}
}
}
}
else
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_del_object(v___x_5451_);
lean_dec(v_val_5443_);
lean_dec(v_us_5413_);
v_a_5487_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5463_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5463_);
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
lean_object* v_a_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5502_; 
lean_del_object(v___x_5451_);
lean_dec(v_val_5443_);
lean_dec_ref(v_args2_5416_);
lean_dec(v_us_5413_);
v_a_5495_ = lean_ctor_get(v___x_5460_, 0);
v_isSharedCheck_5502_ = !lean_is_exclusive(v___x_5460_);
if (v_isSharedCheck_5502_ == 0)
{
v___x_5497_ = v___x_5460_;
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_a_5495_);
lean_dec(v___x_5460_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v___x_5500_; 
if (v_isShared_5498_ == 0)
{
v___x_5500_ = v___x_5497_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
v___x_5500_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
return v___x_5500_;
}
}
}
}
else
{
lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5510_; 
lean_del_object(v___x_5451_);
lean_dec(v_val_5443_);
lean_dec(v_a_5437_);
lean_dec_ref(v_args2_5416_);
lean_dec(v_us_5413_);
v_a_5503_ = lean_ctor_get(v___x_5458_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5458_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5505_ = v___x_5458_;
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_dec(v___x_5458_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
}
}
else
{
lean_object* v___x_5512_; lean_object* v___x_5514_; 
lean_dec(v_a_5445_);
lean_dec(v_val_5443_);
lean_dec(v_a_5437_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5416_);
lean_dec_ref(v___x_5415_);
lean_dec(v_us_5413_);
v___x_5512_ = lean_box(0);
if (v_isShared_5448_ == 0)
{
lean_ctor_set(v___x_5447_, 0, v___x_5512_);
v___x_5514_ = v___x_5447_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v___x_5512_);
v___x_5514_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
return v___x_5514_;
}
}
}
}
else
{
lean_object* v_a_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5524_; 
lean_dec(v_val_5443_);
lean_dec(v_a_5437_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5416_);
lean_dec_ref(v___x_5415_);
lean_dec(v_us_5413_);
v_a_5517_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5524_ == 0)
{
v___x_5519_ = v___x_5444_;
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_a_5517_);
lean_dec(v___x_5444_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5522_; 
if (v_isShared_5520_ == 0)
{
v___x_5522_ = v___x_5519_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_a_5517_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
}
else
{
lean_object* v___x_5525_; lean_object* v___x_5527_; 
lean_dec(v_a_5439_);
lean_dec(v_a_5437_);
lean_dec_ref(v___x_5425_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5416_);
lean_dec_ref(v___x_5415_);
lean_dec(v_us_5413_);
v___x_5525_ = lean_box(0);
if (v_isShared_5442_ == 0)
{
lean_ctor_set(v___x_5441_, 0, v___x_5525_);
v___x_5527_ = v___x_5441_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5525_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
else
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5537_; 
lean_dec(v_a_5437_);
lean_dec_ref(v___x_5425_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5416_);
lean_dec_ref(v___x_5415_);
lean_dec(v_us_5413_);
v_a_5530_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5532_ = v___x_5438_;
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5438_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5535_; 
if (v_isShared_5533_ == 0)
{
v___x_5535_ = v___x_5532_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
v___x_5535_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
return v___x_5535_;
}
}
}
}
else
{
lean_object* v_a_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5545_; 
lean_dec_ref(v___x_5425_);
lean_dec_ref(v___x_5424_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5416_);
lean_dec_ref(v___x_5415_);
lean_dec(v_us_5413_);
v_a_5538_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5540_ = v___x_5436_;
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_a_5538_);
lean_dec(v___x_5436_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5543_; 
if (v_isShared_5541_ == 0)
{
v___x_5543_ = v___x_5540_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_a_5538_);
v___x_5543_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
return v___x_5543_;
}
}
}
}
else
{
lean_object* v___x_5546_; lean_object* v___x_5548_; 
lean_dec(v___x_5434_);
lean_dec(v_a_5427_);
lean_dec_ref(v___x_5425_);
lean_dec_ref(v___x_5424_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5416_);
lean_dec_ref(v___x_5415_);
lean_dec(v_us_5413_);
v___x_5546_ = lean_box(0);
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v___x_5546_);
v___x_5548_ = v___x_5432_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5546_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
return v___x_5548_;
}
}
}
}
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
lean_dec(v_a_5427_);
lean_dec_ref(v___x_5425_);
lean_dec_ref(v___x_5424_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5416_);
lean_dec_ref(v___x_5415_);
lean_dec(v_us_5413_);
v_a_5551_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5429_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5429_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5556_; 
if (v_isShared_5554_ == 0)
{
v___x_5556_ = v___x_5553_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5551_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
else
{
lean_object* v_a_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5566_; 
lean_dec_ref(v___x_5425_);
lean_dec_ref(v___x_5424_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5416_);
lean_dec_ref(v___x_5415_);
lean_dec(v_us_5413_);
v_a_5559_ = lean_ctor_get(v___x_5426_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5426_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5561_ = v___x_5426_;
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_a_5559_);
lean_dec(v___x_5426_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5564_; 
if (v_isShared_5562_ == 0)
{
v___x_5564_ = v___x_5561_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_a_5559_);
v___x_5564_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
return v___x_5564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v___x_5567_, lean_object* v_numParams_5568_, lean_object* v_name_5569_, lean_object* v_us_5570_, lean_object* v_args1_5571_, lean_object* v___x_5572_, lean_object* v_args2_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_){
_start:
{
lean_object* v_res_5579_; 
v_res_5579_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v___x_5567_, v_numParams_5568_, v_name_5569_, v_us_5570_, v_args1_5571_, v___x_5572_, v_args2_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec_ref(v___y_5574_);
lean_dec_ref(v_args1_5571_);
return v_res_5579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5580_, lean_object* v_name_5581_, lean_object* v_us_5582_, lean_object* v_ctorVal_5583_, lean_object* v_a_5584_, lean_object* v_args1_5585_, lean_object* v_x_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_){
_start:
{
lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___f_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; 
v___x_5592_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5580_);
lean_inc_ref_n(v_args1_5585_, 3);
v___x_5593_ = l_Array_toSubarray___redArg(v_args1_5585_, v___x_5592_, v_numParams_5580_);
v___f_5594_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5594_, 0, v___x_5592_);
lean_closure_set(v___f_5594_, 1, v_numParams_5580_);
lean_closure_set(v___f_5594_, 2, v_name_5581_);
lean_closure_set(v___f_5594_, 3, v_us_5582_);
lean_closure_set(v___f_5594_, 4, v_args1_5585_);
lean_closure_set(v___f_5594_, 5, v___x_5593_);
v___x_5595_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5596_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5596_, 0, v_ctorVal_5583_);
lean_closure_set(v___x_5596_, 1, v_args1_5585_);
lean_closure_set(v___x_5596_, 2, v___f_5594_);
lean_closure_set(v___x_5596_, 3, v___x_5592_);
lean_closure_set(v___x_5596_, 4, v_a_5584_);
lean_closure_set(v___x_5596_, 5, v___x_5595_);
v___x_5597_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5585_, v___x_5596_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_);
return v___x_5597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5598_, lean_object* v_name_5599_, lean_object* v_us_5600_, lean_object* v_ctorVal_5601_, lean_object* v_a_5602_, lean_object* v_args1_5603_, lean_object* v_x_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5598_, v_name_5599_, v_us_5600_, v_ctorVal_5601_, v_a_5602_, v_args1_5603_, v_x_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
lean_dec(v___y_5606_);
lean_dec_ref(v___y_5605_);
lean_dec_ref(v_x_5604_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_){
_start:
{
lean_object* v_toConstantVal_5617_; lean_object* v_numParams_5618_; lean_object* v_name_5619_; lean_object* v_levelParams_5620_; lean_object* v_type_5621_; lean_object* v___x_5622_; lean_object* v_us_5623_; lean_object* v___x_5624_; 
v_toConstantVal_5617_ = lean_ctor_get(v_ctorVal_5611_, 0);
v_numParams_5618_ = lean_ctor_get(v_ctorVal_5611_, 3);
lean_inc(v_numParams_5618_);
v_name_5619_ = lean_ctor_get(v_toConstantVal_5617_, 0);
lean_inc(v_name_5619_);
v_levelParams_5620_ = lean_ctor_get(v_toConstantVal_5617_, 1);
v_type_5621_ = lean_ctor_get(v_toConstantVal_5617_, 2);
v___x_5622_ = lean_box(0);
lean_inc(v_levelParams_5620_);
v_us_5623_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5620_, v___x_5622_);
lean_inc_ref(v_type_5621_);
v___x_5624_ = l_Lean_Meta_elimOptParam(v_type_5621_, v_a_5614_, v_a_5615_);
if (lean_obj_tag(v___x_5624_) == 0)
{
lean_object* v_a_5625_; lean_object* v___f_5626_; uint8_t v___x_5627_; lean_object* v___x_5628_; 
v_a_5625_ = lean_ctor_get(v___x_5624_, 0);
lean_inc_n(v_a_5625_, 2);
lean_dec_ref_known(v___x_5624_, 1);
v___f_5626_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5626_, 0, v_numParams_5618_);
lean_closure_set(v___f_5626_, 1, v_name_5619_);
lean_closure_set(v___f_5626_, 2, v_us_5623_);
lean_closure_set(v___f_5626_, 3, v_ctorVal_5611_);
lean_closure_set(v___f_5626_, 4, v_a_5625_);
v___x_5627_ = 0;
v___x_5628_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5625_, v___f_5626_, v___x_5627_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_);
return v___x_5628_;
}
else
{
lean_object* v_a_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5636_; 
lean_dec(v_us_5623_);
lean_dec(v_name_5619_);
lean_dec(v_numParams_5618_);
lean_dec_ref(v_ctorVal_5611_);
v_a_5629_ = lean_ctor_get(v___x_5624_, 0);
v_isSharedCheck_5636_ = !lean_is_exclusive(v___x_5624_);
if (v_isSharedCheck_5636_ == 0)
{
v___x_5631_ = v___x_5624_;
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_a_5629_);
lean_dec(v___x_5624_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5634_; 
if (v_isShared_5632_ == 0)
{
v___x_5634_ = v___x_5631_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5629_);
v___x_5634_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
return v___x_5634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_){
_start:
{
lean_object* v_res_5643_; 
v_res_5643_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5637_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_);
lean_dec(v_a_5641_);
lean_dec_ref(v_a_5640_);
lean_dec(v_a_5639_);
lean_dec_ref(v_a_5638_);
return v_res_5643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5645_; lean_object* v___x_5646_; 
v___x_5645_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5646_ = l_Lean_stringToMessageData(v___x_5645_);
return v___x_5646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v_toConstantVal_5653_; lean_object* v_name_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; 
v_toConstantVal_5653_ = lean_ctor_get(v_ctorVal_5647_, 0);
lean_inc_ref(v_toConstantVal_5653_);
lean_dec_ref(v_ctorVal_5647_);
v_name_5654_ = lean_ctor_get(v_toConstantVal_5653_, 0);
lean_inc(v_name_5654_);
lean_dec_ref(v_toConstantVal_5653_);
v___x_5655_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5656_ = l_Lean_MessageData_ofName(v_name_5654_);
v___x_5657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5657_, 0, v___x_5655_);
lean_ctor_set(v___x_5657_, 1, v___x_5656_);
v___x_5658_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5657_);
lean_ctor_set(v___x_5659_, 1, v___x_5658_);
v___x_5660_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5659_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_);
return v___x_5660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_){
_start:
{
lean_object* v_res_5667_; 
v_res_5667_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5661_, v_a_5662_, v_a_5663_, v_a_5664_, v_a_5665_);
lean_dec(v_a_5665_);
lean_dec_ref(v_a_5664_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5668_, lean_object* v_ctorVal_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_){
_start:
{
lean_object* v___x_5675_; 
v___x_5675_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5676_, lean_object* v_ctorVal_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_){
_start:
{
lean_object* v_res_5683_; 
v_res_5683_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5676_, v_ctorVal_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
lean_dec(v_a_5679_);
lean_dec_ref(v_a_5678_);
return v_res_5683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5689_, size_t v_sz_5690_, size_t v_i_5691_, lean_object* v_bs_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_){
_start:
{
uint8_t v___x_5698_; 
v___x_5698_ = lean_usize_dec_lt(v_i_5691_, v_sz_5690_);
if (v___x_5698_ == 0)
{
lean_object* v___x_5699_; 
lean_dec_ref(v_ctorVal_5689_);
v___x_5699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5699_, 0, v_bs_5692_);
return v___x_5699_;
}
else
{
lean_object* v_v_5700_; lean_object* v___x_5701_; lean_object* v_bs_x27_5702_; lean_object* v_a_5704_; lean_object* v___y_5710_; lean_object* v_lhs_5721_; lean_object* v_rhs_5722_; lean_object* v___x_5724_; 
v_v_5700_ = lean_array_uget(v_bs_5692_, v_i_5691_);
v___x_5701_ = lean_unsigned_to_nat(0u);
v_bs_x27_5702_ = lean_array_uset(v_bs_5692_, v_i_5691_, v___x_5701_);
lean_inc(v___y_5696_);
lean_inc_ref(v___y_5695_);
lean_inc(v___y_5694_);
lean_inc_ref(v___y_5693_);
v___x_5724_ = lean_infer_type(v_v_5700_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
if (lean_obj_tag(v___x_5724_) == 0)
{
lean_object* v_a_5725_; lean_object* v___x_5726_; 
v_a_5725_ = lean_ctor_get(v___x_5724_, 0);
lean_inc(v_a_5725_);
lean_dec_ref_known(v___x_5724_, 1);
v___x_5726_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5725_, v___y_5694_);
if (lean_obj_tag(v___x_5726_) == 0)
{
lean_object* v_a_5727_; lean_object* v___x_5728_; uint8_t v___x_5729_; 
v_a_5727_ = lean_ctor_get(v___x_5726_, 0);
lean_inc(v_a_5727_);
lean_dec_ref_known(v___x_5726_, 1);
v___x_5728_ = l_Lean_Expr_cleanupAnnotations(v_a_5727_);
v___x_5729_ = l_Lean_Expr_isApp(v___x_5728_);
if (v___x_5729_ == 0)
{
lean_object* v___x_5730_; 
lean_dec_ref(v___x_5728_);
lean_inc_ref(v_ctorVal_5689_);
v___x_5730_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5689_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
v___y_5710_ = v___x_5730_;
goto v___jp_5709_;
}
else
{
lean_object* v_arg_5731_; lean_object* v___x_5732_; uint8_t v___x_5733_; 
v_arg_5731_ = lean_ctor_get(v___x_5728_, 1);
lean_inc_ref(v_arg_5731_);
v___x_5732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5728_);
v___x_5733_ = l_Lean_Expr_isApp(v___x_5732_);
if (v___x_5733_ == 0)
{
lean_object* v___x_5734_; 
lean_dec_ref(v___x_5732_);
lean_dec_ref(v_arg_5731_);
lean_inc_ref(v_ctorVal_5689_);
v___x_5734_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5689_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
v___y_5710_ = v___x_5734_;
goto v___jp_5709_;
}
else
{
lean_object* v_arg_5735_; lean_object* v___x_5736_; uint8_t v___x_5737_; 
v_arg_5735_ = lean_ctor_get(v___x_5732_, 1);
lean_inc_ref(v_arg_5735_);
v___x_5736_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5732_);
v___x_5737_ = l_Lean_Expr_isApp(v___x_5736_);
if (v___x_5737_ == 0)
{
lean_object* v___x_5738_; 
lean_dec_ref(v___x_5736_);
lean_dec_ref(v_arg_5735_);
lean_dec_ref(v_arg_5731_);
lean_inc_ref(v_ctorVal_5689_);
v___x_5738_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5689_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
v___y_5710_ = v___x_5738_;
goto v___jp_5709_;
}
else
{
lean_object* v_arg_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; uint8_t v___x_5742_; 
v_arg_5739_ = lean_ctor_get(v___x_5736_, 1);
lean_inc_ref(v_arg_5739_);
v___x_5740_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5736_);
v___x_5741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5742_ = l_Lean_Expr_isConstOf(v___x_5740_, v___x_5741_);
if (v___x_5742_ == 0)
{
uint8_t v___x_5743_; 
lean_dec_ref(v_arg_5735_);
v___x_5743_ = l_Lean_Expr_isApp(v___x_5740_);
if (v___x_5743_ == 0)
{
lean_object* v___x_5744_; 
lean_dec_ref(v___x_5740_);
lean_dec_ref(v_arg_5739_);
lean_dec_ref(v_arg_5731_);
lean_inc_ref(v_ctorVal_5689_);
v___x_5744_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5689_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
v___y_5710_ = v___x_5744_;
goto v___jp_5709_;
}
else
{
lean_object* v___x_5745_; lean_object* v___x_5746_; uint8_t v___x_5747_; 
v___x_5745_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5740_);
v___x_5746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5747_ = l_Lean_Expr_isConstOf(v___x_5745_, v___x_5746_);
lean_dec_ref(v___x_5745_);
if (v___x_5747_ == 0)
{
lean_object* v___x_5748_; 
lean_dec_ref(v_arg_5739_);
lean_dec_ref(v_arg_5731_);
lean_inc_ref(v_ctorVal_5689_);
v___x_5748_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5689_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
v___y_5710_ = v___x_5748_;
goto v___jp_5709_;
}
else
{
v_lhs_5721_ = v_arg_5739_;
v_rhs_5722_ = v_arg_5731_;
goto v___jp_5720_;
}
}
}
else
{
lean_dec_ref(v___x_5740_);
lean_dec_ref(v_arg_5739_);
v_lhs_5721_ = v_arg_5735_;
v_rhs_5722_ = v_arg_5731_;
goto v___jp_5720_;
}
}
}
}
}
else
{
lean_object* v_a_5749_; lean_object* v___x_5751_; uint8_t v_isShared_5752_; uint8_t v_isSharedCheck_5756_; 
lean_dec_ref(v_bs_x27_5702_);
lean_dec_ref(v_ctorVal_5689_);
v_a_5749_ = lean_ctor_get(v___x_5726_, 0);
v_isSharedCheck_5756_ = !lean_is_exclusive(v___x_5726_);
if (v_isSharedCheck_5756_ == 0)
{
v___x_5751_ = v___x_5726_;
v_isShared_5752_ = v_isSharedCheck_5756_;
goto v_resetjp_5750_;
}
else
{
lean_inc(v_a_5749_);
lean_dec(v___x_5726_);
v___x_5751_ = lean_box(0);
v_isShared_5752_ = v_isSharedCheck_5756_;
goto v_resetjp_5750_;
}
v_resetjp_5750_:
{
lean_object* v___x_5754_; 
if (v_isShared_5752_ == 0)
{
v___x_5754_ = v___x_5751_;
goto v_reusejp_5753_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_a_5749_);
v___x_5754_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5753_;
}
v_reusejp_5753_:
{
return v___x_5754_;
}
}
}
}
else
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5764_; 
lean_dec_ref(v_bs_x27_5702_);
lean_dec_ref(v_ctorVal_5689_);
v_a_5757_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5759_ = v___x_5724_;
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5724_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5762_; 
if (v_isShared_5760_ == 0)
{
v___x_5762_ = v___x_5759_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
v___jp_5703_:
{
size_t v___x_5705_; size_t v___x_5706_; lean_object* v___x_5707_; 
v___x_5705_ = ((size_t)1ULL);
v___x_5706_ = lean_usize_add(v_i_5691_, v___x_5705_);
v___x_5707_ = lean_array_uset(v_bs_x27_5702_, v_i_5691_, v_a_5704_);
v_i_5691_ = v___x_5706_;
v_bs_5692_ = v___x_5707_;
goto _start;
}
v___jp_5709_:
{
if (lean_obj_tag(v___y_5710_) == 0)
{
lean_object* v_a_5711_; 
v_a_5711_ = lean_ctor_get(v___y_5710_, 0);
lean_inc(v_a_5711_);
lean_dec_ref_known(v___y_5710_, 1);
v_a_5704_ = v_a_5711_;
goto v___jp_5703_;
}
else
{
lean_object* v_a_5712_; lean_object* v___x_5714_; uint8_t v_isShared_5715_; uint8_t v_isSharedCheck_5719_; 
lean_dec_ref(v_bs_x27_5702_);
lean_dec_ref(v_ctorVal_5689_);
v_a_5712_ = lean_ctor_get(v___y_5710_, 0);
v_isSharedCheck_5719_ = !lean_is_exclusive(v___y_5710_);
if (v_isSharedCheck_5719_ == 0)
{
v___x_5714_ = v___y_5710_;
v_isShared_5715_ = v_isSharedCheck_5719_;
goto v_resetjp_5713_;
}
else
{
lean_inc(v_a_5712_);
lean_dec(v___y_5710_);
v___x_5714_ = lean_box(0);
v_isShared_5715_ = v_isSharedCheck_5719_;
goto v_resetjp_5713_;
}
v_resetjp_5713_:
{
lean_object* v___x_5717_; 
if (v_isShared_5715_ == 0)
{
v___x_5717_ = v___x_5714_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_a_5712_);
v___x_5717_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
return v___x_5717_;
}
}
}
}
v___jp_5720_:
{
lean_object* v___x_5723_; 
v___x_5723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5723_, 0, v_lhs_5721_);
lean_ctor_set(v___x_5723_, 1, v_rhs_5722_);
v_a_5704_ = v___x_5723_;
goto v___jp_5703_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5765_, lean_object* v_sz_5766_, lean_object* v_i_5767_, lean_object* v_bs_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_){
_start:
{
size_t v_sz_boxed_5774_; size_t v_i_boxed_5775_; lean_object* v_res_5776_; 
v_sz_boxed_5774_ = lean_unbox_usize(v_sz_5766_);
lean_dec(v_sz_5766_);
v_i_boxed_5775_ = lean_unbox_usize(v_i_5767_);
lean_dec(v_i_5767_);
v_res_5776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5765_, v_sz_boxed_5774_, v_i_boxed_5775_, v_bs_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
lean_dec(v___y_5772_);
lean_dec_ref(v___y_5771_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
return v_res_5776_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5778_; lean_object* v___x_5779_; 
v___x_5778_ = lean_unsigned_to_nat(0u);
v___x_5779_ = l_Lean_Level_ofNat(v___x_5778_);
return v___x_5779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5780_, lean_object* v_us_5781_, lean_object* v_numIndices_5782_, lean_object* v_xs_5783_, lean_object* v_type_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_){
_start:
{
lean_object* v_toConstantVal_5790_; lean_object* v_induct_5791_; lean_object* v_numParams_5792_; lean_object* v___x_5793_; lean_object* v_noConfusionName_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v_noConfusion_5798_; lean_object* v_noConfusion_5799_; lean_object* v_lower_5801_; lean_object* v_upper_5802_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v_n_5913_; uint8_t v___x_5914_; 
v_toConstantVal_5790_ = lean_ctor_get(v_ctorVal_5780_, 0);
v_induct_5791_ = lean_ctor_get(v_ctorVal_5780_, 1);
v_numParams_5792_ = lean_ctor_get(v_ctorVal_5780_, 3);
v___x_5793_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5791_);
v_noConfusionName_5794_ = l_Lean_Name_str___override(v_induct_5791_, v___x_5793_);
v___x_5795_ = lean_unsigned_to_nat(0u);
v___x_5796_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5797_, 0, v___x_5796_);
lean_ctor_set(v___x_5797_, 1, v_us_5781_);
v_noConfusion_5798_ = l_Lean_mkConst(v_noConfusionName_5794_, v___x_5797_);
v_noConfusion_5799_ = l_Lean_Expr_app___override(v_noConfusion_5798_, v_type_5784_);
v___x_5909_ = lean_array_get_size(v_xs_5783_);
v___x_5910_ = lean_nat_sub(v___x_5909_, v_numParams_5792_);
v___x_5911_ = lean_nat_sub(v___x_5910_, v_numIndices_5782_);
lean_dec(v___x_5910_);
v___x_5912_ = lean_unsigned_to_nat(1u);
v_n_5913_ = lean_nat_sub(v___x_5911_, v___x_5912_);
lean_dec(v___x_5911_);
v___x_5914_ = lean_nat_dec_le(v_n_5913_, v___x_5795_);
if (v___x_5914_ == 0)
{
v_lower_5801_ = v_n_5913_;
v_upper_5802_ = v___x_5909_;
goto v___jp_5800_;
}
else
{
lean_dec(v_n_5913_);
v_lower_5801_ = v___x_5795_;
v_upper_5802_ = v___x_5909_;
goto v___jp_5800_;
}
v___jp_5800_:
{
lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v_eqs_5805_; size_t v_sz_5806_; size_t v___x_5807_; lean_object* v___x_5808_; 
lean_inc_ref(v_xs_5783_);
v___x_5803_ = l_Array_toSubarray___redArg(v_xs_5783_, v_lower_5801_, v_upper_5802_);
v___x_5804_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5805_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5803_, v___x_5804_);
v_sz_5806_ = lean_array_size(v_eqs_5805_);
v___x_5807_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5805_);
lean_inc_ref(v_ctorVal_5780_);
v___x_5808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5780_, v_sz_5806_, v___x_5807_, v_eqs_5805_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
if (lean_obj_tag(v___x_5808_) == 0)
{
lean_object* v_a_5809_; lean_object* v___x_5810_; lean_object* v_fst_5811_; lean_object* v_snd_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; 
v_a_5809_ = lean_ctor_get(v___x_5808_, 0);
lean_inc(v_a_5809_);
lean_dec_ref_known(v___x_5808_, 1);
v___x_5810_ = l_Array_unzip___redArg(v_a_5809_);
lean_dec(v_a_5809_);
v_fst_5811_ = lean_ctor_get(v___x_5810_, 0);
lean_inc(v_fst_5811_);
v_snd_5812_ = lean_ctor_get(v___x_5810_, 1);
lean_inc(v_snd_5812_);
lean_dec_ref(v___x_5810_);
v___x_5813_ = l_Lean_mkAppN(v_noConfusion_5799_, v_fst_5811_);
lean_dec(v_fst_5811_);
v___x_5814_ = l_Lean_mkAppN(v___x_5813_, v_snd_5812_);
lean_dec(v_snd_5812_);
v___x_5815_ = l_Lean_mkAppN(v___x_5814_, v_eqs_5805_);
lean_dec_ref(v_eqs_5805_);
lean_inc(v___y_5788_);
lean_inc_ref(v___y_5787_);
lean_inc(v___y_5786_);
lean_inc_ref(v___y_5785_);
lean_inc_ref(v___x_5815_);
v___x_5816_ = lean_infer_type(v___x_5815_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
if (lean_obj_tag(v___x_5816_) == 0)
{
lean_object* v_a_5817_; lean_object* v___x_5818_; 
v_a_5817_ = lean_ctor_get(v___x_5816_, 0);
lean_inc(v_a_5817_);
lean_dec_ref_known(v___x_5816_, 1);
lean_inc(v___y_5788_);
lean_inc_ref(v___y_5787_);
lean_inc(v___y_5786_);
lean_inc_ref(v___y_5785_);
v___x_5818_ = lean_whnf(v_a_5817_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
if (lean_obj_tag(v___x_5818_) == 0)
{
lean_object* v_a_5819_; 
v_a_5819_ = lean_ctor_get(v___x_5818_, 0);
lean_inc(v_a_5819_);
lean_dec_ref_known(v___x_5818_, 1);
if (lean_obj_tag(v_a_5819_) == 7)
{
lean_object* v_binderType_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; 
lean_inc_ref(v_toConstantVal_5790_);
lean_dec_ref(v_ctorVal_5780_);
v_binderType_5820_ = lean_ctor_get(v_a_5819_, 1);
lean_inc_ref(v_binderType_5820_);
lean_dec_ref_known(v_a_5819_, 3);
v___x_5821_ = lean_box(0);
v___x_5822_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5820_, v___x_5821_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
if (lean_obj_tag(v___x_5822_) == 0)
{
lean_object* v_a_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; 
v_a_5823_ = lean_ctor_get(v___x_5822_, 0);
lean_inc_n(v_a_5823_, 2);
lean_dec_ref_known(v___x_5822_, 1);
v___x_5824_ = l_Lean_Expr_app___override(v___x_5815_, v_a_5823_);
v___x_5825_ = l_Lean_Expr_mvarId_x21(v_a_5823_);
lean_dec(v_a_5823_);
v___x_5826_ = l_Lean_MVarId_intros(v___x_5825_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
if (lean_obj_tag(v___x_5826_) == 0)
{
lean_object* v_a_5827_; lean_object* v_snd_5828_; lean_object* v_name_5829_; lean_object* v___x_5830_; 
v_a_5827_ = lean_ctor_get(v___x_5826_, 0);
lean_inc(v_a_5827_);
lean_dec_ref_known(v___x_5826_, 1);
v_snd_5828_ = lean_ctor_get(v_a_5827_, 1);
lean_inc(v_snd_5828_);
lean_dec(v_a_5827_);
v_name_5829_ = lean_ctor_get(v_toConstantVal_5790_, 0);
lean_inc(v_name_5829_);
lean_dec_ref(v_toConstantVal_5790_);
v___x_5830_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5828_, v_name_5829_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
if (lean_obj_tag(v___x_5830_) == 0)
{
lean_object* v___x_5831_; lean_object* v_a_5832_; lean_object* v___x_5834_; uint8_t v_isShared_5835_; uint8_t v_isSharedCheck_5859_; 
lean_dec_ref_known(v___x_5830_, 1);
v___x_5831_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5824_, v___y_5786_);
v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5859_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5834_ = v___x_5831_;
v_isShared_5835_ = v_isSharedCheck_5859_;
goto v_resetjp_5833_;
}
else
{
lean_inc(v_a_5832_);
lean_dec(v___x_5831_);
v___x_5834_ = lean_box(0);
v_isShared_5835_ = v_isSharedCheck_5859_;
goto v_resetjp_5833_;
}
v_resetjp_5833_:
{
uint8_t v___x_5836_; uint8_t v___x_5837_; uint8_t v___x_5838_; lean_object* v___x_5839_; 
v___x_5836_ = 0;
v___x_5837_ = 1;
v___x_5838_ = 1;
v___x_5839_ = l_Lean_Meta_mkLambdaFVars(v_xs_5783_, v_a_5832_, v___x_5836_, v___x_5837_, v___x_5836_, v___x_5837_, v___x_5838_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
lean_dec_ref(v_xs_5783_);
if (lean_obj_tag(v___x_5839_) == 0)
{
lean_object* v_a_5840_; lean_object* v___x_5842_; uint8_t v_isShared_5843_; uint8_t v_isSharedCheck_5850_; 
v_a_5840_ = lean_ctor_get(v___x_5839_, 0);
v_isSharedCheck_5850_ = !lean_is_exclusive(v___x_5839_);
if (v_isSharedCheck_5850_ == 0)
{
v___x_5842_ = v___x_5839_;
v_isShared_5843_ = v_isSharedCheck_5850_;
goto v_resetjp_5841_;
}
else
{
lean_inc(v_a_5840_);
lean_dec(v___x_5839_);
v___x_5842_ = lean_box(0);
v_isShared_5843_ = v_isSharedCheck_5850_;
goto v_resetjp_5841_;
}
v_resetjp_5841_:
{
lean_object* v___x_5845_; 
if (v_isShared_5835_ == 0)
{
lean_ctor_set_tag(v___x_5834_, 1);
lean_ctor_set(v___x_5834_, 0, v_a_5840_);
v___x_5845_ = v___x_5834_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5849_; 
v_reuseFailAlloc_5849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5840_);
v___x_5845_ = v_reuseFailAlloc_5849_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
lean_object* v___x_5847_; 
if (v_isShared_5843_ == 0)
{
lean_ctor_set(v___x_5842_, 0, v___x_5845_);
v___x_5847_ = v___x_5842_;
goto v_reusejp_5846_;
}
else
{
lean_object* v_reuseFailAlloc_5848_; 
v_reuseFailAlloc_5848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5848_, 0, v___x_5845_);
v___x_5847_ = v_reuseFailAlloc_5848_;
goto v_reusejp_5846_;
}
v_reusejp_5846_:
{
return v___x_5847_;
}
}
}
}
else
{
lean_object* v_a_5851_; lean_object* v___x_5853_; uint8_t v_isShared_5854_; uint8_t v_isSharedCheck_5858_; 
lean_del_object(v___x_5834_);
v_a_5851_ = lean_ctor_get(v___x_5839_, 0);
v_isSharedCheck_5858_ = !lean_is_exclusive(v___x_5839_);
if (v_isSharedCheck_5858_ == 0)
{
v___x_5853_ = v___x_5839_;
v_isShared_5854_ = v_isSharedCheck_5858_;
goto v_resetjp_5852_;
}
else
{
lean_inc(v_a_5851_);
lean_dec(v___x_5839_);
v___x_5853_ = lean_box(0);
v_isShared_5854_ = v_isSharedCheck_5858_;
goto v_resetjp_5852_;
}
v_resetjp_5852_:
{
lean_object* v___x_5856_; 
if (v_isShared_5854_ == 0)
{
v___x_5856_ = v___x_5853_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_a_5851_);
v___x_5856_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
return v___x_5856_;
}
}
}
}
}
else
{
lean_object* v_a_5860_; lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5867_; 
lean_dec_ref(v___x_5824_);
lean_dec_ref(v_xs_5783_);
v_a_5860_ = lean_ctor_get(v___x_5830_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v___x_5830_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5862_ = v___x_5830_;
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
else
{
lean_inc(v_a_5860_);
lean_dec(v___x_5830_);
v___x_5862_ = lean_box(0);
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
v_resetjp_5861_:
{
lean_object* v___x_5865_; 
if (v_isShared_5863_ == 0)
{
v___x_5865_ = v___x_5862_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5860_);
v___x_5865_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
return v___x_5865_;
}
}
}
}
else
{
lean_object* v_a_5868_; lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5875_; 
lean_dec_ref(v___x_5824_);
lean_dec_ref(v_toConstantVal_5790_);
lean_dec_ref(v_xs_5783_);
v_a_5868_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5875_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5875_ == 0)
{
v___x_5870_ = v___x_5826_;
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
else
{
lean_inc(v_a_5868_);
lean_dec(v___x_5826_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
lean_object* v___x_5873_; 
if (v_isShared_5871_ == 0)
{
v___x_5873_ = v___x_5870_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5874_; 
v_reuseFailAlloc_5874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5874_, 0, v_a_5868_);
v___x_5873_ = v_reuseFailAlloc_5874_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
return v___x_5873_;
}
}
}
}
else
{
lean_object* v_a_5876_; lean_object* v___x_5878_; uint8_t v_isShared_5879_; uint8_t v_isSharedCheck_5883_; 
lean_dec_ref(v___x_5815_);
lean_dec_ref(v_toConstantVal_5790_);
lean_dec_ref(v_xs_5783_);
v_a_5876_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5883_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5883_ == 0)
{
v___x_5878_ = v___x_5822_;
v_isShared_5879_ = v_isSharedCheck_5883_;
goto v_resetjp_5877_;
}
else
{
lean_inc(v_a_5876_);
lean_dec(v___x_5822_);
v___x_5878_ = lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5883_;
goto v_resetjp_5877_;
}
v_resetjp_5877_:
{
lean_object* v___x_5881_; 
if (v_isShared_5879_ == 0)
{
v___x_5881_ = v___x_5878_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5882_; 
v_reuseFailAlloc_5882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5882_, 0, v_a_5876_);
v___x_5881_ = v_reuseFailAlloc_5882_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
return v___x_5881_;
}
}
}
}
else
{
lean_object* v___x_5884_; 
lean_dec(v_a_5819_);
lean_dec_ref(v___x_5815_);
lean_dec_ref(v_xs_5783_);
v___x_5884_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5780_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
return v___x_5884_;
}
}
else
{
lean_object* v_a_5885_; lean_object* v___x_5887_; uint8_t v_isShared_5888_; uint8_t v_isSharedCheck_5892_; 
lean_dec_ref(v___x_5815_);
lean_dec_ref(v_xs_5783_);
lean_dec_ref(v_ctorVal_5780_);
v_a_5885_ = lean_ctor_get(v___x_5818_, 0);
v_isSharedCheck_5892_ = !lean_is_exclusive(v___x_5818_);
if (v_isSharedCheck_5892_ == 0)
{
v___x_5887_ = v___x_5818_;
v_isShared_5888_ = v_isSharedCheck_5892_;
goto v_resetjp_5886_;
}
else
{
lean_inc(v_a_5885_);
lean_dec(v___x_5818_);
v___x_5887_ = lean_box(0);
v_isShared_5888_ = v_isSharedCheck_5892_;
goto v_resetjp_5886_;
}
v_resetjp_5886_:
{
lean_object* v___x_5890_; 
if (v_isShared_5888_ == 0)
{
v___x_5890_ = v___x_5887_;
goto v_reusejp_5889_;
}
else
{
lean_object* v_reuseFailAlloc_5891_; 
v_reuseFailAlloc_5891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5891_, 0, v_a_5885_);
v___x_5890_ = v_reuseFailAlloc_5891_;
goto v_reusejp_5889_;
}
v_reusejp_5889_:
{
return v___x_5890_;
}
}
}
}
else
{
lean_object* v_a_5893_; lean_object* v___x_5895_; uint8_t v_isShared_5896_; uint8_t v_isSharedCheck_5900_; 
lean_dec_ref(v___x_5815_);
lean_dec_ref(v_xs_5783_);
lean_dec_ref(v_ctorVal_5780_);
v_a_5893_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5900_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5900_ == 0)
{
v___x_5895_ = v___x_5816_;
v_isShared_5896_ = v_isSharedCheck_5900_;
goto v_resetjp_5894_;
}
else
{
lean_inc(v_a_5893_);
lean_dec(v___x_5816_);
v___x_5895_ = lean_box(0);
v_isShared_5896_ = v_isSharedCheck_5900_;
goto v_resetjp_5894_;
}
v_resetjp_5894_:
{
lean_object* v___x_5898_; 
if (v_isShared_5896_ == 0)
{
v___x_5898_ = v___x_5895_;
goto v_reusejp_5897_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v_a_5893_);
v___x_5898_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5897_;
}
v_reusejp_5897_:
{
return v___x_5898_;
}
}
}
}
else
{
lean_object* v_a_5901_; lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5908_; 
lean_dec_ref(v_eqs_5805_);
lean_dec_ref(v_noConfusion_5799_);
lean_dec_ref(v_xs_5783_);
lean_dec_ref(v_ctorVal_5780_);
v_a_5901_ = lean_ctor_get(v___x_5808_, 0);
v_isSharedCheck_5908_ = !lean_is_exclusive(v___x_5808_);
if (v_isSharedCheck_5908_ == 0)
{
v___x_5903_ = v___x_5808_;
v_isShared_5904_ = v_isSharedCheck_5908_;
goto v_resetjp_5902_;
}
else
{
lean_inc(v_a_5901_);
lean_dec(v___x_5808_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5908_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v___x_5906_; 
if (v_isShared_5904_ == 0)
{
v___x_5906_ = v___x_5903_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5907_; 
v_reuseFailAlloc_5907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5907_, 0, v_a_5901_);
v___x_5906_ = v_reuseFailAlloc_5907_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
return v___x_5906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5915_, lean_object* v_us_5916_, lean_object* v_numIndices_5917_, lean_object* v_xs_5918_, lean_object* v_type_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_){
_start:
{
lean_object* v_res_5925_; 
v_res_5925_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5915_, v_us_5916_, v_numIndices_5917_, v_xs_5918_, v_type_5919_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_);
lean_dec(v___y_5923_);
lean_dec_ref(v___y_5922_);
lean_dec(v___y_5921_);
lean_dec_ref(v___y_5920_);
lean_dec(v_numIndices_5917_);
return v_res_5925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5926_, lean_object* v_typeInfo_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_){
_start:
{
lean_object* v_thmType_5933_; lean_object* v_us_5934_; lean_object* v_numIndices_5935_; lean_object* v___f_5936_; uint8_t v___x_5937_; lean_object* v___x_5938_; 
v_thmType_5933_ = lean_ctor_get(v_typeInfo_5927_, 0);
lean_inc_ref(v_thmType_5933_);
v_us_5934_ = lean_ctor_get(v_typeInfo_5927_, 1);
lean_inc(v_us_5934_);
v_numIndices_5935_ = lean_ctor_get(v_typeInfo_5927_, 2);
lean_inc(v_numIndices_5935_);
lean_dec_ref(v_typeInfo_5927_);
v___f_5936_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5936_, 0, v_ctorVal_5926_);
lean_closure_set(v___f_5936_, 1, v_us_5934_);
lean_closure_set(v___f_5936_, 2, v_numIndices_5935_);
v___x_5937_ = 0;
v___x_5938_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5933_, v___f_5936_, v___x_5937_, v___x_5937_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_);
return v___x_5938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5939_, lean_object* v_typeInfo_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_){
_start:
{
lean_object* v_res_5946_; 
v_res_5946_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5939_, v_typeInfo_5940_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_);
lean_dec(v_a_5944_);
lean_dec_ref(v_a_5943_);
lean_dec(v_a_5942_);
lean_dec_ref(v_a_5941_);
return v_res_5946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5949_){
_start:
{
lean_object* v___x_5950_; lean_object* v___x_5951_; 
v___x_5950_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5951_ = l_Lean_Name_str___override(v_ctorName_5949_, v___x_5950_);
return v___x_5951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5952_, lean_object* v_ctorVal_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_){
_start:
{
lean_object* v___x_5959_; 
lean_inc_ref(v_ctorVal_5953_);
v___x_5959_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_);
if (lean_obj_tag(v___x_5959_) == 0)
{
lean_object* v_a_5960_; lean_object* v___x_5962_; uint8_t v_isShared_5963_; uint8_t v_isSharedCheck_6021_; 
v_a_5960_ = lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_6021_ = !lean_is_exclusive(v___x_5959_);
if (v_isSharedCheck_6021_ == 0)
{
v___x_5962_ = v___x_5959_;
v_isShared_5963_ = v_isSharedCheck_6021_;
goto v_resetjp_5961_;
}
else
{
lean_inc(v_a_5960_);
lean_dec(v___x_5959_);
v___x_5962_ = lean_box(0);
v_isShared_5963_ = v_isSharedCheck_6021_;
goto v_resetjp_5961_;
}
v_resetjp_5961_:
{
if (lean_obj_tag(v_a_5960_) == 1)
{
lean_object* v_val_5964_; lean_object* v___x_5965_; 
lean_del_object(v___x_5962_);
v_val_5964_ = lean_ctor_get(v_a_5960_, 0);
lean_inc_n(v_val_5964_, 2);
lean_dec_ref_known(v_a_5960_, 1);
lean_inc_ref(v_ctorVal_5953_);
v___x_5965_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5953_, v_val_5964_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_);
if (lean_obj_tag(v___x_5965_) == 0)
{
lean_object* v_a_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_6008_; 
v_a_5966_ = lean_ctor_get(v___x_5965_, 0);
v_isSharedCheck_6008_ = !lean_is_exclusive(v___x_5965_);
if (v_isSharedCheck_6008_ == 0)
{
v___x_5968_ = v___x_5965_;
v_isShared_5969_ = v_isSharedCheck_6008_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_a_5966_);
lean_dec(v___x_5965_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_6008_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
if (lean_obj_tag(v_a_5966_) == 1)
{
lean_object* v_toConstantVal_5970_; lean_object* v_val_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_6003_; 
v_toConstantVal_5970_ = lean_ctor_get(v_ctorVal_5953_, 0);
lean_inc_ref(v_toConstantVal_5970_);
lean_dec_ref(v_ctorVal_5953_);
v_val_5971_ = lean_ctor_get(v_a_5966_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v_a_5966_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5973_ = v_a_5966_;
v_isShared_5974_ = v_isSharedCheck_6003_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_val_5971_);
lean_dec(v_a_5966_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_6003_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v_levelParams_5975_; lean_object* v___x_5977_; uint8_t v_isShared_5978_; uint8_t v_isSharedCheck_6000_; 
v_levelParams_5975_ = lean_ctor_get(v_toConstantVal_5970_, 1);
v_isSharedCheck_6000_ = !lean_is_exclusive(v_toConstantVal_5970_);
if (v_isSharedCheck_6000_ == 0)
{
lean_object* v_unused_6001_; lean_object* v_unused_6002_; 
v_unused_6001_ = lean_ctor_get(v_toConstantVal_5970_, 2);
lean_dec(v_unused_6001_);
v_unused_6002_ = lean_ctor_get(v_toConstantVal_5970_, 0);
lean_dec(v_unused_6002_);
v___x_5977_ = v_toConstantVal_5970_;
v_isShared_5978_ = v_isSharedCheck_6000_;
goto v_resetjp_5976_;
}
else
{
lean_inc(v_levelParams_5975_);
lean_dec(v_toConstantVal_5970_);
v___x_5977_ = lean_box(0);
v_isShared_5978_ = v_isSharedCheck_6000_;
goto v_resetjp_5976_;
}
v_resetjp_5976_:
{
lean_object* v_thmType_5979_; lean_object* v___x_5981_; uint8_t v_isShared_5982_; uint8_t v_isSharedCheck_5997_; 
v_thmType_5979_ = lean_ctor_get(v_val_5964_, 0);
v_isSharedCheck_5997_ = !lean_is_exclusive(v_val_5964_);
if (v_isSharedCheck_5997_ == 0)
{
lean_object* v_unused_5998_; lean_object* v_unused_5999_; 
v_unused_5998_ = lean_ctor_get(v_val_5964_, 2);
lean_dec(v_unused_5998_);
v_unused_5999_ = lean_ctor_get(v_val_5964_, 1);
lean_dec(v_unused_5999_);
v___x_5981_ = v_val_5964_;
v_isShared_5982_ = v_isSharedCheck_5997_;
goto v_resetjp_5980_;
}
else
{
lean_inc(v_thmType_5979_);
lean_dec(v_val_5964_);
v___x_5981_ = lean_box(0);
v_isShared_5982_ = v_isSharedCheck_5997_;
goto v_resetjp_5980_;
}
v_resetjp_5980_:
{
lean_object* v___x_5984_; 
lean_inc(v_thmName_5952_);
if (v_isShared_5978_ == 0)
{
lean_ctor_set(v___x_5977_, 2, v_thmType_5979_);
lean_ctor_set(v___x_5977_, 0, v_thmName_5952_);
v___x_5984_ = v___x_5977_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_5996_; 
v_reuseFailAlloc_5996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5996_, 0, v_thmName_5952_);
lean_ctor_set(v_reuseFailAlloc_5996_, 1, v_levelParams_5975_);
lean_ctor_set(v_reuseFailAlloc_5996_, 2, v_thmType_5979_);
v___x_5984_ = v_reuseFailAlloc_5996_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5988_; 
v___x_5985_ = lean_box(0);
v___x_5986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5986_, 0, v_thmName_5952_);
lean_ctor_set(v___x_5986_, 1, v___x_5985_);
if (v_isShared_5982_ == 0)
{
lean_ctor_set(v___x_5981_, 2, v___x_5986_);
lean_ctor_set(v___x_5981_, 1, v_val_5971_);
lean_ctor_set(v___x_5981_, 0, v___x_5984_);
v___x_5988_ = v___x_5981_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5995_; 
v_reuseFailAlloc_5995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5995_, 0, v___x_5984_);
lean_ctor_set(v_reuseFailAlloc_5995_, 1, v_val_5971_);
lean_ctor_set(v_reuseFailAlloc_5995_, 2, v___x_5986_);
v___x_5988_ = v_reuseFailAlloc_5995_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
lean_object* v___x_5990_; 
if (v_isShared_5974_ == 0)
{
lean_ctor_set(v___x_5973_, 0, v___x_5988_);
v___x_5990_ = v___x_5973_;
goto v_reusejp_5989_;
}
else
{
lean_object* v_reuseFailAlloc_5994_; 
v_reuseFailAlloc_5994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5994_, 0, v___x_5988_);
v___x_5990_ = v_reuseFailAlloc_5994_;
goto v_reusejp_5989_;
}
v_reusejp_5989_:
{
lean_object* v___x_5992_; 
if (v_isShared_5969_ == 0)
{
lean_ctor_set(v___x_5968_, 0, v___x_5990_);
v___x_5992_ = v___x_5968_;
goto v_reusejp_5991_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v___x_5990_);
v___x_5992_ = v_reuseFailAlloc_5993_;
goto v_reusejp_5991_;
}
v_reusejp_5991_:
{
return v___x_5992_;
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
lean_object* v___x_6004_; lean_object* v___x_6006_; 
lean_dec(v_a_5966_);
lean_dec(v_val_5964_);
lean_dec_ref(v_ctorVal_5953_);
lean_dec(v_thmName_5952_);
v___x_6004_ = lean_box(0);
if (v_isShared_5969_ == 0)
{
lean_ctor_set(v___x_5968_, 0, v___x_6004_);
v___x_6006_ = v___x_5968_;
goto v_reusejp_6005_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v___x_6004_);
v___x_6006_ = v_reuseFailAlloc_6007_;
goto v_reusejp_6005_;
}
v_reusejp_6005_:
{
return v___x_6006_;
}
}
}
}
else
{
lean_object* v_a_6009_; lean_object* v___x_6011_; uint8_t v_isShared_6012_; uint8_t v_isSharedCheck_6016_; 
lean_dec(v_val_5964_);
lean_dec_ref(v_ctorVal_5953_);
lean_dec(v_thmName_5952_);
v_a_6009_ = lean_ctor_get(v___x_5965_, 0);
v_isSharedCheck_6016_ = !lean_is_exclusive(v___x_5965_);
if (v_isSharedCheck_6016_ == 0)
{
v___x_6011_ = v___x_5965_;
v_isShared_6012_ = v_isSharedCheck_6016_;
goto v_resetjp_6010_;
}
else
{
lean_inc(v_a_6009_);
lean_dec(v___x_5965_);
v___x_6011_ = lean_box(0);
v_isShared_6012_ = v_isSharedCheck_6016_;
goto v_resetjp_6010_;
}
v_resetjp_6010_:
{
lean_object* v___x_6014_; 
if (v_isShared_6012_ == 0)
{
v___x_6014_ = v___x_6011_;
goto v_reusejp_6013_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v_a_6009_);
v___x_6014_ = v_reuseFailAlloc_6015_;
goto v_reusejp_6013_;
}
v_reusejp_6013_:
{
return v___x_6014_;
}
}
}
}
else
{
lean_object* v___x_6017_; lean_object* v___x_6019_; 
lean_dec(v_a_5960_);
lean_dec_ref(v_ctorVal_5953_);
lean_dec(v_thmName_5952_);
v___x_6017_ = lean_box(0);
if (v_isShared_5963_ == 0)
{
lean_ctor_set(v___x_5962_, 0, v___x_6017_);
v___x_6019_ = v___x_5962_;
goto v_reusejp_6018_;
}
else
{
lean_object* v_reuseFailAlloc_6020_; 
v_reuseFailAlloc_6020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6020_, 0, v___x_6017_);
v___x_6019_ = v_reuseFailAlloc_6020_;
goto v_reusejp_6018_;
}
v_reusejp_6018_:
{
return v___x_6019_;
}
}
}
}
else
{
lean_object* v_a_6022_; lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6029_; 
lean_dec_ref(v_ctorVal_5953_);
lean_dec(v_thmName_5952_);
v_a_6022_ = lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_6029_ = !lean_is_exclusive(v___x_5959_);
if (v_isSharedCheck_6029_ == 0)
{
v___x_6024_ = v___x_5959_;
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
else
{
lean_inc(v_a_6022_);
lean_dec(v___x_5959_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6029_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
lean_object* v___x_6027_; 
if (v_isShared_6025_ == 0)
{
v___x_6027_ = v___x_6024_;
goto v_reusejp_6026_;
}
else
{
lean_object* v_reuseFailAlloc_6028_; 
v_reuseFailAlloc_6028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6028_, 0, v_a_6022_);
v___x_6027_ = v_reuseFailAlloc_6028_;
goto v_reusejp_6026_;
}
v_reusejp_6026_:
{
return v___x_6027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6030_, lean_object* v_ctorVal_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_, lean_object* v_a_6034_, lean_object* v_a_6035_, lean_object* v_a_6036_){
_start:
{
lean_object* v_res_6037_; 
v_res_6037_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6030_, v_ctorVal_6031_, v_a_6032_, v_a_6033_, v_a_6034_, v_a_6035_);
lean_dec(v_a_6035_);
lean_dec_ref(v_a_6034_);
lean_dec(v_a_6033_);
lean_dec_ref(v_a_6032_);
return v_res_6037_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6038_, lean_object* v_n_6039_){
_start:
{
if (lean_obj_tag(v_n_6039_) == 1)
{
lean_object* v_pre_6040_; lean_object* v_str_6041_; lean_object* v___x_6042_; uint8_t v___x_6043_; 
v_pre_6040_ = lean_ctor_get(v_n_6039_, 0);
lean_inc(v_pre_6040_);
v_str_6041_ = lean_ctor_get(v_n_6039_, 1);
lean_inc_ref(v_str_6041_);
lean_dec_ref_known(v_n_6039_, 2);
v___x_6042_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6043_ = lean_string_dec_eq(v_str_6041_, v___x_6042_);
lean_dec_ref(v_str_6041_);
if (v___x_6043_ == 0)
{
lean_dec(v_pre_6040_);
lean_dec_ref(v_env_6038_);
return v___x_6043_;
}
else
{
uint8_t v___x_6044_; lean_object* v___x_6045_; 
v___x_6044_ = 0;
v___x_6045_ = l_Lean_Environment_find_x3f(v_env_6038_, v_pre_6040_, v___x_6044_);
if (lean_obj_tag(v___x_6045_) == 1)
{
lean_object* v_val_6046_; 
v_val_6046_ = lean_ctor_get(v___x_6045_, 0);
lean_inc(v_val_6046_);
lean_dec_ref_known(v___x_6045_, 1);
if (lean_obj_tag(v_val_6046_) == 6)
{
lean_dec_ref_known(v_val_6046_, 1);
return v___x_6043_;
}
else
{
lean_dec(v_val_6046_);
return v___x_6044_;
}
}
else
{
lean_dec(v___x_6045_);
return v___x_6044_;
}
}
}
else
{
uint8_t v___x_6047_; 
lean_dec(v_n_6039_);
lean_dec_ref(v_env_6038_);
v___x_6047_ = 0;
return v___x_6047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6048_, lean_object* v_n_6049_){
_start:
{
uint8_t v_res_6050_; lean_object* v_r_6051_; 
v_res_6050_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6048_, v_n_6049_);
v_r_6051_ = lean_box(v_res_6050_);
return v_r_6051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6054_; lean_object* v___x_6055_; 
v___f_6054_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6055_ = l_Lean_registerReservedNamePredicate(v___f_6054_);
return v___x_6055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6056_){
_start:
{
lean_object* v_res_6057_; 
v_res_6057_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6057_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6058_, lean_object* v___y_6059_){
_start:
{
lean_object* v___x_6061_; lean_object* v_env_6062_; lean_object* v_toConstantVal_6063_; lean_object* v_value_6064_; lean_object* v_all_6065_; uint8_t v___y_6067_; lean_object* v_type_6075_; uint8_t v___x_6076_; 
v___x_6061_ = lean_st_ref_get(v___y_6059_);
v_env_6062_ = lean_ctor_get(v___x_6061_, 0);
lean_inc_ref_n(v_env_6062_, 2);
lean_dec(v___x_6061_);
v_toConstantVal_6063_ = lean_ctor_get(v_thm_6058_, 0);
v_value_6064_ = lean_ctor_get(v_thm_6058_, 1);
v_all_6065_ = lean_ctor_get(v_thm_6058_, 2);
v_type_6075_ = lean_ctor_get(v_toConstantVal_6063_, 2);
v___x_6076_ = l_Lean_Environment_hasUnsafe(v_env_6062_, v_type_6075_);
if (v___x_6076_ == 0)
{
uint8_t v___x_6077_; 
v___x_6077_ = l_Lean_Environment_hasUnsafe(v_env_6062_, v_value_6064_);
v___y_6067_ = v___x_6077_;
goto v___jp_6066_;
}
else
{
lean_dec_ref(v_env_6062_);
v___y_6067_ = v___x_6076_;
goto v___jp_6066_;
}
v___jp_6066_:
{
if (v___y_6067_ == 0)
{
lean_object* v___x_6068_; lean_object* v___x_6069_; 
v___x_6068_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6068_, 0, v_thm_6058_);
v___x_6069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
return v___x_6069_;
}
else
{
lean_object* v___x_6070_; uint8_t v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
lean_inc(v_all_6065_);
lean_inc_ref(v_value_6064_);
lean_inc_ref(v_toConstantVal_6063_);
lean_dec_ref(v_thm_6058_);
v___x_6070_ = lean_box(0);
v___x_6071_ = 0;
v___x_6072_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6072_, 0, v_toConstantVal_6063_);
lean_ctor_set(v___x_6072_, 1, v_value_6064_);
lean_ctor_set(v___x_6072_, 2, v___x_6070_);
lean_ctor_set(v___x_6072_, 3, v_all_6065_);
lean_ctor_set_uint8(v___x_6072_, sizeof(void*)*4, v___x_6071_);
v___x_6073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6072_);
v___x_6074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6074_, 0, v___x_6073_);
return v___x_6074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_){
_start:
{
lean_object* v_res_6081_; 
v_res_6081_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6078_, v___y_6079_);
lean_dec(v___y_6079_);
return v_res_6081_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_){
_start:
{
lean_object* v___x_6088_; 
v___x_6088_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6082_, v___y_6086_);
return v___x_6088_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_){
_start:
{
lean_object* v_res_6095_; 
v_res_6095_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_);
lean_dec(v___y_6093_);
lean_dec_ref(v___y_6092_);
lean_dec(v___y_6091_);
lean_dec_ref(v___y_6090_);
return v_res_6095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6096_, uint8_t v___x_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_){
_start:
{
lean_object* v___x_6103_; lean_object* v_a_6104_; lean_object* v___x_6105_; 
v___x_6103_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6096_, v___y_6101_);
v_a_6104_ = lean_ctor_get(v___x_6103_, 0);
lean_inc(v_a_6104_);
lean_dec_ref(v___x_6103_);
v___x_6105_ = l_Lean_addDecl(v_a_6104_, v___x_6097_, v___y_6100_, v___y_6101_);
return v___x_6105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6106_, lean_object* v___x_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_){
_start:
{
uint8_t v___x_2152__boxed_6113_; lean_object* v_res_6114_; 
v___x_2152__boxed_6113_ = lean_unbox(v___x_6107_);
v_res_6114_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6106_, v___x_2152__boxed_6113_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_);
lean_dec(v___y_6111_);
lean_dec_ref(v___y_6110_);
lean_dec(v___y_6109_);
lean_dec_ref(v___y_6108_);
return v_res_6114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; 
v___x_6117_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_6118_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6119_ = lean_unsigned_to_nat(0u);
v___x_6120_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
lean_ctor_set(v___x_6120_, 2, v___x_6119_);
lean_ctor_set(v___x_6120_, 3, v___x_6119_);
lean_ctor_set(v___x_6120_, 4, v___x_6118_);
lean_ctor_set(v___x_6120_, 5, v___x_6118_);
lean_ctor_set(v___x_6120_, 6, v___x_6118_);
lean_ctor_set(v___x_6120_, 7, v___x_6118_);
lean_ctor_set(v___x_6120_, 8, v___x_6118_);
lean_ctor_set(v___x_6120_, 9, v___x_6118_);
lean_ctor_set(v___x_6120_, 10, v___x_6118_);
lean_ctor_set(v___x_6120_, 11, v___x_6117_);
return v___x_6120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6121_; lean_object* v___x_6122_; 
v___x_6121_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6122_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6121_);
lean_ctor_set(v___x_6122_, 1, v___x_6121_);
lean_ctor_set(v___x_6122_, 2, v___x_6121_);
lean_ctor_set(v___x_6122_, 3, v___x_6121_);
lean_ctor_set(v___x_6122_, 4, v___x_6121_);
lean_ctor_set(v___x_6122_, 5, v___x_6121_);
return v___x_6122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; 
v___x_6123_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6124_, 0, v___x_6123_);
lean_ctor_set(v___x_6124_, 1, v___x_6123_);
lean_ctor_set(v___x_6124_, 2, v___x_6123_);
lean_ctor_set(v___x_6124_, 3, v___x_6123_);
lean_ctor_set(v___x_6124_, 4, v___x_6123_);
return v___x_6124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6125_, lean_object* v_name_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_){
_start:
{
if (lean_obj_tag(v_name_6126_) == 1)
{
lean_object* v_pre_6138_; lean_object* v_str_6139_; lean_object* v___x_6140_; uint8_t v___x_6141_; 
v_pre_6138_ = lean_ctor_get(v_name_6126_, 0);
lean_inc(v_pre_6138_);
v_str_6139_ = lean_ctor_get(v_name_6126_, 1);
v___x_6140_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6141_ = lean_string_dec_eq(v_str_6139_, v___x_6140_);
if (v___x_6141_ == 0)
{
lean_dec_ref_known(v_name_6126_, 2);
lean_dec(v_pre_6138_);
lean_dec(v___x_6125_);
goto v___jp_6134_;
}
else
{
lean_object* v___x_6142_; lean_object* v_env_6143_; uint8_t v___x_6144_; lean_object* v___x_6145_; 
v___x_6142_ = lean_st_ref_get(v___y_6128_);
v_env_6143_ = lean_ctor_get(v___x_6142_, 0);
lean_inc_ref(v_env_6143_);
lean_dec(v___x_6142_);
v___x_6144_ = 0;
lean_inc(v_pre_6138_);
v___x_6145_ = l_Lean_Environment_find_x3f(v_env_6143_, v_pre_6138_, v___x_6144_);
if (lean_obj_tag(v___x_6145_) == 1)
{
lean_object* v_val_6146_; 
v_val_6146_ = lean_ctor_get(v___x_6145_, 0);
lean_inc(v_val_6146_);
lean_dec_ref_known(v___x_6145_, 1);
if (lean_obj_tag(v_val_6146_) == 6)
{
lean_object* v_val_6147_; lean_object* v___x_6149_; uint8_t v_isShared_6150_; uint8_t v_isSharedCheck_6197_; 
v_val_6147_ = lean_ctor_get(v_val_6146_, 0);
v_isSharedCheck_6197_ = !lean_is_exclusive(v_val_6146_);
if (v_isSharedCheck_6197_ == 0)
{
v___x_6149_ = v_val_6146_;
v_isShared_6150_ = v_isSharedCheck_6197_;
goto v_resetjp_6148_;
}
else
{
lean_inc(v_val_6147_);
lean_dec(v_val_6146_);
v___x_6149_ = lean_box(0);
v_isShared_6150_ = v_isSharedCheck_6197_;
goto v_resetjp_6148_;
}
v_resetjp_6148_:
{
uint8_t v___x_6151_; uint8_t v___x_6152_; uint8_t v___x_6153_; lean_object* v___x_6154_; uint64_t v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; uint8_t v_a_6169_; lean_object* v___x_6175_; 
v___x_6151_ = 1;
v___x_6152_ = 0;
v___x_6153_ = 2;
v___x_6154_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_6154_, 0, v___x_6144_);
lean_ctor_set_uint8(v___x_6154_, 1, v___x_6144_);
lean_ctor_set_uint8(v___x_6154_, 2, v___x_6144_);
lean_ctor_set_uint8(v___x_6154_, 3, v___x_6144_);
lean_ctor_set_uint8(v___x_6154_, 4, v___x_6144_);
lean_ctor_set_uint8(v___x_6154_, 5, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 6, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 7, v___x_6144_);
lean_ctor_set_uint8(v___x_6154_, 8, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 9, v___x_6151_);
lean_ctor_set_uint8(v___x_6154_, 10, v___x_6152_);
lean_ctor_set_uint8(v___x_6154_, 11, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 12, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 13, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 14, v___x_6153_);
lean_ctor_set_uint8(v___x_6154_, 15, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 16, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 17, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 18, v___x_6141_);
lean_ctor_set_uint8(v___x_6154_, 19, v___x_6144_);
v___x_6155_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6154_);
v___x_6156_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6156_, 0, v___x_6154_);
lean_ctor_set_uint64(v___x_6156_, sizeof(void*)*1, v___x_6155_);
v___x_6157_ = lean_unsigned_to_nat(0u);
v___x_6158_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_6159_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6160_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6161_ = lean_box(0);
lean_inc(v___x_6125_);
v___x_6162_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6162_, 0, v___x_6156_);
lean_ctor_set(v___x_6162_, 1, v___x_6125_);
lean_ctor_set(v___x_6162_, 2, v___x_6159_);
lean_ctor_set(v___x_6162_, 3, v___x_6160_);
lean_ctor_set(v___x_6162_, 4, v___x_6161_);
lean_ctor_set(v___x_6162_, 5, v___x_6157_);
lean_ctor_set(v___x_6162_, 6, v___x_6161_);
lean_ctor_set_uint8(v___x_6162_, sizeof(void*)*7, v___x_6144_);
lean_ctor_set_uint8(v___x_6162_, sizeof(void*)*7 + 1, v___x_6144_);
lean_ctor_set_uint8(v___x_6162_, sizeof(void*)*7 + 2, v___x_6144_);
lean_ctor_set_uint8(v___x_6162_, sizeof(void*)*7 + 3, v___x_6141_);
v___x_6163_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6164_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6165_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6163_);
lean_ctor_set(v___x_6166_, 1, v___x_6164_);
lean_ctor_set(v___x_6166_, 2, v___x_6125_);
lean_ctor_set(v___x_6166_, 3, v___x_6158_);
lean_ctor_set(v___x_6166_, 4, v___x_6165_);
v___x_6167_ = lean_st_mk_ref(v___x_6166_);
lean_inc_ref(v_name_6126_);
v___x_6175_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6126_, v_val_6147_, v___x_6162_, v___x_6167_, v___y_6127_, v___y_6128_);
if (lean_obj_tag(v___x_6175_) == 0)
{
lean_object* v_a_6176_; 
v_a_6176_ = lean_ctor_get(v___x_6175_, 0);
lean_inc(v_a_6176_);
lean_dec_ref_known(v___x_6175_, 1);
if (lean_obj_tag(v_a_6176_) == 1)
{
lean_object* v_val_6177_; lean_object* v___x_6178_; lean_object* v___f_6179_; lean_object* v___x_6180_; 
v_val_6177_ = lean_ctor_get(v_a_6176_, 0);
lean_inc(v_val_6177_);
lean_dec_ref_known(v_a_6176_, 1);
v___x_6178_ = lean_box(v___x_6144_);
v___f_6179_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6179_, 0, v_val_6177_);
lean_closure_set(v___f_6179_, 1, v___x_6178_);
v___x_6180_ = l_Lean_Meta_realizeConst(v_pre_6138_, v_name_6126_, v___f_6179_, v___x_6162_, v___x_6167_, v___y_6127_, v___y_6128_);
lean_dec_ref_known(v___x_6162_, 7);
if (lean_obj_tag(v___x_6180_) == 0)
{
lean_dec_ref_known(v___x_6180_, 1);
v_a_6169_ = v___x_6141_;
goto v___jp_6168_;
}
else
{
lean_object* v_a_6181_; lean_object* v___x_6183_; uint8_t v_isShared_6184_; uint8_t v_isSharedCheck_6188_; 
lean_dec(v___x_6167_);
lean_del_object(v___x_6149_);
v_a_6181_ = lean_ctor_get(v___x_6180_, 0);
v_isSharedCheck_6188_ = !lean_is_exclusive(v___x_6180_);
if (v_isSharedCheck_6188_ == 0)
{
v___x_6183_ = v___x_6180_;
v_isShared_6184_ = v_isSharedCheck_6188_;
goto v_resetjp_6182_;
}
else
{
lean_inc(v_a_6181_);
lean_dec(v___x_6180_);
v___x_6183_ = lean_box(0);
v_isShared_6184_ = v_isSharedCheck_6188_;
goto v_resetjp_6182_;
}
v_resetjp_6182_:
{
lean_object* v___x_6186_; 
if (v_isShared_6184_ == 0)
{
v___x_6186_ = v___x_6183_;
goto v_reusejp_6185_;
}
else
{
lean_object* v_reuseFailAlloc_6187_; 
v_reuseFailAlloc_6187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6187_, 0, v_a_6181_);
v___x_6186_ = v_reuseFailAlloc_6187_;
goto v_reusejp_6185_;
}
v_reusejp_6185_:
{
return v___x_6186_;
}
}
}
}
else
{
lean_dec(v_a_6176_);
lean_dec_ref_known(v___x_6162_, 7);
lean_dec_ref_known(v_name_6126_, 2);
lean_dec(v_pre_6138_);
v_a_6169_ = v___x_6144_;
goto v___jp_6168_;
}
}
else
{
lean_object* v_a_6189_; lean_object* v___x_6191_; uint8_t v_isShared_6192_; uint8_t v_isSharedCheck_6196_; 
lean_dec(v___x_6167_);
lean_dec_ref_known(v___x_6162_, 7);
lean_del_object(v___x_6149_);
lean_dec_ref_known(v_name_6126_, 2);
lean_dec(v_pre_6138_);
v_a_6189_ = lean_ctor_get(v___x_6175_, 0);
v_isSharedCheck_6196_ = !lean_is_exclusive(v___x_6175_);
if (v_isSharedCheck_6196_ == 0)
{
v___x_6191_ = v___x_6175_;
v_isShared_6192_ = v_isSharedCheck_6196_;
goto v_resetjp_6190_;
}
else
{
lean_inc(v_a_6189_);
lean_dec(v___x_6175_);
v___x_6191_ = lean_box(0);
v_isShared_6192_ = v_isSharedCheck_6196_;
goto v_resetjp_6190_;
}
v_resetjp_6190_:
{
lean_object* v___x_6194_; 
if (v_isShared_6192_ == 0)
{
v___x_6194_ = v___x_6191_;
goto v_reusejp_6193_;
}
else
{
lean_object* v_reuseFailAlloc_6195_; 
v_reuseFailAlloc_6195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6195_, 0, v_a_6189_);
v___x_6194_ = v_reuseFailAlloc_6195_;
goto v_reusejp_6193_;
}
v_reusejp_6193_:
{
return v___x_6194_;
}
}
}
v___jp_6168_:
{
lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6173_; 
v___x_6170_ = lean_st_ref_get(v___x_6167_);
lean_dec(v___x_6167_);
lean_dec(v___x_6170_);
v___x_6171_ = lean_box(v_a_6169_);
if (v_isShared_6150_ == 0)
{
lean_ctor_set_tag(v___x_6149_, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6171_);
v___x_6173_ = v___x_6149_;
goto v_reusejp_6172_;
}
else
{
lean_object* v_reuseFailAlloc_6174_; 
v_reuseFailAlloc_6174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6174_, 0, v___x_6171_);
v___x_6173_ = v_reuseFailAlloc_6174_;
goto v_reusejp_6172_;
}
v_reusejp_6172_:
{
return v___x_6173_;
}
}
}
}
else
{
lean_dec(v_val_6146_);
lean_dec(v_pre_6138_);
lean_dec_ref_known(v_name_6126_, 2);
lean_dec(v___x_6125_);
goto v___jp_6130_;
}
}
else
{
lean_dec(v___x_6145_);
lean_dec_ref_known(v_name_6126_, 2);
lean_dec(v_pre_6138_);
lean_dec(v___x_6125_);
goto v___jp_6130_;
}
}
}
else
{
lean_dec(v_name_6126_);
lean_dec(v___x_6125_);
goto v___jp_6134_;
}
v___jp_6130_:
{
uint8_t v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; 
v___x_6131_ = 0;
v___x_6132_ = lean_box(v___x_6131_);
v___x_6133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6132_);
return v___x_6133_;
}
v___jp_6134_:
{
uint8_t v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; 
v___x_6135_ = 0;
v___x_6136_ = lean_box(v___x_6135_);
v___x_6137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6137_, 0, v___x_6136_);
return v___x_6137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6198_, lean_object* v_name_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_){
_start:
{
lean_object* v_res_6203_; 
v_res_6203_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6198_, v_name_6199_, v___y_6200_, v___y_6201_);
lean_dec(v___y_6201_);
lean_dec_ref(v___y_6200_);
return v_res_6203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6207_; lean_object* v___x_6208_; 
v___f_6207_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6208_ = l_Lean_registerReservedNameAction(v___f_6207_);
return v___x_6208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6209_){
_start:
{
lean_object* v_res_6210_; 
v_res_6210_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6210_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Injective(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_genInjectivity = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_genInjectivity);
lean_dec_ref(res);
res = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Injective(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Injective(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Injective(builtin);
}
#ifdef __cplusplus
}
#endif
