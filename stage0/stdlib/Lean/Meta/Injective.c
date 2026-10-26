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
lean_object* v___y_255_; lean_object* v___y_265_; uint8_t v___y_266_; lean_object* v___y_267_; uint16_t v___y_268_; uint8_t v___y_269_; uint8_t v___y_270_; lean_object* v___y_271_; lean_object* v_toCold_276_; lean_object* v_currRecDepth_277_; lean_object* v_ref_278_; uint16_t v_optionFlags_279_; uint8_t v_suppressElabErrors_280_; uint8_t v_checkDeprecated_281_; uint8_t v_isRecordingDeps_282_; lean_object* v_maxRecDepth_283_; lean_object* v_cancelTk_x3f_284_; 
v_toCold_276_ = lean_ctor_get(v___y_251_, 0);
v_currRecDepth_277_ = lean_ctor_get(v___y_251_, 1);
v_ref_278_ = lean_ctor_get(v___y_251_, 2);
v_optionFlags_279_ = lean_ctor_get_uint16(v___y_251_, sizeof(void*)*3);
v_suppressElabErrors_280_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 2);
v_checkDeprecated_281_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 3);
v_isRecordingDeps_282_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 4);
v_maxRecDepth_283_ = lean_ctor_get(v_toCold_276_, 3);
v_cancelTk_x3f_284_ = lean_ctor_get(v_toCold_276_, 10);
if (lean_obj_tag(v_cancelTk_x3f_284_) == 1)
{
lean_object* v_val_290_; uint8_t v___x_291_; 
v_val_290_ = lean_ctor_get(v_cancelTk_x3f_284_, 0);
v___x_291_ = l_IO_CancelToken_isSet(v_val_290_);
if (v___x_291_ == 0)
{
goto v___jp_285_;
}
else
{
lean_object* v___x_292_; lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec_ref(v_x_249_);
v___x_292_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
goto v___jp_285_;
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
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v___y_271_, v___x_272_);
lean_inc_ref(v___y_265_);
v___x_274_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_274_, 0, v___y_265_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_ctor_set(v___x_274_, 2, v___y_267_);
lean_ctor_set_uint16(v___x_274_, sizeof(void*)*3, v___y_268_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*3 + 2, v___y_266_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*3 + 3, v___y_270_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*3 + 4, v___y_269_);
lean_inc(v___y_252_);
lean_inc(v___y_250_);
v___x_275_ = lean_apply_4(v_x_249_, v___y_250_, v___x_274_, v___y_252_, lean_box(0));
v___y_255_ = v___x_275_;
goto v___jp_254_;
}
v___jp_285_:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_nat_dec_eq(v_maxRecDepth_283_, v___x_286_);
if (v___x_287_ == 0)
{
uint8_t v___x_288_; 
v___x_288_ = lean_nat_dec_eq(v_currRecDepth_277_, v_maxRecDepth_283_);
if (v___x_288_ == 0)
{
lean_inc(v_ref_278_);
v___y_265_ = v_toCold_276_;
v___y_266_ = v_suppressElabErrors_280_;
v___y_267_ = v_ref_278_;
v___y_268_ = v_optionFlags_279_;
v___y_269_ = v_isRecordingDeps_282_;
v___y_270_ = v_checkDeprecated_281_;
v___y_271_ = v_currRecDepth_277_;
goto v___jp_264_;
}
else
{
lean_object* v___x_289_; 
lean_dec_ref(v_x_249_);
lean_inc(v_ref_278_);
v___x_289_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_278_);
v___y_255_ = v___x_289_;
goto v___jp_254_;
}
}
else
{
lean_inc(v_ref_278_);
v___y_265_ = v_toCold_276_;
v___y_266_ = v_suppressElabErrors_280_;
v___y_267_ = v_ref_278_;
v___y_268_ = v_optionFlags_279_;
v___y_269_ = v_isRecordingDeps_282_;
v___y_270_ = v_checkDeprecated_281_;
v___y_271_ = v_currRecDepth_277_;
goto v___jp_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_307_, lean_object* v_x_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_apply_1(v_x_308_, lean_box(0));
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_314_, lean_object* v_x_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_314_, v_x_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v_key_323_; lean_object* v_value_324_; lean_object* v_tail_325_; uint8_t v___x_326_; 
v_key_323_ = lean_ctor_get(v_x_321_, 0);
v_value_324_ = lean_ctor_get(v_x_321_, 1);
v_tail_325_ = lean_ctor_get(v_x_321_, 2);
v___x_326_ = l_Lean_ExprStructEq_beq(v_key_323_, v_a_320_);
if (v___x_326_ == 0)
{
v_x_321_ = v_tail_325_;
goto _start;
}
else
{
lean_object* v___x_328_; 
lean_inc(v_value_324_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_value_324_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_329_, v_x_330_);
lean_dec(v_x_330_);
lean_dec_ref(v_a_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_buckets_334_; lean_object* v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v_fold_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_buckets_334_ = lean_ctor_get(v_m_332_, 1);
v___x_335_ = lean_array_get_size(v_buckets_334_);
v___x_336_ = l_Lean_ExprStructEq_hash(v_a_333_);
v___x_337_ = 32ULL;
v___x_338_ = lean_uint64_shift_right(v___x_336_, v___x_337_);
v_fold_339_ = lean_uint64_xor(v___x_336_, v___x_338_);
v___x_340_ = 16ULL;
v___x_341_ = lean_uint64_shift_right(v_fold_339_, v___x_340_);
v___x_342_ = lean_uint64_xor(v_fold_339_, v___x_341_);
v___x_343_ = lean_uint64_to_usize(v___x_342_);
v___x_344_ = lean_usize_of_nat(v___x_335_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_sub(v___x_344_, v___x_345_);
v___x_347_ = lean_usize_land(v___x_343_, v___x_346_);
v___x_348_ = lean_array_uget_borrowed(v_buckets_334_, v___x_347_);
v___x_349_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_333_, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_350_, v_a_351_);
lean_dec_ref(v_a_351_);
lean_dec_ref(v_m_350_);
return v_res_352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_354_; lean_object* v_dummy_355_; 
v___x_354_ = lean_box(0);
v_dummy_355_ = l_Lean_Expr_sort___override(v___x_354_);
return v_dummy_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_356_, lean_object* v_post_357_, size_t v_sz_358_, size_t v_i_359_, lean_object* v_bs_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec_ref(v_post_357_);
lean_dec_ref(v_pre_356_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_bs_360_);
return v___x_366_;
}
else
{
lean_object* v_v_367_; lean_object* v___x_368_; lean_object* v_bs_x27_369_; lean_object* v___x_370_; 
v_v_367_ = lean_array_uget(v_bs_360_, v_i_359_);
v___x_368_ = lean_unsigned_to_nat(0u);
v_bs_x27_369_ = lean_array_uset(v_bs_360_, v_i_359_, v___x_368_);
lean_inc_ref(v_post_357_);
lean_inc_ref(v_pre_356_);
v___x_370_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_356_, v_post_357_, v_v_367_, v___y_361_, v___y_362_, v___y_363_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_add(v_i_359_, v___x_372_);
v___x_374_ = lean_array_uset(v_bs_x27_369_, v_i_359_, v_a_371_);
v_i_359_ = v___x_373_;
v_bs_360_ = v___x_374_;
goto _start;
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref(v_bs_x27_369_);
lean_dec_ref(v_post_357_);
lean_dec_ref(v_pre_356_);
v_a_376_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_370_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_370_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_384_, lean_object* v_post_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
if (lean_obj_tag(v_x_386_) == 5)
{
lean_object* v_fn_393_; lean_object* v_arg_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_fn_393_ = lean_ctor_get(v_x_386_, 0);
lean_inc_ref(v_fn_393_);
v_arg_394_ = lean_ctor_get(v_x_386_, 1);
lean_inc_ref(v_arg_394_);
lean_dec_ref_known(v_x_386_, 2);
v___x_395_ = lean_array_set(v_x_387_, v_x_388_, v_arg_394_);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_sub(v_x_388_, v___x_396_);
lean_dec(v_x_388_);
v_x_386_ = v_fn_393_;
v_x_387_ = v___x_395_;
v_x_388_ = v___x_397_;
goto _start;
}
else
{
lean_object* v___x_399_; 
lean_dec(v_x_388_);
lean_inc_ref(v_post_385_);
lean_inc_ref(v_pre_384_);
v___x_399_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_384_, v_post_385_, v_x_386_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; size_t v_sz_401_; size_t v___x_402_; lean_object* v___x_403_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v_sz_401_ = lean_array_size(v_x_387_);
v___x_402_ = ((size_t)0ULL);
lean_inc_ref(v_post_385_);
lean_inc_ref(v_pre_384_);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_384_, v_post_385_, v_sz_401_, v___x_402_, v_x_387_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v___x_405_ = l_Lean_mkAppN(v_a_400_, v_a_404_);
lean_dec(v_a_404_);
v___x_406_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_384_, v_post_385_, v___x_405_, v___y_389_, v___y_390_, v___y_391_);
return v___x_406_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_a_400_);
lean_dec_ref(v_post_385_);
lean_dec_ref(v_pre_384_);
v_a_407_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_403_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_403_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_dec_ref(v_x_387_);
lean_dec_ref(v_post_385_);
lean_dec_ref(v_pre_384_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_415_, lean_object* v_pre_416_, lean_object* v_e_417_, lean_object* v_post_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Core_checkSystem(v___x_415_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_424_; 
lean_dec_ref_known(v___x_423_, 1);
lean_inc_ref(v_pre_416_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
lean_inc_ref(v_e_417_);
v___x_424_ = lean_apply_4(v_pre_416_, v_e_417_, v___y_420_, v___y_421_, lean_box(0));
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_540_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_540_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_540_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_540_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___y_430_; 
switch(lean_obj_tag(v_a_425_))
{
case 0:
{
lean_object* v_e_530_; lean_object* v___x_532_; 
lean_dec_ref(v_post_418_);
lean_dec_ref(v_e_417_);
lean_dec_ref(v_pre_416_);
v_e_530_ = lean_ctor_get(v_a_425_, 0);
lean_inc_ref(v_e_530_);
lean_dec_ref_known(v_a_425_, 1);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v_e_530_);
v___x_532_ = v___x_427_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_e_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
case 1:
{
lean_object* v_e_534_; lean_object* v___x_535_; 
lean_del_object(v___x_427_);
lean_dec_ref(v_e_417_);
v_e_534_ = lean_ctor_get(v_a_425_, 0);
lean_inc_ref(v_e_534_);
lean_dec_ref_known(v_a_425_, 1);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_535_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_e_534_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_537_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_535_, 1);
v___x_537_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v_a_536_, v___y_419_, v___y_420_, v___y_421_);
return v___x_537_;
}
else
{
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_535_;
}
}
default: 
{
lean_object* v_e_x3f_538_; 
lean_del_object(v___x_427_);
v_e_x3f_538_ = lean_ctor_get(v_a_425_, 0);
lean_inc(v_e_x3f_538_);
lean_dec_ref_known(v_a_425_, 1);
if (lean_obj_tag(v_e_x3f_538_) == 0)
{
v___y_430_ = v_e_417_;
goto v___jp_429_;
}
else
{
lean_object* v_val_539_; 
lean_dec_ref(v_e_417_);
v_val_539_ = lean_ctor_get(v_e_x3f_538_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v_e_x3f_538_, 1);
v___y_430_ = v_val_539_;
goto v___jp_429_;
}
}
}
v___jp_429_:
{
switch(lean_obj_tag(v___y_430_))
{
case 7:
{
lean_object* v_binderName_431_; lean_object* v_binderType_432_; lean_object* v_body_433_; uint8_t v_binderInfo_434_; lean_object* v___x_435_; 
v_binderName_431_ = lean_ctor_get(v___y_430_, 0);
v_binderType_432_ = lean_ctor_get(v___y_430_, 1);
v_body_433_ = lean_ctor_get(v___y_430_, 2);
v_binderInfo_434_ = lean_ctor_get_uint8(v___y_430_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_432_);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_binderType_432_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
lean_inc_ref(v_body_433_);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_437_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_body_433_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; size_t v___x_439_; size_t v___x_440_; uint8_t v___x_441_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = lean_ptr_addr(v_binderType_432_);
v___x_440_ = lean_ptr_addr(v_a_436_);
v___x_441_ = lean_usize_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_inc(v_binderName_431_);
lean_dec_ref_known(v___y_430_, 3);
v___x_442_ = l_Lean_Expr_forallE___override(v_binderName_431_, v_a_436_, v_a_438_, v_binderInfo_434_);
v___x_443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_442_, v___y_419_, v___y_420_, v___y_421_);
return v___x_443_;
}
else
{
size_t v___x_444_; size_t v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_ptr_addr(v_body_433_);
v___x_445_ = lean_ptr_addr(v_a_438_);
v___x_446_ = lean_usize_dec_eq(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_inc(v_binderName_431_);
lean_dec_ref_known(v___y_430_, 3);
v___x_447_ = l_Lean_Expr_forallE___override(v_binderName_431_, v_a_436_, v_a_438_, v_binderInfo_434_);
v___x_448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_447_, v___y_419_, v___y_420_, v___y_421_);
return v___x_448_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_434_, v_binderInfo_434_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_inc(v_binderName_431_);
lean_dec_ref_known(v___y_430_, 3);
v___x_450_ = l_Lean_Expr_forallE___override(v_binderName_431_, v_a_436_, v_a_438_, v_binderInfo_434_);
v___x_451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_450_, v___y_419_, v___y_420_, v___y_421_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; 
lean_dec(v_a_438_);
lean_dec(v_a_436_);
v___x_452_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___y_430_, v___y_419_, v___y_420_, v___y_421_);
return v___x_452_;
}
}
}
}
else
{
lean_dec(v_a_436_);
lean_dec_ref_known(v___y_430_, 3);
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_437_;
}
}
else
{
lean_dec_ref_known(v___y_430_, 3);
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_435_;
}
}
case 6:
{
lean_object* v_binderName_453_; lean_object* v_binderType_454_; lean_object* v_body_455_; uint8_t v_binderInfo_456_; lean_object* v___x_457_; 
v_binderName_453_ = lean_ctor_get(v___y_430_, 0);
v_binderType_454_ = lean_ctor_get(v___y_430_, 1);
v_body_455_ = lean_ctor_get(v___y_430_, 2);
v_binderInfo_456_ = lean_ctor_get_uint8(v___y_430_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_454_);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_binderType_454_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
lean_inc_ref(v_body_455_);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_body_455_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; size_t v___x_461_; size_t v___x_462_; uint8_t v___x_463_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = lean_ptr_addr(v_binderType_454_);
v___x_462_ = lean_ptr_addr(v_a_458_);
v___x_463_ = lean_usize_dec_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_inc(v_binderName_453_);
lean_dec_ref_known(v___y_430_, 3);
v___x_464_ = l_Lean_Expr_lam___override(v_binderName_453_, v_a_458_, v_a_460_, v_binderInfo_456_);
v___x_465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_464_, v___y_419_, v___y_420_, v___y_421_);
return v___x_465_;
}
else
{
size_t v___x_466_; size_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_ptr_addr(v_body_455_);
v___x_467_ = lean_ptr_addr(v_a_460_);
v___x_468_ = lean_usize_dec_eq(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_inc(v_binderName_453_);
lean_dec_ref_known(v___y_430_, 3);
v___x_469_ = l_Lean_Expr_lam___override(v_binderName_453_, v_a_458_, v_a_460_, v_binderInfo_456_);
v___x_470_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_469_, v___y_419_, v___y_420_, v___y_421_);
return v___x_470_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_456_, v_binderInfo_456_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_inc(v_binderName_453_);
lean_dec_ref_known(v___y_430_, 3);
v___x_472_ = l_Lean_Expr_lam___override(v_binderName_453_, v_a_458_, v_a_460_, v_binderInfo_456_);
v___x_473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_472_, v___y_419_, v___y_420_, v___y_421_);
return v___x_473_;
}
else
{
lean_object* v___x_474_; 
lean_dec(v_a_460_);
lean_dec(v_a_458_);
v___x_474_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___y_430_, v___y_419_, v___y_420_, v___y_421_);
return v___x_474_;
}
}
}
}
else
{
lean_dec(v_a_458_);
lean_dec_ref_known(v___y_430_, 3);
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_459_;
}
}
else
{
lean_dec_ref_known(v___y_430_, 3);
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_457_;
}
}
case 8:
{
lean_object* v_declName_475_; lean_object* v_type_476_; lean_object* v_value_477_; lean_object* v_body_478_; uint8_t v_nondep_479_; lean_object* v___x_480_; 
v_declName_475_ = lean_ctor_get(v___y_430_, 0);
v_type_476_ = lean_ctor_get(v___y_430_, 1);
v_value_477_ = lean_ctor_get(v___y_430_, 2);
v_body_478_ = lean_ctor_get(v___y_430_, 3);
v_nondep_479_ = lean_ctor_get_uint8(v___y_430_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_476_);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_type_476_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
lean_inc_ref(v_value_477_);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_482_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_value_477_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
lean_inc_ref(v_body_478_);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_484_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_body_478_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; size_t v___x_486_; size_t v___x_487_; uint8_t v___x_488_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v___x_486_ = lean_ptr_addr(v_type_476_);
v___x_487_ = lean_ptr_addr(v_a_481_);
v___x_488_ = lean_usize_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_inc(v_declName_475_);
lean_dec_ref_known(v___y_430_, 4);
v___x_489_ = l_Lean_Expr_letE___override(v_declName_475_, v_a_481_, v_a_483_, v_a_485_, v_nondep_479_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_489_, v___y_419_, v___y_420_, v___y_421_);
return v___x_490_;
}
else
{
size_t v___x_491_; size_t v___x_492_; uint8_t v___x_493_; 
v___x_491_ = lean_ptr_addr(v_value_477_);
v___x_492_ = lean_ptr_addr(v_a_483_);
v___x_493_ = lean_usize_dec_eq(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_inc(v_declName_475_);
lean_dec_ref_known(v___y_430_, 4);
v___x_494_ = l_Lean_Expr_letE___override(v_declName_475_, v_a_481_, v_a_483_, v_a_485_, v_nondep_479_);
v___x_495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_494_, v___y_419_, v___y_420_, v___y_421_);
return v___x_495_;
}
else
{
size_t v___x_496_; size_t v___x_497_; uint8_t v___x_498_; 
v___x_496_ = lean_ptr_addr(v_body_478_);
v___x_497_ = lean_ptr_addr(v_a_485_);
v___x_498_ = lean_usize_dec_eq(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_inc(v_declName_475_);
lean_dec_ref_known(v___y_430_, 4);
v___x_499_ = l_Lean_Expr_letE___override(v_declName_475_, v_a_481_, v_a_483_, v_a_485_, v_nondep_479_);
v___x_500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_499_, v___y_419_, v___y_420_, v___y_421_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; 
lean_dec(v_a_485_);
lean_dec(v_a_483_);
lean_dec(v_a_481_);
v___x_501_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___y_430_, v___y_419_, v___y_420_, v___y_421_);
return v___x_501_;
}
}
}
}
else
{
lean_dec(v_a_483_);
lean_dec(v_a_481_);
lean_dec_ref_known(v___y_430_, 4);
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_484_;
}
}
else
{
lean_dec(v_a_481_);
lean_dec_ref_known(v___y_430_, 4);
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_482_;
}
}
else
{
lean_dec_ref_known(v___y_430_, 4);
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_480_;
}
}
case 5:
{
lean_object* v_dummy_502_; lean_object* v_nargs_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_dummy_502_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_503_ = l_Lean_Expr_getAppNumArgs(v___y_430_);
lean_inc(v_nargs_503_);
v___x_504_ = lean_mk_array(v_nargs_503_, v_dummy_502_);
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_sub(v_nargs_503_, v___x_505_);
lean_dec(v_nargs_503_);
v___x_507_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_416_, v_post_418_, v___y_430_, v___x_504_, v___x_506_, v___y_419_, v___y_420_, v___y_421_);
return v___x_507_;
}
case 10:
{
lean_object* v_data_508_; lean_object* v_expr_509_; lean_object* v___x_510_; 
v_data_508_ = lean_ctor_get(v___y_430_, 0);
v_expr_509_ = lean_ctor_get(v___y_430_, 1);
lean_inc_ref(v_expr_509_);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_510_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_expr_509_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; size_t v___x_512_; size_t v___x_513_; uint8_t v___x_514_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = lean_ptr_addr(v_expr_509_);
v___x_513_ = lean_ptr_addr(v_a_511_);
v___x_514_ = lean_usize_dec_eq(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_inc(v_data_508_);
lean_dec_ref_known(v___y_430_, 2);
v___x_515_ = l_Lean_Expr_mdata___override(v_data_508_, v_a_511_);
v___x_516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_515_, v___y_419_, v___y_420_, v___y_421_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; 
lean_dec(v_a_511_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___y_430_, v___y_419_, v___y_420_, v___y_421_);
return v___x_517_;
}
}
else
{
lean_dec_ref_known(v___y_430_, 2);
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_510_;
}
}
case 11:
{
lean_object* v_typeName_518_; lean_object* v_idx_519_; lean_object* v_struct_520_; lean_object* v___x_521_; 
v_typeName_518_ = lean_ctor_get(v___y_430_, 0);
v_idx_519_ = lean_ctor_get(v___y_430_, 1);
v_struct_520_ = lean_ctor_get(v___y_430_, 2);
lean_inc_ref(v_struct_520_);
lean_inc_ref(v_post_418_);
lean_inc_ref(v_pre_416_);
v___x_521_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_416_, v_post_418_, v_struct_520_, v___y_419_, v___y_420_, v___y_421_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = lean_ptr_addr(v_struct_520_);
v___x_524_ = lean_ptr_addr(v_a_522_);
v___x_525_ = lean_usize_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_inc(v_idx_519_);
lean_inc(v_typeName_518_);
lean_dec_ref_known(v___y_430_, 3);
v___x_526_ = l_Lean_Expr_proj___override(v_typeName_518_, v_idx_519_, v_a_522_);
v___x_527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___x_526_, v___y_419_, v___y_420_, v___y_421_);
return v___x_527_;
}
else
{
lean_object* v___x_528_; 
lean_dec(v_a_522_);
v___x_528_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___y_430_, v___y_419_, v___y_420_, v___y_421_);
return v___x_528_;
}
}
else
{
lean_dec_ref_known(v___y_430_, 3);
lean_dec_ref(v_post_418_);
lean_dec_ref(v_pre_416_);
return v___x_521_;
}
}
default: 
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_416_, v_post_418_, v___y_430_, v___y_419_, v___y_420_, v___y_421_);
return v___x_529_;
}
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_post_418_);
lean_dec_ref(v_e_417_);
lean_dec_ref(v_pre_416_);
v_a_541_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_424_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_424_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
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
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v_post_418_);
lean_dec_ref(v_e_417_);
lean_dec_ref(v_pre_416_);
v_a_549_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_423_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_423_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_557_, lean_object* v_pre_558_, lean_object* v_e_559_, lean_object* v_post_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_557_, v_pre_558_, v_e_559_, v_post_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_566_, lean_object* v_post_567_, lean_object* v_e_568_, lean_object* v_a_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_inc(v_a_569_);
v___x_573_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_573_, 0, lean_box(0));
lean_closure_set(v___x_573_, 1, lean_box(0));
lean_closure_set(v___x_573_, 2, v_a_569_);
v___x_574_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_573_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_606_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_606_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_606_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_606_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_575_, v_e_568_);
lean_dec(v_a_575_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_580_; lean_object* v___f_581_; lean_object* v___x_582_; 
lean_del_object(v___x_577_);
v___x_580_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_568_);
v___f_581_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_581_, 0, v___x_580_);
lean_closure_set(v___f_581_, 1, v_pre_566_);
lean_closure_set(v___f_581_, 2, v_e_568_);
lean_closure_set(v___f_581_, 3, v_post_567_);
v___x_582_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_581_, v_a_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc_n(v_a_583_, 2);
lean_dec_ref_known(v___x_582_, 1);
lean_inc(v_a_569_);
v___f_584_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_584_, 0, v_a_569_);
lean_closure_set(v___f_584_, 1, v_e_568_);
lean_closure_set(v___f_584_, 2, v_a_583_);
v___x_585_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_584_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_585_, 0);
lean_dec(v_unused_593_);
v___x_587_ = v___x_585_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_dec(v___x_585_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v_a_583_);
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_583_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_a_583_);
v_a_594_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_585_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_585_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_dec_ref(v_e_568_);
return v___x_582_;
}
}
else
{
lean_object* v_val_602_; lean_object* v___x_604_; 
lean_dec_ref(v_e_568_);
lean_dec_ref(v_post_567_);
lean_dec_ref(v_pre_566_);
v_val_602_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v___x_579_, 1);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v_val_602_);
v___x_604_ = v___x_577_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_val_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_e_568_);
lean_dec_ref(v_post_567_);
lean_dec_ref(v_pre_566_);
v_a_607_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_574_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_574_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_615_, lean_object* v_post_616_, lean_object* v_e_617_, lean_object* v_a_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
lean_inc_ref(v_post_616_);
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc_ref(v_e_617_);
v___x_622_ = lean_apply_4(v_post_616_, v_e_617_, v___y_619_, v___y_620_, lean_box(0));
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_641_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_641_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_641_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_641_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
switch(lean_obj_tag(v_a_623_))
{
case 0:
{
lean_object* v_e_627_; lean_object* v___x_629_; 
lean_dec_ref(v_e_617_);
lean_dec_ref(v_post_616_);
lean_dec_ref(v_pre_615_);
v_e_627_ = lean_ctor_get(v_a_623_, 0);
lean_inc_ref(v_e_627_);
lean_dec_ref_known(v_a_623_, 1);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_e_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_e_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
case 1:
{
lean_object* v_e_631_; lean_object* v___x_632_; 
lean_del_object(v___x_625_);
lean_dec_ref(v_e_617_);
v_e_631_ = lean_ctor_get(v_a_623_, 0);
lean_inc_ref(v_e_631_);
lean_dec_ref_known(v_a_623_, 1);
v___x_632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_615_, v_post_616_, v_e_631_, v_a_618_, v___y_619_, v___y_620_);
return v___x_632_;
}
default: 
{
lean_object* v_e_x3f_633_; 
lean_dec_ref(v_post_616_);
lean_dec_ref(v_pre_615_);
v_e_x3f_633_ = lean_ctor_get(v_a_623_, 0);
lean_inc(v_e_x3f_633_);
lean_dec_ref_known(v_a_623_, 1);
if (lean_obj_tag(v_e_x3f_633_) == 0)
{
lean_object* v___x_635_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_e_617_);
v___x_635_ = v___x_625_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_e_617_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
else
{
lean_object* v_val_637_; lean_object* v___x_639_; 
lean_dec_ref(v_e_617_);
v_val_637_ = lean_ctor_get(v_e_x3f_633_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v_e_x3f_633_, 1);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v_val_637_);
v___x_639_ = v___x_625_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_val_637_);
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
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec_ref(v_e_617_);
lean_dec_ref(v_post_616_);
lean_dec_ref(v_pre_615_);
v_a_642_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_622_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_622_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_650_, lean_object* v_post_651_, lean_object* v_e_652_, lean_object* v_a_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_650_, v_post_651_, v_e_652_, v_a_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v_a_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_658_, lean_object* v_post_659_, lean_object* v_sz_660_, lean_object* v_i_661_, lean_object* v_bs_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
size_t v_sz_boxed_667_; size_t v_i_boxed_668_; lean_object* v_res_669_; 
v_sz_boxed_667_ = lean_unbox_usize(v_sz_660_);
lean_dec(v_sz_660_);
v_i_boxed_668_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_658_, v_post_659_, v_sz_boxed_667_, v_i_boxed_668_, v_bs_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_670_, lean_object* v_post_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_670_, v_post_671_, v_x_672_, v_x_673_, v_x_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_680_, lean_object* v_post_681_, lean_object* v_e_682_, lean_object* v_a_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_680_, v_post_681_, v_e_682_, v_a_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v_a_683_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_688_, lean_object* v_x_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_apply_1(v_x_689_, lean_box(0));
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_695_, lean_object* v_x_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_695_, v_x_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
return v_res_700_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_box(0);
v___x_702_ = lean_unsigned_to_nat(16u);
v___x_703_ = lean_mk_array(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_708_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_708_, 0, lean_box(0));
lean_closure_set(v___x_708_, 1, lean_box(0));
lean_closure_set(v___x_708_, 2, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_709_, lean_object* v_pre_710_, lean_object* v_post_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v___x_718_; 
v___x_715_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_716_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_715_, v___y_712_, v___y_713_);
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref(v___x_716_);
v___x_718_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_710_, v_post_711_, v_input_709_, v_a_717_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_720_, 0, lean_box(0));
lean_closure_set(v___x_720_, 1, lean_box(0));
lean_closure_set(v___x_720_, 2, v_a_717_);
v___x_721_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_720_, v___y_712_, v___y_713_);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_721_, 0);
lean_dec(v_unused_729_);
v___x_723_ = v___x_721_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_dec(v___x_721_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v_a_719_);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_719_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
lean_dec(v_a_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_730_, lean_object* v_pre_731_, lean_object* v_post_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_730_, v_pre_731_, v_post_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___x_745_; 
v___f_743_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_744_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_745_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_739_, v___f_743_, v___f_744_, v_a_740_, v_a_741_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Meta_elimOptParam(v_type_746_, v_a_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_751_, lean_object* v_m_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_752_, v_a_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_755_, lean_object* v_m_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_755_, v_m_756_, v_a_757_);
lean_dec_ref(v_a_757_);
lean_dec_ref(v_m_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_759_, lean_object* v_ref_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_760_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_765_, lean_object* v_ref_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_765_, v_ref_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_781_, lean_object* v_x_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_788_, lean_object* v_x_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_788_, v_x_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_795_, lean_object* v_m_796_, lean_object* v_a_797_, lean_object* v_b_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_796_, v_a_797_, v_b_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_800_, lean_object* v_a_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_804_, lean_object* v_a_805_, lean_object* v_x_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_804_, v_a_805_, v_x_806_);
lean_dec(v_x_806_);
lean_dec_ref(v_a_805_);
return v_res_807_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_808_, lean_object* v_a_809_, lean_object* v_x_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_812_, lean_object* v_a_813_, lean_object* v_x_814_){
_start:
{
uint8_t v_res_815_; lean_object* v_r_816_; 
v_res_815_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_812_, v_a_813_, v_x_814_);
lean_dec(v_x_814_);
lean_dec_ref(v_a_813_);
v_r_816_ = lean_box(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_817_, lean_object* v_data_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_820_, lean_object* v_a_821_, lean_object* v_b_822_, lean_object* v_x_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_821_, v_b_822_, v_x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_825_, lean_object* v_i_826_, lean_object* v_source_827_, lean_object* v_target_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_826_, v_source_827_, v_target_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_834_, lean_object* v_as_835_, size_t v_sz_836_, size_t v_i_837_, lean_object* v_b_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_a_845_; uint8_t v___x_849_; 
v___x_849_ = lean_usize_dec_lt(v_i_837_, v_sz_836_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v_b_838_);
return v___x_850_;
}
else
{
lean_object* v_snd_851_; lean_object* v_fst_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_930_; 
v_snd_851_ = lean_ctor_get(v_b_838_, 1);
v_fst_852_ = lean_ctor_get(v_b_838_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_b_838_);
if (v_isSharedCheck_930_ == 0)
{
v___x_854_ = v_b_838_;
v_isShared_855_ = v_isSharedCheck_930_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snd_851_);
lean_inc(v_fst_852_);
lean_dec(v_b_838_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_930_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_array_856_; lean_object* v_start_857_; lean_object* v_stop_858_; uint8_t v___x_859_; 
v_array_856_ = lean_ctor_get(v_snd_851_, 0);
v_start_857_ = lean_ctor_get(v_snd_851_, 1);
v_stop_858_ = lean_ctor_get(v_snd_851_, 2);
v___x_859_ = lean_nat_dec_lt(v_start_857_, v_stop_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_861_; 
if (v_isShared_855_ == 0)
{
v___x_861_ = v___x_854_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_fst_852_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_snd_851_);
v___x_861_ = v_reuseFailAlloc_863_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; 
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
else
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_926_; 
lean_inc(v_stop_858_);
lean_inc(v_start_857_);
lean_inc_ref(v_array_856_);
v_isSharedCheck_926_ = !lean_is_exclusive(v_snd_851_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_927_ = lean_ctor_get(v_snd_851_, 2);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_snd_851_, 1);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_snd_851_, 0);
lean_dec(v_unused_929_);
v___x_865_ = v_snd_851_;
v_isShared_866_ = v_isSharedCheck_926_;
goto v_resetjp_864_;
}
else
{
lean_dec(v_snd_851_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_926_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v_a_867_ = lean_array_uget_borrowed(v_as_835_, v_i_837_);
v___x_868_ = lean_array_fget(v_array_856_, v_start_857_);
v___x_869_ = lean_unsigned_to_nat(1u);
v___x_870_ = lean_nat_add(v_start_857_, v___x_869_);
lean_dec(v_start_857_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v___x_870_);
v___x_872_ = v___x_865_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_array_856_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_stop_858_);
v___x_872_ = v_reuseFailAlloc_925_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; 
lean_inc(v___y_842_);
lean_inc_ref(v___y_841_);
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v_a_867_);
v___x_873_ = lean_infer_type(v_a_867_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_873_) == 0)
{
if (v_skipIfPropOrEq_834_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref_known(v___x_873_, 1);
lean_inc(v_a_867_);
v___x_874_ = l_Lean_Meta_mkEqHEq(v_a_867_, v___x_868_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = lean_array_push(v_fst_852_, v_a_875_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_872_);
lean_ctor_set(v___x_854_, 0, v___x_876_);
v___x_878_ = v___x_854_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_872_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
v_a_845_ = v___x_878_;
goto v___jp_844_;
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v___x_872_);
lean_del_object(v___x_854_);
lean_dec(v_fst_852_);
v_a_880_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_874_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_874_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_873_, 1);
v___x_889_ = l_Lean_Meta_isProp(v_a_888_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; uint8_t v___x_895_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_895_ = lean_unbox(v_a_890_);
lean_dec(v_a_890_);
if (v___x_895_ == 0)
{
uint8_t v___x_896_; 
v___x_896_ = lean_expr_eqv(v_a_867_, v___x_868_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_del_object(v___x_854_);
lean_inc(v_a_867_);
v___x_897_ = l_Lean_Meta_mkEqHEq(v_a_867_, v___x_868_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = lean_array_push(v_fst_852_, v_a_898_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_872_);
v_a_845_ = v___x_900_;
goto v___jp_844_;
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v___x_872_);
lean_dec(v_fst_852_);
v_a_901_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_897_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_897_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_dec(v___x_868_);
goto v___jp_891_;
}
}
else
{
lean_dec(v___x_868_);
goto v___jp_891_;
}
v___jp_891_:
{
lean_object* v___x_893_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_872_);
v___x_893_ = v___x_854_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_fst_852_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_872_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
v_a_845_ = v___x_893_;
goto v___jp_844_;
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v___x_872_);
lean_dec(v___x_868_);
lean_del_object(v___x_854_);
lean_dec(v_fst_852_);
v_a_909_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_889_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_889_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v___x_872_);
lean_dec(v___x_868_);
lean_del_object(v___x_854_);
lean_dec(v_fst_852_);
v_a_917_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_873_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_873_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
}
}
v___jp_844_:
{
size_t v___x_846_; size_t v___x_847_; 
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_i_837_, v___x_846_);
v_i_837_ = v___x_847_;
v_b_838_ = v_a_845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_931_, lean_object* v_as_932_, lean_object* v_sz_933_, lean_object* v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_941_; size_t v_sz_boxed_942_; size_t v_i_boxed_943_; lean_object* v_res_944_; 
v_skipIfPropOrEq_boxed_941_ = lean_unbox(v_skipIfPropOrEq_931_);
v_sz_boxed_942_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_943_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_941_, v_as_932_, v_sz_boxed_942_, v_i_boxed_943_, v_b_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec_ref(v_as_932_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_947_, lean_object* v_args2_948_, uint8_t v_skipIfPropOrEq_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_eqs_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; size_t v_sz_960_; size_t v___x_961_; lean_object* v___x_962_; 
v___x_955_ = lean_unsigned_to_nat(0u);
v_eqs_956_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_957_ = lean_array_get_size(v_args2_948_);
v___x_958_ = l_Array_toSubarray___redArg(v_args2_948_, v___x_955_, v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v_eqs_956_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v_sz_960_ = lean_array_size(v_args1_947_);
v___x_961_ = ((size_t)0ULL);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_949_, v_args1_947_, v_sz_960_, v___x_961_, v___x_959_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_971_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_971_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_fst_967_; lean_object* v___x_969_; 
v_fst_967_ = lean_ctor_get(v_a_963_, 0);
lean_inc(v_fst_967_);
lean_dec(v_a_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v_fst_967_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_fst_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_a_972_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_962_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_962_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_980_, lean_object* v_args2_981_, lean_object* v_skipIfPropOrEq_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_988_; lean_object* v_res_989_; 
v_skipIfPropOrEq_boxed_988_ = lean_unbox(v_skipIfPropOrEq_982_);
v_res_989_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_980_, v_args2_981_, v_skipIfPropOrEq_boxed_988_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec_ref(v_args1_980_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_990_, lean_object* v_b_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
v___x_997_ = lean_apply_6(v_k_990_, v_b_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, lean_box(0));
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_998_, lean_object* v_b_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_998_, v_b_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1006_, uint8_t v_bi_1007_, lean_object* v_type_1008_, lean_object* v_k_1009_, uint8_t v_kind_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___f_1016_; lean_object* v___x_1017_; 
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1016_, 0, v_k_1009_);
v___x_1017_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1006_, v_bi_1007_, v_type_1008_, v___f_1016_, v_kind_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1017_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1017_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1034_, lean_object* v_bi_1035_, lean_object* v_type_1036_, lean_object* v_k_1037_, lean_object* v_kind_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
uint8_t v_bi_boxed_1044_; uint8_t v_kind_boxed_1045_; lean_object* v_res_1046_; 
v_bi_boxed_1044_ = lean_unbox(v_bi_1035_);
v_kind_boxed_1045_ = lean_unbox(v_kind_1038_);
v_res_1046_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1034_, v_bi_boxed_1044_, v_type_1036_, v_k_1037_, v_kind_boxed_1045_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1047_, lean_object* v_name_1048_, uint8_t v_bi_1049_, lean_object* v_type_1050_, lean_object* v_k_1051_, uint8_t v_kind_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1048_, v_bi_1049_, v_type_1050_, v_k_1051_, v_kind_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1059_, lean_object* v_name_1060_, lean_object* v_bi_1061_, lean_object* v_type_1062_, lean_object* v_k_1063_, lean_object* v_kind_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v_bi_boxed_1070_; uint8_t v_kind_boxed_1071_; lean_object* v_res_1072_; 
v_bi_boxed_1070_ = lean_unbox(v_bi_1061_);
v_kind_boxed_1071_ = lean_unbox(v_kind_1064_);
v_res_1072_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1059_, v_name_1060_, v_bi_boxed_1070_, v_type_1062_, v_k_1063_, v_kind_boxed_1071_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_env_1080_; uint8_t v___x_1081_; lean_object* v_env_1082_; lean_object* v___x_1083_; lean_object* v_toCold_1084_; lean_object* v_mctx_1085_; lean_object* v_lctx_1086_; lean_object* v_options_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1079_ = lean_st_ref_get(v___y_1077_);
v_env_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_env_1080_);
lean_dec(v___x_1079_);
v___x_1081_ = 0;
v_env_1082_ = l_Lean_Environment_setRecordingDeps(v_env_1080_, v___x_1081_);
v___x_1083_ = lean_st_ref_get(v___y_1075_);
v_toCold_1084_ = lean_ctor_get(v___y_1076_, 0);
v_mctx_1085_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_mctx_1085_);
lean_dec(v___x_1083_);
v_lctx_1086_ = lean_ctor_get(v___y_1074_, 2);
v_options_1087_ = lean_ctor_get(v_toCold_1084_, 2);
lean_inc_ref(v_options_1087_);
lean_inc_ref(v_lctx_1086_);
v___x_1088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1088_, 0, v_env_1082_);
lean_ctor_set(v___x_1088_, 1, v_mctx_1085_);
lean_ctor_set(v___x_1088_, 2, v_lctx_1086_);
lean_ctor_set(v___x_1088_, 3, v_options_1087_);
v___x_1089_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_msgData_1073_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_ref_1104_; lean_object* v___x_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1114_; 
v_ref_1104_ = lean_ctor_get(v___y_1101_, 2);
v___x_1105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
lean_inc(v_ref_1104_);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v_ref_1104_);
lean_ctor_set(v___x_1110_, 1, v_a_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 1);
lean_ctor_set(v___x_1108_, 0, v___x_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1122_, lean_object* v_body_1123_, lean_object* v_args2_1124_, lean_object* v_args2New_1125_, lean_object* v_ctorVal_1126_, lean_object* v_useEq_1127_, lean_object* v_args1_1128_, lean_object* v_resultType_1129_, lean_object* v_k_1130_, lean_object* v_arg2_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_useEq_boxed_1137_; lean_object* v_res_1138_; 
v_useEq_boxed_1137_ = lean_unbox(v_useEq_1127_);
v_res_1138_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1122_, v_body_1123_, v_args2_1124_, v_args2New_1125_, v_ctorVal_1126_, v_useEq_boxed_1137_, v_args1_1128_, v_resultType_1129_, v_k_1130_, v_arg2_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v_body_1123_);
lean_dec(v_i_1122_);
return v_res_1138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1145_, uint8_t v_useEq_1146_, lean_object* v_args1_1147_, lean_object* v_resultType_1148_, lean_object* v_k_1149_, lean_object* v_i_1150_, lean_object* v_type_1151_, lean_object* v_args2_1152_, lean_object* v_args2New_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = lean_array_get_size(v_args1_1147_);
v___x_1160_ = lean_nat_dec_lt(v_i_1150_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec_ref(v_type_1151_);
lean_dec(v_i_1150_);
lean_dec_ref(v_resultType_1148_);
lean_dec_ref(v_args1_1147_);
lean_dec_ref(v_ctorVal_1145_);
lean_inc(v_a_1157_);
lean_inc_ref(v_a_1156_);
lean_inc(v_a_1155_);
lean_inc_ref(v_a_1154_);
v___x_1161_ = lean_apply_7(v_k_1149_, v_args2_1152_, v_args2New_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, lean_box(0));
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; 
lean_inc(v_a_1157_);
lean_inc_ref(v_a_1156_);
lean_inc(v_a_1155_);
lean_inc_ref(v_a_1154_);
v___x_1162_ = lean_whnf(v_type_1151_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
if (lean_obj_tag(v_a_1163_) == 7)
{
lean_object* v_binderName_1164_; lean_object* v_binderType_1165_; lean_object* v_body_1166_; lean_object* v_lctx_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_binderName_1164_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_binderName_1164_);
v_binderType_1165_ = lean_ctor_get(v_a_1163_, 1);
lean_inc_ref(v_binderType_1165_);
v_body_1166_ = lean_ctor_get(v_a_1163_, 2);
lean_inc_ref(v_body_1166_);
lean_dec_ref_known(v_a_1163_, 3);
v_lctx_1167_ = lean_ctor_get(v_a_1154_, 2);
v___x_1168_ = lean_array_fget_borrowed(v_args1_1147_, v_i_1150_);
lean_inc(v___x_1168_);
lean_inc_ref(v_lctx_1167_);
v___x_1169_ = l_Lean_Meta_occursOrInType(v_lctx_1167_, v___x_1168_, v_resultType_1148_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v___f_1171_; uint8_t v___y_1173_; 
v___x_1170_ = lean_box(v_useEq_1146_);
v___f_1171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1171_, 0, v_i_1150_);
lean_closure_set(v___f_1171_, 1, v_body_1166_);
lean_closure_set(v___f_1171_, 2, v_args2_1152_);
lean_closure_set(v___f_1171_, 3, v_args2New_1153_);
lean_closure_set(v___f_1171_, 4, v_ctorVal_1145_);
lean_closure_set(v___f_1171_, 5, v___x_1170_);
lean_closure_set(v___f_1171_, 6, v_args1_1147_);
lean_closure_set(v___f_1171_, 7, v_resultType_1148_);
lean_closure_set(v___f_1171_, 8, v_k_1149_);
if (v_useEq_1146_ == 0)
{
uint8_t v___x_1176_; 
v___x_1176_ = 1;
v___y_1173_ = v___x_1176_;
goto v___jp_1172_;
}
else
{
uint8_t v___x_1177_; 
v___x_1177_ = 0;
v___y_1173_ = v___x_1177_;
goto v___jp_1172_;
}
v___jp_1172_:
{
uint8_t v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = 0;
v___x_1175_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1164_, v___y_1173_, v_binderType_1165_, v___f_1171_, v___x_1174_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
return v___x_1175_;
}
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec_ref(v_binderType_1165_);
lean_dec(v_binderName_1164_);
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_add(v_i_1150_, v___x_1178_);
lean_dec(v_i_1150_);
v___x_1180_ = lean_expr_instantiate1(v_body_1166_, v___x_1168_);
lean_dec_ref(v_body_1166_);
lean_inc(v___x_1168_);
v___x_1181_ = lean_array_push(v_args2_1152_, v___x_1168_);
v_i_1150_ = v___x_1179_;
v_type_1151_ = v___x_1180_;
v_args2_1152_ = v___x_1181_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1183_; lean_object* v_name_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
lean_dec(v_a_1163_);
lean_dec_ref(v_args2New_1153_);
lean_dec_ref(v_args2_1152_);
lean_dec(v_i_1150_);
lean_dec_ref(v_k_1149_);
lean_dec_ref(v_resultType_1148_);
lean_dec_ref(v_args1_1147_);
v_toConstantVal_1183_ = lean_ctor_get(v_ctorVal_1145_, 0);
lean_inc_ref(v_toConstantVal_1183_);
lean_dec_ref(v_ctorVal_1145_);
v_name_1184_ = lean_ctor_get(v_toConstantVal_1183_, 0);
lean_inc(v_name_1184_);
lean_dec_ref(v_toConstantVal_1183_);
v___x_1185_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1186_ = l_Lean_MessageData_ofName(v_name_1184_);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1189_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
return v___x_1190_;
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_args2New_1153_);
lean_dec_ref(v_args2_1152_);
lean_dec(v_i_1150_);
lean_dec_ref(v_k_1149_);
lean_dec_ref(v_resultType_1148_);
lean_dec_ref(v_args1_1147_);
lean_dec_ref(v_ctorVal_1145_);
v_a_1191_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1162_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1162_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1199_, lean_object* v_body_1200_, lean_object* v_args2_1201_, lean_object* v_args2New_1202_, lean_object* v_ctorVal_1203_, uint8_t v_useEq_1204_, lean_object* v_args1_1205_, lean_object* v_resultType_1206_, lean_object* v_k_1207_, lean_object* v_arg2_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = lean_nat_add(v_i_1199_, v___x_1214_);
v___x_1216_ = lean_expr_instantiate1(v_body_1200_, v_arg2_1208_);
lean_inc_ref(v_arg2_1208_);
v___x_1217_ = lean_array_push(v_args2_1201_, v_arg2_1208_);
v___x_1218_ = lean_array_push(v_args2New_1202_, v_arg2_1208_);
v___x_1219_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1203_, v_useEq_1204_, v_args1_1205_, v_resultType_1206_, v_k_1207_, v___x_1215_, v___x_1216_, v___x_1217_, v___x_1218_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1220_, lean_object* v_useEq_1221_, lean_object* v_args1_1222_, lean_object* v_resultType_1223_, lean_object* v_k_1224_, lean_object* v_i_1225_, lean_object* v_type_1226_, lean_object* v_args2_1227_, lean_object* v_args2New_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
uint8_t v_useEq_boxed_1234_; lean_object* v_res_1235_; 
v_useEq_boxed_1234_ = lean_unbox(v_useEq_1221_);
v_res_1235_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1220_, v_useEq_boxed_1234_, v_args1_1222_, v_resultType_1223_, v_k_1224_, v_i_1225_, v_type_1226_, v_args2_1227_, v_args2New_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1236_, lean_object* v_msg_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1244_, lean_object* v_msg_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1244_, v_msg_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1252_, lean_object* v_h__1_1253_, lean_object* v_h__2_1254_){
_start:
{
if (lean_obj_tag(v_____x_1252_) == 7)
{
lean_object* v_binderName_1255_; lean_object* v_binderType_1256_; lean_object* v_body_1257_; uint8_t v_binderInfo_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_h__2_1254_);
v_binderName_1255_ = lean_ctor_get(v_____x_1252_, 0);
lean_inc(v_binderName_1255_);
v_binderType_1256_ = lean_ctor_get(v_____x_1252_, 1);
lean_inc_ref(v_binderType_1256_);
v_body_1257_ = lean_ctor_get(v_____x_1252_, 2);
lean_inc_ref(v_body_1257_);
v_binderInfo_1258_ = lean_ctor_get_uint8(v_____x_1252_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1252_, 3);
v___x_1259_ = lean_box(v_binderInfo_1258_);
v___x_1260_ = lean_apply_4(v_h__1_1253_, v_binderName_1255_, v_binderType_1256_, v_body_1257_, v___x_1259_);
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_h__1_1253_);
v___x_1261_ = lean_apply_2(v_h__2_1254_, v_____x_1252_, lean_box(0));
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1262_, lean_object* v_____x_1263_, lean_object* v_h__1_1264_, lean_object* v_h__2_1265_){
_start:
{
if (lean_obj_tag(v_____x_1263_) == 7)
{
lean_object* v_binderName_1266_; lean_object* v_binderType_1267_; lean_object* v_body_1268_; uint8_t v_binderInfo_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_h__2_1265_);
v_binderName_1266_ = lean_ctor_get(v_____x_1263_, 0);
lean_inc(v_binderName_1266_);
v_binderType_1267_ = lean_ctor_get(v_____x_1263_, 1);
lean_inc_ref(v_binderType_1267_);
v_body_1268_ = lean_ctor_get(v_____x_1263_, 2);
lean_inc_ref(v_body_1268_);
v_binderInfo_1269_ = lean_ctor_get_uint8(v_____x_1263_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1263_, 3);
v___x_1270_ = lean_box(v_binderInfo_1269_);
v___x_1271_ = lean_apply_4(v_h__1_1264_, v_binderName_1266_, v_binderType_1267_, v_body_1268_, v___x_1270_);
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; 
lean_dec(v_h__1_1264_);
v___x_1272_ = lean_apply_2(v_h__2_1265_, v_____x_1263_, lean_box(0));
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1273_, lean_object* v_b_1274_, lean_object* v_c_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
v___x_1281_ = lean_apply_7(v_k_1273_, v_b_1274_, v_c_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, lean_box(0));
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1282_, lean_object* v_b_1283_, lean_object* v_c_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1282_, v_b_1283_, v_c_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1291_, lean_object* v_k_1292_, uint8_t v_cleanupAnnotations_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___f_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___f_1299_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1299_, 0, v_k_1292_);
v___x_1300_ = 0;
v___x_1301_ = lean_box(0);
v___x_1302_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1300_, v___x_1301_, v_type_1291_, v___f_1299_, v_cleanupAnnotations_1293_, v___x_1300_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_a_1311_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1302_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1302_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1319_, lean_object* v_k_1320_, lean_object* v_cleanupAnnotations_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1327_; lean_object* v_res_1328_; 
v_cleanupAnnotations_boxed_1327_ = lean_unbox(v_cleanupAnnotations_1321_);
v_res_1328_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1319_, v_k_1320_, v_cleanupAnnotations_boxed_1327_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1329_, lean_object* v_type_1330_, lean_object* v_k_1331_, uint8_t v_cleanupAnnotations_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1330_, v_k_1331_, v_cleanupAnnotations_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_type_1340_, lean_object* v_k_1341_, lean_object* v_cleanupAnnotations_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1348_; lean_object* v_res_1349_; 
v_cleanupAnnotations_boxed_1348_ = lean_unbox(v_cleanupAnnotations_1342_);
v_res_1349_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1339_, v_type_1340_, v_k_1341_, v_cleanupAnnotations_boxed_1348_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1350_, lean_object* v_maxFVars_x3f_1351_, lean_object* v_k_1352_, uint8_t v_cleanupAnnotations_1353_, uint8_t v_whnfType_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___f_1360_; lean_object* v___x_1361_; 
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1360_, 0, v_k_1352_);
v___x_1361_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1350_, v_maxFVars_x3f_1351_, v___f_1360_, v_cleanupAnnotations_1353_, v_whnfType_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1370_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1361_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1361_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1378_, lean_object* v_maxFVars_x3f_1379_, lean_object* v_k_1380_, lean_object* v_cleanupAnnotations_1381_, lean_object* v_whnfType_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1388_; uint8_t v_whnfType_boxed_1389_; lean_object* v_res_1390_; 
v_cleanupAnnotations_boxed_1388_ = lean_unbox(v_cleanupAnnotations_1381_);
v_whnfType_boxed_1389_ = lean_unbox(v_whnfType_1382_);
v_res_1390_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1378_, v_maxFVars_x3f_1379_, v_k_1380_, v_cleanupAnnotations_boxed_1388_, v_whnfType_boxed_1389_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1391_, lean_object* v_type_1392_, lean_object* v_maxFVars_x3f_1393_, lean_object* v_k_1394_, uint8_t v_cleanupAnnotations_1395_, uint8_t v_whnfType_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1392_, v_maxFVars_x3f_1393_, v_k_1394_, v_cleanupAnnotations_1395_, v_whnfType_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_type_1404_, lean_object* v_maxFVars_x3f_1405_, lean_object* v_k_1406_, lean_object* v_cleanupAnnotations_1407_, lean_object* v_whnfType_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1414_; uint8_t v_whnfType_boxed_1415_; lean_object* v_res_1416_; 
v_cleanupAnnotations_boxed_1414_ = lean_unbox(v_cleanupAnnotations_1407_);
v_whnfType_boxed_1415_ = lean_unbox(v_whnfType_1408_);
v_res_1416_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1403_, v_type_1404_, v_maxFVars_x3f_1405_, v_k_1406_, v_cleanupAnnotations_boxed_1414_, v_whnfType_boxed_1415_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1417_, lean_object* v_us_1418_, lean_object* v_params_1419_, lean_object* v_args1_1420_, uint8_t v_useEq_1421_, lean_object* v_args2_1422_, lean_object* v_args2New_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1429_ = l_Lean_mkConst(v_name_1417_, v_us_1418_);
v___x_1430_ = l_Lean_mkAppN(v___x_1429_, v_params_1419_);
lean_inc_ref(v___x_1430_);
v___x_1431_ = l_Lean_mkAppN(v___x_1430_, v_args1_1420_);
v___x_1432_ = l_Lean_mkAppN(v___x_1430_, v_args2_1422_);
v___x_1433_ = l_Lean_Meta_mkEq(v___x_1431_, v___x_1432_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; uint8_t v___x_1435_; lean_object* v_result_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___x_1482_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = 1;
v___x_1482_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1420_, v_args2_1422_, v___x_1435_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1514_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1514_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1514_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; 
v___x_1487_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1483_);
if (lean_obj_tag(v___x_1487_) == 1)
{
lean_del_object(v___x_1485_);
if (v_useEq_1421_ == 0)
{
lean_object* v_val_1488_; lean_object* v___x_1489_; 
v_val_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = l_Lean_mkArrow(v_a_1434_, v_val_1488_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1489_, 1);
v_result_1437_ = v_a_1490_;
v___y_1438_ = v___y_1424_;
v___y_1439_ = v___y_1425_;
v___y_1440_ = v___y_1426_;
v___y_1441_ = v___y_1427_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
v_a_1491_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1489_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1489_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_val_1499_; lean_object* v___x_1500_; 
v_val_1499_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_val_1499_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1500_ = l_Lean_Meta_mkEq(v_a_1434_, v_val_1499_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v_result_1437_ = v_a_1501_;
v___y_1438_ = v___y_1424_;
v___y_1439_ = v___y_1425_;
v___y_1440_ = v___y_1426_;
v___y_1441_ = v___y_1427_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_a_1502_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1500_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1500_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_dec(v___x_1487_);
lean_dec(v_a_1434_);
v___x_1510_ = lean_box(0);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1510_);
v___x_1512_ = v___x_1485_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec(v_a_1434_);
v_a_1515_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1482_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1482_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
v___jp_1436_:
{
uint8_t v___x_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = 0;
v___x_1443_ = 1;
v___x_1444_ = l_Lean_Meta_mkForallFVars(v_args2New_1423_, v_result_1437_, v___x_1442_, v___x_1435_, v___x_1435_, v___x_1443_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = l_Lean_Meta_mkForallFVars(v_args1_1420_, v_a_1445_, v___x_1442_, v___x_1435_, v___x_1435_, v___x_1443_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = l_Lean_Meta_mkForallFVars(v_params_1419_, v_a_1447_, v___x_1442_, v___x_1435_, v___x_1435_, v___x_1443_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1457_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1457_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v_a_1449_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1453_);
v___x_1455_ = v___x_1451_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1448_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1448_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_a_1466_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1446_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1446_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1444_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1444_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec_ref(v_args2_1422_);
v_a_1523_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1433_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1433_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1531_, lean_object* v_us_1532_, lean_object* v_params_1533_, lean_object* v_args1_1534_, lean_object* v_useEq_1535_, lean_object* v_args2_1536_, lean_object* v_args2New_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
uint8_t v_useEq_boxed_1543_; lean_object* v_res_1544_; 
v_useEq_boxed_1543_ = lean_unbox(v_useEq_1535_);
v_res_1544_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1531_, v_us_1532_, v_params_1533_, v_args1_1534_, v_useEq_boxed_1543_, v_args2_1536_, v_args2New_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec_ref(v_args2New_1537_);
lean_dec_ref(v_args1_1534_);
lean_dec_ref(v_params_1533_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1545_, size_t v_i_1546_, lean_object* v_bs_1547_){
_start:
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_usize_dec_lt(v_i_1546_, v_sz_1545_);
if (v___x_1548_ == 0)
{
return v_bs_1547_;
}
else
{
lean_object* v_v_1549_; lean_object* v___x_1550_; lean_object* v_bs_x27_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; lean_object* v___x_1558_; 
v_v_1549_ = lean_array_uget(v_bs_1547_, v_i_1546_);
v___x_1550_ = lean_unsigned_to_nat(0u);
v_bs_x27_1551_ = lean_array_uset(v_bs_1547_, v_i_1546_, v___x_1550_);
v___x_1552_ = l_Lean_Expr_fvarId_x21(v_v_1549_);
lean_dec(v_v_1549_);
v___x_1553_ = 1;
v___x_1554_ = lean_box(v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1552_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = ((size_t)1ULL);
v___x_1557_ = lean_usize_add(v_i_1546_, v___x_1556_);
v___x_1558_ = lean_array_uset(v_bs_x27_1551_, v_i_1546_, v___x_1555_);
v_i_1546_ = v___x_1557_;
v_bs_1547_ = v___x_1558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1560_, lean_object* v_i_1561_, lean_object* v_bs_1562_){
_start:
{
size_t v_sz_boxed_1563_; size_t v_i_boxed_1564_; lean_object* v_res_1565_; 
v_sz_boxed_1563_ = lean_unbox_usize(v_sz_1560_);
lean_dec(v_sz_1560_);
v_i_boxed_1564_ = lean_unbox_usize(v_i_1561_);
lean_dec(v_i_1561_);
v_res_1565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1563_, v_i_boxed_1564_, v_bs_1562_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1566_, lean_object* v_k_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1566_, v_k_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1582_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1573_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1573_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1590_, lean_object* v_k_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1590_, v_k_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v_bs_1590_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1598_, lean_object* v_k_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
size_t v_sz_1605_; size_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_sz_1605_ = lean_array_size(v_bs_1598_);
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1605_, v___x_1606_, v_bs_1598_);
v___x_1608_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1607_, v_k_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec_ref(v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1609_, lean_object* v_k_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1609_, v_k_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1617_, lean_object* v_us_1618_, lean_object* v_params_1619_, uint8_t v_useEq_1620_, lean_object* v_ctorVal_1621_, lean_object* v_type_1622_, lean_object* v_args1_1623_, lean_object* v_resultType_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; lean_object* v___f_1631_; 
v___x_1630_ = lean_box(v_useEq_1620_);
lean_inc_ref(v_args1_1623_);
lean_inc_ref(v_params_1619_);
v___f_1631_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1631_, 0, v_name_1617_);
lean_closure_set(v___f_1631_, 1, v_us_1618_);
lean_closure_set(v___f_1631_, 2, v_params_1619_);
lean_closure_set(v___f_1631_, 3, v_args1_1623_);
lean_closure_set(v___f_1631_, 4, v___x_1630_);
if (v_useEq_1620_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1632_ = l_Array_append___redArg(v_params_1619_, v_args1_1623_);
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1635_ = lean_box(v_useEq_1620_);
v___x_1636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1636_, 0, v_ctorVal_1621_);
lean_closure_set(v___x_1636_, 1, v___x_1635_);
lean_closure_set(v___x_1636_, 2, v_args1_1623_);
lean_closure_set(v___x_1636_, 3, v_resultType_1624_);
lean_closure_set(v___x_1636_, 4, v___f_1631_);
lean_closure_set(v___x_1636_, 5, v___x_1633_);
lean_closure_set(v___x_1636_, 6, v_type_1622_);
lean_closure_set(v___x_1636_, 7, v___x_1634_);
lean_closure_set(v___x_1636_, 8, v___x_1634_);
v___x_1637_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1632_, v___x_1636_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_params_1619_);
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1640_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1621_, v_useEq_1620_, v_args1_1623_, v_resultType_1624_, v___f_1631_, v___x_1638_, v_type_1622_, v___x_1639_, v___x_1639_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1641_, lean_object* v_us_1642_, lean_object* v_params_1643_, lean_object* v_useEq_1644_, lean_object* v_ctorVal_1645_, lean_object* v_type_1646_, lean_object* v_args1_1647_, lean_object* v_resultType_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
uint8_t v_useEq_boxed_1654_; lean_object* v_res_1655_; 
v_useEq_boxed_1654_ = lean_unbox(v_useEq_1644_);
v_res_1655_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1641_, v_us_1642_, v_params_1643_, v_useEq_boxed_1654_, v_ctorVal_1645_, v_type_1646_, v_args1_1647_, v_resultType_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1656_, lean_object* v_us_1657_, uint8_t v_useEq_1658_, lean_object* v_ctorVal_1659_, lean_object* v_params_1660_, lean_object* v_type_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v___f_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; 
v___x_1667_ = lean_box(v_useEq_1658_);
lean_inc_ref(v_type_1661_);
v___f_1668_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1668_, 0, v_name_1656_);
lean_closure_set(v___f_1668_, 1, v_us_1657_);
lean_closure_set(v___f_1668_, 2, v_params_1660_);
lean_closure_set(v___f_1668_, 3, v___x_1667_);
lean_closure_set(v___f_1668_, 4, v_ctorVal_1659_);
lean_closure_set(v___f_1668_, 5, v_type_1661_);
v___x_1669_ = 0;
v___x_1670_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1661_, v___f_1668_, v___x_1669_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1671_, lean_object* v_us_1672_, lean_object* v_useEq_1673_, lean_object* v_ctorVal_1674_, lean_object* v_params_1675_, lean_object* v_type_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_useEq_boxed_1682_; lean_object* v_res_1683_; 
v_useEq_boxed_1682_ = lean_unbox(v_useEq_1673_);
v_res_1683_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1671_, v_us_1672_, v_useEq_boxed_1682_, v_ctorVal_1674_, v_params_1675_, v_type_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
if (lean_obj_tag(v_a_1684_) == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = l_List_reverse___redArg(v_a_1685_);
return v___x_1686_;
}
else
{
lean_object* v_head_1687_; lean_object* v_tail_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1697_; 
v_head_1687_ = lean_ctor_get(v_a_1684_, 0);
v_tail_1688_ = lean_ctor_get(v_a_1684_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_a_1684_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1690_ = v_a_1684_;
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_tail_1688_);
lean_inc(v_head_1687_);
lean_dec(v_a_1684_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = l_Lean_mkLevelParam(v_head_1687_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 1, v_a_1685_);
lean_ctor_set(v___x_1690_, 0, v___x_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1685_);
v___x_1694_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
v_a_1684_ = v_tail_1688_;
v_a_1685_ = v___x_1694_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1698_, uint8_t v_useEq_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_toConstantVal_1705_; lean_object* v_numParams_1706_; lean_object* v_name_1707_; lean_object* v_levelParams_1708_; lean_object* v_type_1709_; lean_object* v___x_1710_; lean_object* v_us_1711_; lean_object* v___x_1712_; lean_object* v___f_1713_; lean_object* v___x_1714_; 
v_toConstantVal_1705_ = lean_ctor_get(v_ctorVal_1698_, 0);
v_numParams_1706_ = lean_ctor_get(v_ctorVal_1698_, 3);
lean_inc(v_numParams_1706_);
v_name_1707_ = lean_ctor_get(v_toConstantVal_1705_, 0);
lean_inc(v_name_1707_);
v_levelParams_1708_ = lean_ctor_get(v_toConstantVal_1705_, 1);
v_type_1709_ = lean_ctor_get(v_toConstantVal_1705_, 2);
lean_inc_ref(v_type_1709_);
v___x_1710_ = lean_box(0);
lean_inc(v_levelParams_1708_);
v_us_1711_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1708_, v___x_1710_);
v___x_1712_ = lean_box(v_useEq_1699_);
v___f_1713_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1713_, 0, v_name_1707_);
lean_closure_set(v___f_1713_, 1, v_us_1711_);
lean_closure_set(v___f_1713_, 2, v___x_1712_);
lean_closure_set(v___f_1713_, 3, v_ctorVal_1698_);
v___x_1714_ = l_Lean_Meta_elimOptParam(v_type_1709_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_numParams_1706_);
v___x_1717_ = 0;
v___x_1718_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1715_, v___x_1716_, v___f_1713_, v___x_1717_, v___x_1717_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
return v___x_1718_;
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref(v___f_1713_);
lean_dec(v_numParams_1706_);
v_a_1719_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1714_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1714_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1727_, lean_object* v_useEq_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
uint8_t v_useEq_boxed_1734_; lean_object* v_res_1735_; 
v_useEq_boxed_1734_ = lean_unbox(v_useEq_1728_);
v_res_1735_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1727_, v_useEq_boxed_1734_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1736_, lean_object* v_bs_1737_, lean_object* v_k_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1737_, v_k_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_bs_1746_, lean_object* v_k_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1745_, v_bs_1746_, v_k_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v_bs_1746_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1754_, lean_object* v_bs_1755_, lean_object* v_k_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1755_, v_k_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_bs_1764_, lean_object* v_k_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1763_, v_bs_1764_, v_k_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
uint8_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = 0;
v___x_1779_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1772_, v___x_1778_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
return v_res_1786_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1793_){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1794_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1795_ = l_Lean_MessageData_ofName(v_ctorName_1793_);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1796_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1799_, lean_object* v_mvarId_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1806_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1799_);
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_mvarId_1800_);
v___x_1808_ = l_Lean_indentD(v___x_1807_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1806_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1809_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1811_, lean_object* v_mvarId_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1811_, v_mvarId_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1819_, lean_object* v_ctorName_1820_, lean_object* v_mvarId_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1820_, v_mvarId_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_ctorName_1829_, lean_object* v_mvarId_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1828_, v_ctorName_1829_, v_mvarId_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1837_, lean_object* v_as_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
if (lean_obj_tag(v_as_1838_) == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v_ctorName_1837_);
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
else
{
lean_object* v_head_1846_; lean_object* v_tail_1847_; lean_object* v___x_1848_; 
v_head_1846_ = lean_ctor_get(v_as_1838_, 0);
lean_inc_n(v_head_1846_, 2);
v_tail_1847_ = lean_ctor_get(v_as_1838_, 1);
lean_inc(v_tail_1847_);
lean_dec_ref_known(v_as_1838_, 2);
v___x_1848_ = l_Lean_MVarId_assumptionCore(v_head_1846_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; uint8_t v___x_1850_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = lean_unbox(v_a_1849_);
lean_dec(v_a_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
lean_dec(v_tail_1847_);
v___x_1851_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1837_, v_head_1846_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
return v___x_1851_;
}
else
{
lean_dec(v_head_1846_);
v_as_1838_ = v_tail_1847_;
goto _start;
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_tail_1847_);
lean_dec(v_head_1846_);
lean_dec(v_ctorName_1837_);
v_a_1853_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1848_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1848_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1861_, lean_object* v_as_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1861_, v_as_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1869_, lean_object* v_ctorName_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_MVarId_splitAndCore(v_mvarId_1869_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v___x_1878_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1870_, v_a_1877_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1878_;
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_ctorName_1870_);
v_a_1879_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1876_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1876_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1887_, lean_object* v_ctorName_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1887_, v_ctorName_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___f_1902_; lean_object* v___x_922__overap_1903_; lean_object* v___x_1904_; 
v___f_1902_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_922__overap_1903_ = lean_panic_fn_borrowed(v___f_1902_, v_msg_1896_);
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1899_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
v___x_1904_ = lean_apply_5(v___x_922__overap_1903_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, lean_box(0));
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1911_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1912_; double v___x_1913_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_float_of_nat(v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1917_, lean_object* v_msg_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_ref_1924_; lean_object* v___x_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1971_; 
v_ref_1924_ = lean_ctor_get(v___y_1921_, 2);
v___x_1925_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1971_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1971_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v_traceState_1931_; lean_object* v_env_1932_; lean_object* v_nextMacroScope_1933_; lean_object* v_ngen_1934_; lean_object* v_auxDeclNGen_1935_; lean_object* v_cache_1936_; lean_object* v_recordedDeps_1937_; lean_object* v_messages_1938_; lean_object* v_infoState_1939_; lean_object* v_snapshotTasks_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1970_; 
v___x_1930_ = lean_st_ref_take(v___y_1922_);
v_traceState_1931_ = lean_ctor_get(v___x_1930_, 4);
v_env_1932_ = lean_ctor_get(v___x_1930_, 0);
v_nextMacroScope_1933_ = lean_ctor_get(v___x_1930_, 1);
v_ngen_1934_ = lean_ctor_get(v___x_1930_, 2);
v_auxDeclNGen_1935_ = lean_ctor_get(v___x_1930_, 3);
v_cache_1936_ = lean_ctor_get(v___x_1930_, 5);
v_recordedDeps_1937_ = lean_ctor_get(v___x_1930_, 6);
v_messages_1938_ = lean_ctor_get(v___x_1930_, 7);
v_infoState_1939_ = lean_ctor_get(v___x_1930_, 8);
v_snapshotTasks_1940_ = lean_ctor_get(v___x_1930_, 9);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1942_ = v___x_1930_;
v_isShared_1943_ = v_isSharedCheck_1970_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_snapshotTasks_1940_);
lean_inc(v_infoState_1939_);
lean_inc(v_messages_1938_);
lean_inc(v_recordedDeps_1937_);
lean_inc(v_cache_1936_);
lean_inc(v_traceState_1931_);
lean_inc(v_auxDeclNGen_1935_);
lean_inc(v_ngen_1934_);
lean_inc(v_nextMacroScope_1933_);
lean_inc(v_env_1932_);
lean_dec(v___x_1930_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1970_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
uint64_t v_tid_1944_; lean_object* v_traces_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1969_; 
v_tid_1944_ = lean_ctor_get_uint64(v_traceState_1931_, sizeof(void*)*1);
v_traces_1945_ = lean_ctor_get(v_traceState_1931_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_traceState_1931_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1947_ = v_traceState_1931_;
v_isShared_1948_ = v_isSharedCheck_1969_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_traces_1945_);
lean_dec(v_traceState_1931_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1969_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; double v___x_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1949_ = lean_box(0);
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1952_ = 0;
v___x_1953_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1954_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1954_, 0, v_cls_1917_);
lean_ctor_set(v___x_1954_, 1, v___x_1950_);
lean_ctor_set(v___x_1954_, 2, v___x_1953_);
lean_ctor_set_float(v___x_1954_, sizeof(void*)*3, v___x_1951_);
lean_ctor_set_float(v___x_1954_, sizeof(void*)*3 + 8, v___x_1951_);
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*3 + 16, v___x_1952_);
v___x_1955_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1956_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v_a_1926_);
lean_ctor_set(v___x_1956_, 2, v___x_1955_);
lean_inc(v_ref_1924_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_ref_1924_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_PersistentArray_push___redArg(v_traces_1945_, v___x_1957_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1958_);
v___x_1960_ = v___x_1947_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1958_);
lean_ctor_set_uint64(v_reuseFailAlloc_1968_, sizeof(void*)*1, v_tid_1944_);
v___x_1960_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v___x_1960_);
v___x_1962_ = v___x_1942_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_env_1932_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_nextMacroScope_1933_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_ngen_1934_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_auxDeclNGen_1935_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1967_, 5, v_cache_1936_);
lean_ctor_set(v_reuseFailAlloc_1967_, 6, v_recordedDeps_1937_);
lean_ctor_set(v_reuseFailAlloc_1967_, 7, v_messages_1938_);
lean_ctor_set(v_reuseFailAlloc_1967_, 8, v_infoState_1939_);
lean_ctor_set(v_reuseFailAlloc_1967_, 9, v_snapshotTasks_1940_);
v___x_1962_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = lean_st_ref_put(v___y_1922_, v___x_1962_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1949_);
v___x_1965_ = v___x_1928_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1949_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1972_, lean_object* v_msg_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1972_, v_msg_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1979_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1984_ = lean_unsigned_to_nat(30u);
v___x_1985_ = lean_unsigned_to_nat(96u);
v___x_1986_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1987_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1988_ = l_mkPanicMessageWithDecl(v___x_1987_, v___x_1986_, v___x_1985_, v___x_1984_, v___x_1983_);
return v___x_1988_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_cls_1997_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_1998_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_1999_ = l_Lean_Name_append(v___x_1998_, v_cls_1997_);
return v___x_1999_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_2002_ = l_Lean_stringToMessageData(v___x_2001_);
return v___x_2002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_2005_ = l_Lean_stringToMessageData(v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2008_ = l_Lean_stringToMessageData(v___x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2009_, lean_object* v_mvarId_2010_, lean_object* v_h_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v_toCold_2037_; lean_object* v_options_2038_; uint8_t v_hasTrace_2039_; 
v_toCold_2037_ = lean_ctor_get(v_a_2014_, 0);
v_options_2038_ = lean_ctor_get(v_toCold_2037_, 2);
v_hasTrace_2039_ = lean_ctor_get_uint8(v_options_2038_, sizeof(void*)*1);
if (v_hasTrace_2039_ == 0)
{
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
v___y_2020_ = v_a_2014_;
v___y_2021_ = v_a_2015_;
goto v___jp_2017_;
}
else
{
lean_object* v_inheritedTraceOptions_2040_; lean_object* v_cls_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_inheritedTraceOptions_2040_ = lean_ctor_get(v_toCold_2037_, 11);
v_cls_2041_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2042_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2043_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2040_, v_options_2038_, v___x_2042_);
if (v___x_2043_ == 0)
{
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
v___y_2020_ = v_a_2014_;
v___y_2021_ = v_a_2015_;
goto v___jp_2017_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2044_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2009_);
v___x_2045_ = l_Lean_MessageData_ofName(v_ctorName_2009_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_inc(v_h_2011_);
v___x_2049_ = l_Lean_mkFVar(v_h_2011_);
v___x_2050_ = l_Lean_MessageData_ofExpr(v___x_2049_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2048_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
lean_inc(v_mvarId_2010_);
v___x_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2054_, 0, v_mvarId_2010_);
v___x_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2053_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2041_, v___x_2055_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_dec_ref_known(v___x_2056_, 1);
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
v___y_2020_ = v_a_2014_;
v___y_2021_ = v_a_2015_;
goto v___jp_2017_;
}
else
{
lean_dec(v_h_2011_);
lean_dec(v_mvarId_2010_);
lean_dec(v_ctorName_2009_);
return v___x_2056_;
}
}
}
v___jp_2017_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_box(0);
v___x_2023_ = l_Lean_Meta_injection(v_mvarId_2010_, v_h_2011_, v___x_2022_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
if (lean_obj_tag(v_a_2024_) == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_dec(v_ctorName_2009_);
v___x_2025_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2026_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2025_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2026_;
}
else
{
lean_object* v_mvarId_2027_; lean_object* v___x_2028_; 
v_mvarId_2027_ = lean_ctor_get(v_a_2024_, 0);
lean_inc(v_mvarId_2027_);
lean_dec_ref_known(v_a_2024_, 3);
v___x_2028_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2027_, v_ctorName_2009_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2028_;
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_ctorName_2009_);
v_a_2029_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2023_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2023_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2057_, lean_object* v_mvarId_2058_, lean_object* v_h_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2057_, v_mvarId_2058_, v_h_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2066_, lean_object* v_k_2067_, uint8_t v_cleanupAnnotations_2068_, uint8_t v_whnfType_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___f_2075_; lean_object* v___x_2076_; 
v___f_2075_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2075_, 0, v_k_2067_);
v___x_2076_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2066_, v___f_2075_, v_cleanupAnnotations_2068_, v_whnfType_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2076_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2076_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2093_, lean_object* v_k_2094_, lean_object* v_cleanupAnnotations_2095_, lean_object* v_whnfType_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2102_; uint8_t v_whnfType_boxed_2103_; lean_object* v_res_2104_; 
v_cleanupAnnotations_boxed_2102_ = lean_unbox(v_cleanupAnnotations_2095_);
v_whnfType_boxed_2103_ = lean_unbox(v_whnfType_2096_);
v_res_2104_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2093_, v_k_2094_, v_cleanupAnnotations_boxed_2102_, v_whnfType_boxed_2103_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2105_, lean_object* v_type_2106_, lean_object* v_k_2107_, uint8_t v_cleanupAnnotations_2108_, uint8_t v_whnfType_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2106_, v_k_2107_, v_cleanupAnnotations_2108_, v_whnfType_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_type_2117_, lean_object* v_k_2118_, lean_object* v_cleanupAnnotations_2119_, lean_object* v_whnfType_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2126_; uint8_t v_whnfType_boxed_2127_; lean_object* v_res_2128_; 
v_cleanupAnnotations_boxed_2126_ = lean_unbox(v_cleanupAnnotations_2119_);
v_whnfType_boxed_2127_ = lean_unbox(v_whnfType_2120_);
v_res_2128_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2116_, v_type_2117_, v_k_2118_, v_cleanupAnnotations_boxed_2126_, v_whnfType_boxed_2127_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2129_, lean_object* v_ctorName_2130_, lean_object* v_xs_2131_, lean_object* v_type_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_box(0);
v___x_2139_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2132_, v___x_2138_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_Expr_mvarId_x21(v_a_2140_);
v___x_2142_ = lean_array_get_size(v_xs_2131_);
v___x_2143_ = lean_unsigned_to_nat(1u);
v___x_2144_ = lean_nat_sub(v___x_2142_, v___x_2143_);
v___x_2145_ = lean_array_get_borrowed(v___x_2129_, v_xs_2131_, v___x_2144_);
lean_dec(v___x_2144_);
v___x_2146_ = l_Lean_Expr_fvarId_x21(v___x_2145_);
v___x_2147_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2130_, v___x_2141_, v___x_2146_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2147_) == 0)
{
uint8_t v___x_2148_; uint8_t v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref_known(v___x_2147_, 1);
v___x_2148_ = 0;
v___x_2149_ = 1;
v___x_2150_ = 1;
v___x_2151_ = l_Lean_Meta_mkLambdaFVars(v_xs_2131_, v_a_2140_, v___x_2148_, v___x_2149_, v___x_2148_, v___x_2149_, v___x_2150_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2151_;
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v_a_2140_);
v_a_2152_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2147_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2147_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_dec(v_ctorName_2130_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2160_, lean_object* v_ctorName_2161_, lean_object* v_xs_2162_, lean_object* v_type_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2160_, v_ctorName_2161_, v_xs_2162_, v_type_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v_xs_2162_);
lean_dec_ref(v___x_2160_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2170_, lean_object* v_targetType_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v___x_2177_; lean_object* v___f_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; 
v___x_2177_ = l_Lean_instInhabitedExpr;
v___f_2178_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2178_, 0, v___x_2177_);
lean_closure_set(v___f_2178_, 1, v_ctorName_2170_);
v___x_2179_ = 0;
v___x_2180_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2171_, v___f_2178_, v___x_2179_, v___x_2179_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2181_, lean_object* v_targetType_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2181_, v_targetType_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2194_ = l_Lean_Name_append(v_ctorName_2192_, v___x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2195_, lean_object* v___y_2196_){
_start:
{
uint8_t v___x_2198_; 
v___x_2198_ = l_Lean_Expr_hasMVar(v_e_2195_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_e_2195_);
return v___x_2199_;
}
else
{
lean_object* v___x_2200_; lean_object* v_mctx_2201_; lean_object* v___x_2202_; lean_object* v_fst_2203_; lean_object* v_snd_2204_; lean_object* v___x_2205_; lean_object* v_cache_2206_; lean_object* v_zetaDeltaFVarIds_2207_; lean_object* v_postponed_2208_; lean_object* v_diag_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2218_; 
v___x_2200_ = lean_st_ref_get(v___y_2196_);
v_mctx_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc_ref(v_mctx_2201_);
lean_dec(v___x_2200_);
v___x_2202_ = l_Lean_instantiateMVarsCore(v_mctx_2201_, v_e_2195_);
v_fst_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_fst_2203_);
v_snd_2204_ = lean_ctor_get(v___x_2202_, 1);
lean_inc(v_snd_2204_);
lean_dec_ref(v___x_2202_);
v___x_2205_ = lean_st_ref_take(v___y_2196_);
v_cache_2206_ = lean_ctor_get(v___x_2205_, 1);
v_zetaDeltaFVarIds_2207_ = lean_ctor_get(v___x_2205_, 2);
v_postponed_2208_ = lean_ctor_get(v___x_2205_, 3);
v_diag_2209_ = lean_ctor_get(v___x_2205_, 4);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; 
v_unused_2219_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2219_);
v___x_2211_ = v___x_2205_;
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_diag_2209_);
lean_inc(v_postponed_2208_);
lean_inc(v_zetaDeltaFVarIds_2207_);
lean_inc(v_cache_2206_);
lean_dec(v___x_2205_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v_snd_2204_);
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_snd_2204_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_cache_2206_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_zetaDeltaFVarIds_2207_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v_postponed_2208_);
lean_ctor_set(v_reuseFailAlloc_2217_, 4, v_diag_2209_);
v___x_2214_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_st_ref_put(v___y_2196_, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v_fst_2203_);
return v___x_2216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2220_, v___y_2221_);
lean_dec(v___y_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2224_, v___y_2226_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
return v_res_2237_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_unsigned_to_nat(32u);
v___x_2239_ = lean_mk_empty_array_with_capacity(v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2241_ = ((size_t)5ULL);
v___x_2242_ = lean_unsigned_to_nat(0u);
v___x_2243_ = lean_unsigned_to_nat(32u);
v___x_2244_ = lean_mk_empty_array_with_capacity(v___x_2243_);
v___x_2245_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2246_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
lean_ctor_set(v___x_2246_, 1, v___x_2244_);
lean_ctor_set(v___x_2246_, 2, v___x_2242_);
lean_ctor_set(v___x_2246_, 3, v___x_2242_);
lean_ctor_set_usize(v___x_2246_, 4, v___x_2241_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v_traceState_2250_; lean_object* v_traces_2251_; lean_object* v___x_2252_; lean_object* v_traceState_2253_; lean_object* v_env_2254_; lean_object* v_nextMacroScope_2255_; lean_object* v_ngen_2256_; lean_object* v_auxDeclNGen_2257_; lean_object* v_cache_2258_; lean_object* v_recordedDeps_2259_; lean_object* v_messages_2260_; lean_object* v_infoState_2261_; lean_object* v_snapshotTasks_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2281_; 
v___x_2249_ = lean_st_ref_get(v___y_2247_);
v_traceState_2250_ = lean_ctor_get(v___x_2249_, 4);
lean_inc_ref(v_traceState_2250_);
lean_dec(v___x_2249_);
v_traces_2251_ = lean_ctor_get(v_traceState_2250_, 0);
lean_inc_ref(v_traces_2251_);
lean_dec_ref(v_traceState_2250_);
v___x_2252_ = lean_st_ref_take(v___y_2247_);
v_traceState_2253_ = lean_ctor_get(v___x_2252_, 4);
v_env_2254_ = lean_ctor_get(v___x_2252_, 0);
v_nextMacroScope_2255_ = lean_ctor_get(v___x_2252_, 1);
v_ngen_2256_ = lean_ctor_get(v___x_2252_, 2);
v_auxDeclNGen_2257_ = lean_ctor_get(v___x_2252_, 3);
v_cache_2258_ = lean_ctor_get(v___x_2252_, 5);
v_recordedDeps_2259_ = lean_ctor_get(v___x_2252_, 6);
v_messages_2260_ = lean_ctor_get(v___x_2252_, 7);
v_infoState_2261_ = lean_ctor_get(v___x_2252_, 8);
v_snapshotTasks_2262_ = lean_ctor_get(v___x_2252_, 9);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2264_ = v___x_2252_;
v_isShared_2265_ = v_isSharedCheck_2281_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_snapshotTasks_2262_);
lean_inc(v_infoState_2261_);
lean_inc(v_messages_2260_);
lean_inc(v_recordedDeps_2259_);
lean_inc(v_cache_2258_);
lean_inc(v_traceState_2253_);
lean_inc(v_auxDeclNGen_2257_);
lean_inc(v_ngen_2256_);
lean_inc(v_nextMacroScope_2255_);
lean_inc(v_env_2254_);
lean_dec(v___x_2252_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2281_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
uint64_t v_tid_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2279_; 
v_tid_2266_ = lean_ctor_get_uint64(v_traceState_2253_, sizeof(void*)*1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_traceState_2253_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; 
v_unused_2280_ = lean_ctor_get(v_traceState_2253_, 0);
lean_dec(v_unused_2280_);
v___x_2268_ = v_traceState_2253_;
v_isShared_2269_ = v_isSharedCheck_2279_;
goto v_resetjp_2267_;
}
else
{
lean_dec(v_traceState_2253_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2279_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2270_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2270_);
v___x_2272_ = v___x_2268_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2270_);
lean_ctor_set_uint64(v_reuseFailAlloc_2278_, sizeof(void*)*1, v_tid_2266_);
v___x_2272_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2274_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 4, v___x_2272_);
v___x_2274_ = v___x_2264_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_env_2254_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_nextMacroScope_2255_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_ngen_2256_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v_auxDeclNGen_2257_);
lean_ctor_set(v_reuseFailAlloc_2277_, 4, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2277_, 5, v_cache_2258_);
lean_ctor_set(v_reuseFailAlloc_2277_, 6, v_recordedDeps_2259_);
lean_ctor_set(v_reuseFailAlloc_2277_, 7, v_messages_2260_);
lean_ctor_set(v_reuseFailAlloc_2277_, 8, v_infoState_2261_);
lean_ctor_set(v_reuseFailAlloc_2277_, 9, v_snapshotTasks_2262_);
v___x_2274_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_st_ref_put(v___y_2247_, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_traces_2251_);
return v___x_2276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2282_);
lean_dec(v___y_2282_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2297_, lean_object* v_opt_2298_){
_start:
{
lean_object* v_name_2299_; lean_object* v_defValue_2300_; lean_object* v_map_2301_; lean_object* v___x_2302_; 
v_name_2299_ = lean_ctor_get(v_opt_2298_, 0);
v_defValue_2300_ = lean_ctor_get(v_opt_2298_, 1);
v_map_2301_ = lean_ctor_get(v_opts_2297_, 0);
v___x_2302_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2301_, v_name_2299_);
if (lean_obj_tag(v___x_2302_) == 0)
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_unbox(v_defValue_2300_);
return v___x_2303_;
}
else
{
lean_object* v_val_2304_; 
v_val_2304_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_val_2304_);
lean_dec_ref_known(v___x_2302_, 1);
if (lean_obj_tag(v_val_2304_) == 1)
{
uint8_t v_v_2305_; 
v_v_2305_ = lean_ctor_get_uint8(v_val_2304_, 0);
lean_dec_ref_known(v_val_2304_, 0);
return v_v_2305_;
}
else
{
uint8_t v___x_2306_; 
lean_dec(v_val_2304_);
v___x_2306_ = lean_unbox(v_defValue_2300_);
return v___x_2306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2307_, lean_object* v_opt_2308_){
_start:
{
uint8_t v_res_2309_; lean_object* v_r_2310_; 
v_res_2309_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2307_, v_opt_2308_);
lean_dec_ref(v_opt_2308_);
lean_dec_ref(v_opts_2307_);
v_r_2310_ = lean_box(v_res_2309_);
return v_r_2310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2313_ = l_Lean_stringToMessageData(v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2314_, lean_object* v_x_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2321_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2322_ = l_Lean_MessageData_ofName(v_name_2314_);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2323_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2327_, lean_object* v_x_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2327_, v_x_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v_x_2328_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2335_, lean_object* v_val_2336_, lean_object* v_name_2337_, lean_object* v_levelParams_2338_, uint8_t v___x_2339_, lean_object* v_____r_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; 
lean_inc_ref(v_val_2336_);
v___x_2346_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2335_, v_val_2336_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2348_; lean_object* v_a_2349_; lean_object* v___x_2350_; lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2363_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2348_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2336_, v___y_2342_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref(v___x_2348_);
v___x_2350_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2347_, v___y_2342_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2363_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2363_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
lean_inc(v_name_2337_);
v___x_2355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2355_, 0, v_name_2337_);
lean_ctor_set(v___x_2355_, 1, v_levelParams_2338_);
lean_ctor_set(v___x_2355_, 2, v_a_2349_);
v___x_2356_ = lean_box(0);
v___x_2357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2357_, 0, v_name_2337_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2355_);
lean_ctor_set(v___x_2358_, 1, v_a_2351_);
lean_ctor_set(v___x_2358_, 2, v___x_2357_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 2);
lean_ctor_set(v___x_2353_, 0, v___x_2358_);
v___x_2360_ = v___x_2353_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_addDecl(v___x_2360_, v___x_2339_, v___y_2343_, v___y_2344_);
return v___x_2361_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_levelParams_2338_);
lean_dec(v_name_2337_);
lean_dec_ref(v_val_2336_);
v_a_2364_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2346_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2346_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2372_, lean_object* v_val_2373_, lean_object* v_name_2374_, lean_object* v_levelParams_2375_, lean_object* v___x_2376_, lean_object* v_____r_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
uint8_t v___x_12492__boxed_2383_; lean_object* v_res_2384_; 
v___x_12492__boxed_2383_ = lean_unbox(v___x_2376_);
v_res_2384_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2372_, v_val_2373_, v_name_2374_, v_levelParams_2375_, v___x_12492__boxed_2383_, v_____r_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2385_, lean_object* v_val_2386_, lean_object* v_name_2387_, lean_object* v_levelParams_2388_, lean_object* v_____r_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
lean_inc_ref(v_val_2386_);
v___x_2395_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2385_, v_val_2386_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; lean_object* v___x_2397_; lean_object* v_a_2398_; lean_object* v___x_2399_; lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2413_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2397_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2386_, v___y_2391_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2396_, v___y_2391_);
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2413_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2413_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
lean_inc(v_name_2387_);
v___x_2404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2404_, 0, v_name_2387_);
lean_ctor_set(v___x_2404_, 1, v_levelParams_2388_);
lean_ctor_set(v___x_2404_, 2, v_a_2398_);
v___x_2405_ = lean_box(0);
v___x_2406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_name_2387_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2404_);
lean_ctor_set(v___x_2407_, 1, v_a_2400_);
lean_ctor_set(v___x_2407_, 2, v___x_2406_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set_tag(v___x_2402_, 2);
lean_ctor_set(v___x_2402_, 0, v___x_2407_);
v___x_2409_ = v___x_2402_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
uint8_t v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = 0;
v___x_2411_ = l_Lean_addDecl(v___x_2409_, v___x_2410_, v___y_2392_, v___y_2393_);
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v_levelParams_2388_);
lean_dec(v_name_2387_);
lean_dec_ref(v_val_2386_);
v_a_2414_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2395_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2395_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2422_, lean_object* v_val_2423_, lean_object* v_name_2424_, lean_object* v_levelParams_2425_, lean_object* v_____r_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2422_, v_val_2423_, v_name_2424_, v_levelParams_2425_, v_____r_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t v_sz_2433_, size_t v_i_2434_, lean_object* v_bs_2435_){
_start:
{
uint8_t v___x_2436_; 
v___x_2436_ = lean_usize_dec_lt(v_i_2434_, v_sz_2433_);
if (v___x_2436_ == 0)
{
return v_bs_2435_;
}
else
{
lean_object* v_v_2437_; lean_object* v_msg_2438_; lean_object* v___x_2439_; lean_object* v_bs_x27_2440_; size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v_v_2437_ = lean_array_uget_borrowed(v_bs_2435_, v_i_2434_);
v_msg_2438_ = lean_ctor_get(v_v_2437_, 1);
lean_inc_ref(v_msg_2438_);
v___x_2439_ = lean_unsigned_to_nat(0u);
v_bs_x27_2440_ = lean_array_uset(v_bs_2435_, v_i_2434_, v___x_2439_);
v___x_2441_ = ((size_t)1ULL);
v___x_2442_ = lean_usize_add(v_i_2434_, v___x_2441_);
v___x_2443_ = lean_array_uset(v_bs_x27_2440_, v_i_2434_, v_msg_2438_);
v_i_2434_ = v___x_2442_;
v_bs_2435_ = v___x_2443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2445_, lean_object* v_i_2446_, lean_object* v_bs_2447_){
_start:
{
size_t v_sz_boxed_2448_; size_t v_i_boxed_2449_; lean_object* v_res_2450_; 
v_sz_boxed_2448_ = lean_unbox_usize(v_sz_2445_);
lean_dec(v_sz_2445_);
v_i_boxed_2449_ = lean_unbox_usize(v_i_2446_);
lean_dec(v_i_2446_);
v_res_2450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_boxed_2448_, v_i_boxed_2449_, v_bs_2447_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_oldTraces_2451_, lean_object* v_data_2452_, lean_object* v_ref_2453_, lean_object* v_msg_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_toCold_2460_; lean_object* v_currRecDepth_2461_; lean_object* v_ref_2462_; uint16_t v_optionFlags_2463_; uint8_t v_suppressElabErrors_2464_; uint8_t v_checkDeprecated_2465_; uint8_t v_isRecordingDeps_2466_; lean_object* v_ref_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_traceState_2470_; lean_object* v_traces_2471_; lean_object* v___x_2472_; size_t v_sz_2473_; size_t v___x_2474_; lean_object* v___x_2475_; lean_object* v_msg_2476_; lean_object* v___x_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2516_; 
v_toCold_2460_ = lean_ctor_get(v___y_2457_, 0);
v_currRecDepth_2461_ = lean_ctor_get(v___y_2457_, 1);
v_ref_2462_ = lean_ctor_get(v___y_2457_, 2);
v_optionFlags_2463_ = lean_ctor_get_uint16(v___y_2457_, sizeof(void*)*3);
v_suppressElabErrors_2464_ = lean_ctor_get_uint8(v___y_2457_, sizeof(void*)*3 + 2);
v_checkDeprecated_2465_ = lean_ctor_get_uint8(v___y_2457_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2466_ = lean_ctor_get_uint8(v___y_2457_, sizeof(void*)*3 + 4);
v_ref_2467_ = l_Lean_replaceRef(v_ref_2453_, v_ref_2462_);
lean_inc(v_currRecDepth_2461_);
lean_inc_ref(v_toCold_2460_);
v___x_2468_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2468_, 0, v_toCold_2460_);
lean_ctor_set(v___x_2468_, 1, v_currRecDepth_2461_);
lean_ctor_set(v___x_2468_, 2, v_ref_2467_);
lean_ctor_set_uint16(v___x_2468_, sizeof(void*)*3, v_optionFlags_2463_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 2, v_suppressElabErrors_2464_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 3, v_checkDeprecated_2465_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*3 + 4, v_isRecordingDeps_2466_);
v___x_2469_ = lean_st_ref_get(v___y_2458_);
v_traceState_2470_ = lean_ctor_get(v___x_2469_, 4);
lean_inc_ref(v_traceState_2470_);
lean_dec(v___x_2469_);
v_traces_2471_ = lean_ctor_get(v_traceState_2470_, 0);
lean_inc_ref(v_traces_2471_);
lean_dec_ref(v_traceState_2470_);
v___x_2472_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2471_);
lean_dec_ref(v_traces_2471_);
v_sz_2473_ = lean_array_size(v___x_2472_);
v___x_2474_ = ((size_t)0ULL);
v___x_2475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_2473_, v___x_2474_, v___x_2472_);
v_msg_2476_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2476_, 0, v_data_2452_);
lean_ctor_set(v_msg_2476_, 1, v_msg_2454_);
lean_ctor_set(v_msg_2476_, 2, v___x_2475_);
v___x_2477_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2476_, v___y_2455_, v___y_2456_, v___x_2468_, v___y_2458_);
lean_dec_ref_known(v___x_2468_, 3);
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2516_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2516_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v_traceState_2483_; lean_object* v_env_2484_; lean_object* v_nextMacroScope_2485_; lean_object* v_ngen_2486_; lean_object* v_auxDeclNGen_2487_; lean_object* v_cache_2488_; lean_object* v_recordedDeps_2489_; lean_object* v_messages_2490_; lean_object* v_infoState_2491_; lean_object* v_snapshotTasks_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2515_; 
v___x_2482_ = lean_st_ref_take(v___y_2458_);
v_traceState_2483_ = lean_ctor_get(v___x_2482_, 4);
v_env_2484_ = lean_ctor_get(v___x_2482_, 0);
v_nextMacroScope_2485_ = lean_ctor_get(v___x_2482_, 1);
v_ngen_2486_ = lean_ctor_get(v___x_2482_, 2);
v_auxDeclNGen_2487_ = lean_ctor_get(v___x_2482_, 3);
v_cache_2488_ = lean_ctor_get(v___x_2482_, 5);
v_recordedDeps_2489_ = lean_ctor_get(v___x_2482_, 6);
v_messages_2490_ = lean_ctor_get(v___x_2482_, 7);
v_infoState_2491_ = lean_ctor_get(v___x_2482_, 8);
v_snapshotTasks_2492_ = lean_ctor_get(v___x_2482_, 9);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2494_ = v___x_2482_;
v_isShared_2495_ = v_isSharedCheck_2515_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_snapshotTasks_2492_);
lean_inc(v_infoState_2491_);
lean_inc(v_messages_2490_);
lean_inc(v_recordedDeps_2489_);
lean_inc(v_cache_2488_);
lean_inc(v_traceState_2483_);
lean_inc(v_auxDeclNGen_2487_);
lean_inc(v_ngen_2486_);
lean_inc(v_nextMacroScope_2485_);
lean_inc(v_env_2484_);
lean_dec(v___x_2482_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2515_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
uint64_t v_tid_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2513_; 
v_tid_2496_ = lean_ctor_get_uint64(v_traceState_2483_, sizeof(void*)*1);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_traceState_2483_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v_traceState_2483_, 0);
lean_dec(v_unused_2514_);
v___x_2498_ = v_traceState_2483_;
v_isShared_2499_ = v_isSharedCheck_2513_;
goto v_resetjp_2497_;
}
else
{
lean_dec(v_traceState_2483_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2513_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2500_ = lean_box(0);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v_ref_2453_);
lean_ctor_set(v___x_2501_, 1, v_a_2478_);
v___x_2502_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2451_, v___x_2501_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2502_);
v___x_2504_ = v___x_2498_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2502_);
lean_ctor_set_uint64(v_reuseFailAlloc_2512_, sizeof(void*)*1, v_tid_2496_);
v___x_2504_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2506_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 4, v___x_2504_);
v___x_2506_ = v___x_2494_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_env_2484_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_nextMacroScope_2485_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_ngen_2486_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_auxDeclNGen_2487_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2511_, 5, v_cache_2488_);
lean_ctor_set(v_reuseFailAlloc_2511_, 6, v_recordedDeps_2489_);
lean_ctor_set(v_reuseFailAlloc_2511_, 7, v_messages_2490_);
lean_ctor_set(v_reuseFailAlloc_2511_, 8, v_infoState_2491_);
lean_ctor_set(v_reuseFailAlloc_2511_, 9, v_snapshotTasks_2492_);
v___x_2506_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = lean_st_ref_put(v___y_2458_, v___x_2506_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2500_);
v___x_2509_ = v___x_2480_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2500_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_oldTraces_2517_, lean_object* v_data_2518_, lean_object* v_ref_2519_, lean_object* v_msg_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2517_, v_data_2518_, v_ref_2519_, v_msg_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2527_, lean_object* v_opt_2528_){
_start:
{
lean_object* v_name_2529_; lean_object* v_defValue_2530_; lean_object* v_map_2531_; lean_object* v___x_2532_; 
v_name_2529_ = lean_ctor_get(v_opt_2528_, 0);
v_defValue_2530_ = lean_ctor_get(v_opt_2528_, 1);
v_map_2531_ = lean_ctor_get(v_opts_2527_, 0);
v___x_2532_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2531_, v_name_2529_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_inc(v_defValue_2530_);
return v_defValue_2530_;
}
else
{
lean_object* v_val_2533_; 
v_val_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_val_2533_);
lean_dec_ref_known(v___x_2532_, 1);
if (lean_obj_tag(v_val_2533_) == 3)
{
lean_object* v_v_2534_; 
v_v_2534_ = lean_ctor_get(v_val_2533_, 0);
lean_inc(v_v_2534_);
lean_dec_ref_known(v_val_2533_, 1);
return v_v_2534_;
}
else
{
lean_dec(v_val_2533_);
lean_inc(v_defValue_2530_);
return v_defValue_2530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2535_, lean_object* v_opt_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2535_, v_opt_2536_);
lean_dec_ref(v_opt_2536_);
lean_dec_ref(v_opts_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_e_2538_){
_start:
{
if (lean_obj_tag(v_e_2538_) == 0)
{
uint8_t v___x_2539_; 
v___x_2539_ = 2;
return v___x_2539_;
}
else
{
uint8_t v___x_2540_; 
v___x_2540_ = 0;
return v___x_2540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_e_2541_){
_start:
{
uint8_t v_res_2542_; lean_object* v_r_2543_; 
v_res_2542_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_e_2541_);
lean_dec_ref(v_e_2541_);
v_r_2543_ = lean_box(v_res_2542_);
return v_r_2543_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object* v_x_2544_){
_start:
{
if (lean_obj_tag(v_x_2544_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_a_2546_ = lean_ctor_get(v_x_2544_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_x_2544_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v_x_2544_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v_x_2544_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set_tag(v___x_2548_, 1);
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
v_a_2554_ = lean_ctor_get(v_x_2544_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_x_2544_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v_x_2544_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v_x_2544_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
lean_ctor_set_tag(v___x_2556_, 0);
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object* v_x_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2562_);
return v_res_2564_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2567_ = l_Lean_stringToMessageData(v___x_2566_);
return v___x_2567_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2568_; double v___x_2569_; 
v___x_2568_ = lean_unsigned_to_nat(1000u);
v___x_2569_ = lean_float_of_nat(v___x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2570_, uint8_t v_collapsed_2571_, lean_object* v_tag_2572_, lean_object* v_opts_2573_, uint8_t v_clsEnabled_2574_, lean_object* v_oldTraces_2575_, lean_object* v_msg_2576_, lean_object* v_resStartStop_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_fst_2583_; lean_object* v_snd_2584_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v_data_2588_; lean_object* v_fst_2591_; lean_object* v_snd_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; lean_object* v___y_2596_; lean_object* v_a_2597_; uint8_t v___y_2612_; double v___y_2644_; 
v_fst_2583_ = lean_ctor_get(v_resStartStop_2577_, 0);
lean_inc(v_fst_2583_);
v_snd_2584_ = lean_ctor_get(v_resStartStop_2577_, 1);
lean_inc(v_snd_2584_);
lean_dec_ref(v_resStartStop_2577_);
v_fst_2591_ = lean_ctor_get(v_snd_2584_, 0);
lean_inc(v_fst_2591_);
v_snd_2592_ = lean_ctor_get(v_snd_2584_, 1);
lean_inc(v_snd_2592_);
lean_dec(v_snd_2584_);
v___x_2593_ = l_Lean_trace_profiler;
v___x_2594_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2573_, v___x_2593_);
if (v___x_2594_ == 0)
{
v___y_2612_ = v___x_2594_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2650_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2573_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; double v___x_2653_; double v___x_2654_; double v___x_2655_; 
v___x_2651_ = l_Lean_trace_profiler_threshold;
v___x_2652_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2573_, v___x_2651_);
v___x_2653_ = lean_float_of_nat(v___x_2652_);
v___x_2654_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2);
v___x_2655_ = lean_float_div(v___x_2653_, v___x_2654_);
v___y_2644_ = v___x_2655_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; double v___x_2658_; 
v___x_2656_ = l_Lean_trace_profiler_threshold;
v___x_2657_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2573_, v___x_2656_);
v___x_2658_ = lean_float_of_nat(v___x_2657_);
v___y_2644_ = v___x_2658_;
goto v___jp_2643_;
}
}
v___jp_2585_:
{
lean_object* v___x_2589_; 
lean_inc(v___y_2587_);
v___x_2589_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2575_, v_data_2588_, v___y_2587_, v___y_2586_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref_known(v___x_2589_, 1);
v___x_2590_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2583_);
return v___x_2590_;
}
else
{
lean_dec(v_fst_2583_);
return v___x_2589_;
}
}
v___jp_2595_:
{
uint8_t v_result_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; double v___x_2601_; lean_object* v_data_2602_; 
v_result_2598_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_fst_2583_);
v___x_2599_ = lean_box(v_result_2598_);
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
v___x_2601_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2572_);
lean_inc_ref(v___x_2600_);
lean_inc(v_cls_2570_);
v_data_2602_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2602_, 0, v_cls_2570_);
lean_ctor_set(v_data_2602_, 1, v___x_2600_);
lean_ctor_set(v_data_2602_, 2, v_tag_2572_);
lean_ctor_set_float(v_data_2602_, sizeof(void*)*3, v___x_2601_);
lean_ctor_set_float(v_data_2602_, sizeof(void*)*3 + 8, v___x_2601_);
lean_ctor_set_uint8(v_data_2602_, sizeof(void*)*3 + 16, v_collapsed_2571_);
if (v___x_2594_ == 0)
{
lean_dec_ref_known(v___x_2600_, 1);
lean_dec(v_snd_2592_);
lean_dec(v_fst_2591_);
lean_dec_ref(v_tag_2572_);
lean_dec(v_cls_2570_);
v___y_2586_ = v_a_2597_;
v___y_2587_ = v___y_2596_;
v_data_2588_ = v_data_2602_;
goto v___jp_2585_;
}
else
{
lean_object* v_data_2603_; double v___x_2604_; double v___x_2605_; 
lean_dec_ref_known(v_data_2602_, 3);
v_data_2603_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2603_, 0, v_cls_2570_);
lean_ctor_set(v_data_2603_, 1, v___x_2600_);
lean_ctor_set(v_data_2603_, 2, v_tag_2572_);
v___x_2604_ = lean_unbox_float(v_fst_2591_);
lean_dec(v_fst_2591_);
lean_ctor_set_float(v_data_2603_, sizeof(void*)*3, v___x_2604_);
v___x_2605_ = lean_unbox_float(v_snd_2592_);
lean_dec(v_snd_2592_);
lean_ctor_set_float(v_data_2603_, sizeof(void*)*3 + 8, v___x_2605_);
lean_ctor_set_uint8(v_data_2603_, sizeof(void*)*3 + 16, v_collapsed_2571_);
v___y_2586_ = v_a_2597_;
v___y_2587_ = v___y_2596_;
v_data_2588_ = v_data_2603_;
goto v___jp_2585_;
}
}
v___jp_2606_:
{
lean_object* v_ref_2607_; lean_object* v___x_2608_; 
v_ref_2607_ = lean_ctor_get(v___y_2580_, 2);
lean_inc(v___y_2581_);
lean_inc_ref(v___y_2580_);
lean_inc(v___y_2579_);
lean_inc_ref(v___y_2578_);
lean_inc(v_fst_2583_);
v___x_2608_ = lean_apply_6(v_msg_2576_, v_fst_2583_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, lean_box(0));
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v___y_2596_ = v_ref_2607_;
v_a_2597_ = v_a_2609_;
goto v___jp_2595_;
}
else
{
lean_object* v___x_2610_; 
lean_dec_ref_known(v___x_2608_, 1);
v___x_2610_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
v___y_2596_ = v_ref_2607_;
v_a_2597_ = v___x_2610_;
goto v___jp_2595_;
}
}
v___jp_2611_:
{
if (v_clsEnabled_2574_ == 0)
{
if (v___y_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v_traceState_2614_; lean_object* v_env_2615_; lean_object* v_nextMacroScope_2616_; lean_object* v_ngen_2617_; lean_object* v_auxDeclNGen_2618_; lean_object* v_cache_2619_; lean_object* v_recordedDeps_2620_; lean_object* v_messages_2621_; lean_object* v_infoState_2622_; lean_object* v_snapshotTasks_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_snd_2592_);
lean_dec(v_fst_2591_);
lean_dec_ref(v_msg_2576_);
lean_dec_ref(v_tag_2572_);
lean_dec(v_cls_2570_);
v___x_2613_ = lean_st_ref_take(v___y_2581_);
v_traceState_2614_ = lean_ctor_get(v___x_2613_, 4);
v_env_2615_ = lean_ctor_get(v___x_2613_, 0);
v_nextMacroScope_2616_ = lean_ctor_get(v___x_2613_, 1);
v_ngen_2617_ = lean_ctor_get(v___x_2613_, 2);
v_auxDeclNGen_2618_ = lean_ctor_get(v___x_2613_, 3);
v_cache_2619_ = lean_ctor_get(v___x_2613_, 5);
v_recordedDeps_2620_ = lean_ctor_get(v___x_2613_, 6);
v_messages_2621_ = lean_ctor_get(v___x_2613_, 7);
v_infoState_2622_ = lean_ctor_get(v___x_2613_, 8);
v_snapshotTasks_2623_ = lean_ctor_get(v___x_2613_, 9);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2625_ = v___x_2613_;
v_isShared_2626_ = v_isSharedCheck_2642_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_snapshotTasks_2623_);
lean_inc(v_infoState_2622_);
lean_inc(v_messages_2621_);
lean_inc(v_recordedDeps_2620_);
lean_inc(v_cache_2619_);
lean_inc(v_traceState_2614_);
lean_inc(v_auxDeclNGen_2618_);
lean_inc(v_ngen_2617_);
lean_inc(v_nextMacroScope_2616_);
lean_inc(v_env_2615_);
lean_dec(v___x_2613_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2642_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
uint64_t v_tid_2627_; lean_object* v_traces_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2641_; 
v_tid_2627_ = lean_ctor_get_uint64(v_traceState_2614_, sizeof(void*)*1);
v_traces_2628_ = lean_ctor_get(v_traceState_2614_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_traceState_2614_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2630_ = v_traceState_2614_;
v_isShared_2631_ = v_isSharedCheck_2641_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_traces_2628_);
lean_dec(v_traceState_2614_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2641_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2575_, v_traces_2628_);
lean_dec_ref(v_traces_2628_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2632_);
lean_ctor_set_uint64(v_reuseFailAlloc_2640_, sizeof(void*)*1, v_tid_2627_);
v___x_2634_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2636_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 4, v___x_2634_);
v___x_2636_ = v___x_2625_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_env_2615_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v_nextMacroScope_2616_);
lean_ctor_set(v_reuseFailAlloc_2639_, 2, v_ngen_2617_);
lean_ctor_set(v_reuseFailAlloc_2639_, 3, v_auxDeclNGen_2618_);
lean_ctor_set(v_reuseFailAlloc_2639_, 4, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2639_, 5, v_cache_2619_);
lean_ctor_set(v_reuseFailAlloc_2639_, 6, v_recordedDeps_2620_);
lean_ctor_set(v_reuseFailAlloc_2639_, 7, v_messages_2621_);
lean_ctor_set(v_reuseFailAlloc_2639_, 8, v_infoState_2622_);
lean_ctor_set(v_reuseFailAlloc_2639_, 9, v_snapshotTasks_2623_);
v___x_2636_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = lean_st_ref_put(v___y_2581_, v___x_2636_);
v___x_2638_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2583_);
return v___x_2638_;
}
}
}
}
}
else
{
goto v___jp_2606_;
}
}
else
{
goto v___jp_2606_;
}
}
v___jp_2643_:
{
double v___x_2645_; double v___x_2646_; double v___x_2647_; uint8_t v___x_2648_; 
v___x_2645_ = lean_unbox_float(v_snd_2592_);
v___x_2646_ = lean_unbox_float(v_fst_2591_);
v___x_2647_ = lean_float_sub(v___x_2645_, v___x_2646_);
v___x_2648_ = lean_float_decLt(v___y_2644_, v___x_2647_);
v___y_2612_ = v___x_2648_;
goto v___jp_2611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2659_, lean_object* v_collapsed_2660_, lean_object* v_tag_2661_, lean_object* v_opts_2662_, lean_object* v_clsEnabled_2663_, lean_object* v_oldTraces_2664_, lean_object* v_msg_2665_, lean_object* v_resStartStop_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v_collapsed_boxed_2672_; uint8_t v_clsEnabled_boxed_2673_; lean_object* v_res_2674_; 
v_collapsed_boxed_2672_ = lean_unbox(v_collapsed_2660_);
v_clsEnabled_boxed_2673_ = lean_unbox(v_clsEnabled_2663_);
v_res_2674_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2659_, v_collapsed_boxed_2672_, v_tag_2661_, v_opts_2662_, v_clsEnabled_boxed_2673_, v_oldTraces_2664_, v_msg_2665_, v_resStartStop_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec_ref(v_opts_2662_);
return v_res_2674_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2675_; double v___x_2676_; 
v___x_2675_ = lean_unsigned_to_nat(1000000000u);
v___x_2676_ = lean_float_of_nat(v___x_2675_);
return v___x_2676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2679_ = l_Lean_stringToMessageData(v___x_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_toConstantVal_2686_; lean_object* v_toCold_2687_; lean_object* v_options_2688_; lean_object* v_name_2689_; lean_object* v_levelParams_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2903_; 
v_toConstantVal_2686_ = lean_ctor_get(v_ctorVal_2680_, 0);
lean_inc_ref(v_toConstantVal_2686_);
v_toCold_2687_ = lean_ctor_get(v_a_2683_, 0);
v_options_2688_ = lean_ctor_get(v_toCold_2687_, 2);
v_name_2689_ = lean_ctor_get(v_toConstantVal_2686_, 0);
v_levelParams_2690_ = lean_ctor_get(v_toConstantVal_2686_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_toConstantVal_2686_);
if (v_isSharedCheck_2903_ == 0)
{
lean_object* v_unused_2904_; 
v_unused_2904_ = lean_ctor_get(v_toConstantVal_2686_, 2);
lean_dec(v_unused_2904_);
v___x_2692_ = v_toConstantVal_2686_;
v_isShared_2693_ = v_isSharedCheck_2903_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_levelParams_2690_);
lean_inc(v_name_2689_);
lean_dec(v_toConstantVal_2686_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2903_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_inheritedTraceOptions_2694_; uint8_t v_hasTrace_2695_; lean_object* v_name_2696_; 
v_inheritedTraceOptions_2694_ = lean_ctor_get(v_toCold_2687_, 11);
v_hasTrace_2695_ = lean_ctor_get_uint8(v_options_2688_, sizeof(void*)*1);
lean_inc(v_name_2689_);
v_name_2696_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2689_);
if (v_hasTrace_2695_ == 0)
{
lean_object* v___x_2697_; 
v___x_2697_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2735_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2735_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2735_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
if (lean_obj_tag(v_a_2698_) == 1)
{
lean_object* v_val_2702_; lean_object* v___x_2703_; 
lean_del_object(v___x_2700_);
v_val_2702_ = lean_ctor_get(v_a_2698_, 0);
lean_inc_n(v_val_2702_, 2);
lean_dec_ref_known(v_a_2698_, 1);
v___x_2703_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2689_, v_val_2702_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2705_; lean_object* v_a_2706_; lean_object* v___x_2707_; lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2722_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2702_, v_a_2682_);
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref(v___x_2705_);
v___x_2707_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2704_, v_a_2682_);
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2722_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2722_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
lean_inc(v_name_2696_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 2, v_a_2706_);
lean_ctor_set(v___x_2692_, 0, v_name_2696_);
v___x_2713_ = v___x_2692_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_name_2696_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_levelParams_2690_);
lean_ctor_set(v_reuseFailAlloc_2721_, 2, v_a_2706_);
v___x_2713_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_name_2696_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2713_);
lean_ctor_set(v___x_2716_, 1, v_a_2708_);
lean_ctor_set(v___x_2716_, 2, v___x_2715_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set_tag(v___x_2710_, 2);
lean_ctor_set(v___x_2710_, 0, v___x_2716_);
v___x_2718_ = v___x_2710_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_addDecl(v___x_2718_, v_hasTrace_2695_, v_a_2683_, v_a_2684_);
return v___x_2719_;
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_val_2702_);
lean_dec(v_name_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_levelParams_2690_);
v_a_2723_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2703_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2703_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
lean_dec(v_a_2698_);
lean_dec(v_name_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v___x_2731_ = lean_box(0);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2731_);
v___x_2733_ = v___x_2700_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_name_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v_a_2736_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2697_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2697_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
else
{
lean_object* v___f_2744_; lean_object* v_cls_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v_a_2752_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v_a_2764_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v_a_2769_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v_a_2780_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v_a_2795_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v_a_2800_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; 
lean_inc(v_name_2696_);
v___f_2744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2744_, 0, v_name_2696_);
v_cls_2745_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2746_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2747_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2748_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2694_, v_options_2688_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2845_ = l_Lean_trace_profiler;
v___x_2846_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2688_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; 
lean_dec_ref(v___f_2744_);
v___x_2847_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2894_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2894_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2894_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
if (lean_obj_tag(v_a_2848_) == 1)
{
lean_object* v_val_2852_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; 
lean_del_object(v___x_2850_);
v_val_2852_ = lean_ctor_get(v_a_2848_, 0);
lean_inc(v_val_2852_);
lean_dec_ref_known(v_a_2848_, 1);
if (v___x_2748_ == 0)
{
v___y_2854_ = v_a_2681_;
v___y_2855_ = v_a_2682_;
v___y_2856_ = v_a_2683_;
v___y_2857_ = v_a_2684_;
goto v___jp_2853_;
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2886_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2852_);
v___x_2887_ = l_Lean_MessageData_ofExpr(v_val_2852_);
v___x_2888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2745_, v___x_2888_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_dec_ref_known(v___x_2889_, 1);
v___y_2854_ = v_a_2681_;
v___y_2855_ = v_a_2682_;
v___y_2856_ = v_a_2683_;
v___y_2857_ = v_a_2684_;
goto v___jp_2853_;
}
else
{
lean_dec(v_val_2852_);
lean_dec(v_name_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
return v___x_2889_;
}
}
v___jp_2853_:
{
lean_object* v___x_2858_; 
lean_inc(v_val_2852_);
v___x_2858_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2689_, v_val_2852_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2877_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2860_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2852_, v___y_2855_);
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
v___x_2862_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2859_, v___y_2855_);
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2877_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2877_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
lean_inc(v_name_2696_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 2, v_a_2861_);
lean_ctor_set(v___x_2692_, 0, v_name_2696_);
v___x_2868_ = v___x_2692_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_name_2696_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_levelParams_2690_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_a_2861_);
v___x_2868_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2869_ = lean_box(0);
v___x_2870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2870_, 0, v_name_2696_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2868_);
lean_ctor_set(v___x_2871_, 1, v_a_2863_);
lean_ctor_set(v___x_2871_, 2, v___x_2870_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set_tag(v___x_2865_, 2);
lean_ctor_set(v___x_2865_, 0, v___x_2871_);
v___x_2873_ = v___x_2865_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_addDecl(v___x_2873_, v___x_2846_, v___y_2856_, v___y_2857_);
return v___x_2874_;
}
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec(v_val_2852_);
lean_dec(v_name_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_levelParams_2690_);
v_a_2878_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2858_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2858_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
lean_dec(v_a_2848_);
lean_dec(v_name_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v___x_2890_ = lean_box(0);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2890_);
v___x_2892_ = v___x_2850_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v_name_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v_a_2895_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2847_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2847_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
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
else
{
lean_del_object(v___x_2692_);
goto v___jp_2808_;
}
}
else
{
lean_del_object(v___x_2692_);
goto v___jp_2808_;
}
v___jp_2749_:
{
lean_object* v___x_2753_; double v___x_2754_; double v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2753_ = lean_io_get_num_heartbeats();
v___x_2754_ = lean_float_of_nat(v___y_2751_);
v___x_2755_ = lean_float_of_nat(v___x_2753_);
v___x_2756_ = lean_box_float(v___x_2754_);
v___x_2757_ = lean_box_float(v___x_2755_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_a_2752_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2745_, v_hasTrace_2695_, v___x_2746_, v_options_2688_, v___x_2748_, v___y_2750_, v___f_2744_, v___x_2759_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
return v___x_2760_;
}
v___jp_2761_:
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_a_2764_);
v___y_2750_ = v___y_2762_;
v___y_2751_ = v___y_2763_;
v_a_2752_ = v___x_2765_;
goto v___jp_2749_;
}
v___jp_2766_:
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_a_2769_);
v___y_2750_ = v___y_2767_;
v___y_2751_ = v___y_2768_;
v_a_2752_ = v___x_2770_;
goto v___jp_2749_;
}
v___jp_2771_:
{
if (lean_obj_tag(v___y_2774_) == 0)
{
lean_object* v_a_2775_; 
v_a_2775_ = lean_ctor_get(v___y_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___y_2774_, 1);
v___y_2767_ = v___y_2772_;
v___y_2768_ = v___y_2773_;
v_a_2769_ = v_a_2775_;
goto v___jp_2766_;
}
else
{
lean_object* v_a_2776_; 
v_a_2776_ = lean_ctor_get(v___y_2774_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___y_2774_, 1);
v___y_2762_ = v___y_2772_;
v___y_2763_ = v___y_2773_;
v_a_2764_ = v_a_2776_;
goto v___jp_2761_;
}
}
v___jp_2777_:
{
lean_object* v___x_2781_; double v___x_2782_; double v___x_2783_; double v___x_2784_; double v___x_2785_; double v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2781_ = lean_io_mono_nanos_now();
v___x_2782_ = lean_float_of_nat(v___y_2778_);
v___x_2783_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2784_ = lean_float_div(v___x_2782_, v___x_2783_);
v___x_2785_ = lean_float_of_nat(v___x_2781_);
v___x_2786_ = lean_float_div(v___x_2785_, v___x_2783_);
v___x_2787_ = lean_box_float(v___x_2784_);
v___x_2788_ = lean_box_float(v___x_2786_);
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v_a_2780_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2745_, v_hasTrace_2695_, v___x_2746_, v_options_2688_, v___x_2748_, v___y_2779_, v___f_2744_, v___x_2790_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
return v___x_2791_;
}
v___jp_2792_:
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2796_, 0, v_a_2795_);
v___y_2778_ = v___y_2793_;
v___y_2779_ = v___y_2794_;
v_a_2780_ = v___x_2796_;
goto v___jp_2777_;
}
v___jp_2797_:
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_a_2800_);
v___y_2778_ = v___y_2798_;
v___y_2779_ = v___y_2799_;
v_a_2780_ = v___x_2801_;
goto v___jp_2777_;
}
v___jp_2802_:
{
if (lean_obj_tag(v___y_2805_) == 0)
{
lean_object* v_a_2806_; 
v_a_2806_ = lean_ctor_get(v___y_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___y_2805_, 1);
v___y_2793_ = v___y_2803_;
v___y_2794_ = v___y_2804_;
v_a_2795_ = v_a_2806_;
goto v___jp_2792_;
}
else
{
lean_object* v_a_2807_; 
v_a_2807_ = lean_ctor_get(v___y_2805_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___y_2805_, 1);
v___y_2798_ = v___y_2803_;
v___y_2799_ = v___y_2804_;
v_a_2800_ = v_a_2807_;
goto v___jp_2797_;
}
}
v___jp_2808_:
{
lean_object* v___x_2809_; lean_object* v_a_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2809_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2684_);
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref(v___x_2809_);
v___x_2811_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2812_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2688_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_io_mono_nanos_now();
v___x_2814_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
if (lean_obj_tag(v_a_2815_) == 1)
{
if (v___x_2748_ == 0)
{
lean_object* v_val_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_val_2816_ = lean_ctor_get(v_a_2815_, 0);
lean_inc(v_val_2816_);
lean_dec_ref_known(v_a_2815_, 1);
v___x_2817_ = lean_box(0);
v___x_2818_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2689_, v_val_2816_, v_name_2696_, v_levelParams_2690_, v___x_2812_, v___x_2817_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
v___y_2803_ = v___x_2813_;
v___y_2804_ = v_a_2810_;
v___y_2805_ = v___x_2818_;
goto v___jp_2802_;
}
else
{
lean_object* v_val_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_val_2819_ = lean_ctor_get(v_a_2815_, 0);
lean_inc_n(v_val_2819_, 2);
lean_dec_ref_known(v_a_2815_, 1);
v___x_2820_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2821_ = l_Lean_MessageData_ofExpr(v_val_2819_);
v___x_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2745_, v___x_2822_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2689_, v_val_2819_, v_name_2696_, v_levelParams_2690_, v___x_2812_, v_a_2824_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
v___y_2803_ = v___x_2813_;
v___y_2804_ = v_a_2810_;
v___y_2805_ = v___x_2825_;
goto v___jp_2802_;
}
else
{
lean_object* v_a_2826_; 
lean_dec(v_val_2819_);
lean_dec(v_name_2696_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v_a_2826_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2823_, 1);
v___y_2798_ = v___x_2813_;
v___y_2799_ = v_a_2810_;
v_a_2800_ = v_a_2826_;
goto v___jp_2797_;
}
}
}
else
{
lean_object* v___x_2827_; 
lean_dec(v_a_2815_);
lean_dec(v_name_2696_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v___x_2827_ = lean_box(0);
v___y_2793_ = v___x_2813_;
v___y_2794_ = v_a_2810_;
v_a_2795_ = v___x_2827_;
goto v___jp_2792_;
}
}
else
{
lean_object* v_a_2828_; 
lean_dec(v_name_2696_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v_a_2828_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2814_, 1);
v___y_2798_ = v___x_2813_;
v___y_2799_ = v_a_2810_;
v_a_2800_ = v_a_2828_;
goto v___jp_2797_;
}
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_io_get_num_heartbeats();
v___x_2830_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
if (lean_obj_tag(v_a_2831_) == 1)
{
if (v___x_2748_ == 0)
{
lean_object* v_val_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_val_2832_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_val_2832_);
lean_dec_ref_known(v_a_2831_, 1);
v___x_2833_ = lean_box(0);
v___x_2834_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2689_, v_val_2832_, v_name_2696_, v_levelParams_2690_, v___x_2833_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
v___y_2772_ = v_a_2810_;
v___y_2773_ = v___x_2829_;
v___y_2774_ = v___x_2834_;
goto v___jp_2771_;
}
else
{
lean_object* v_val_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_val_2835_ = lean_ctor_get(v_a_2831_, 0);
lean_inc_n(v_val_2835_, 2);
lean_dec_ref_known(v_a_2831_, 1);
v___x_2836_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2837_ = l_Lean_MessageData_ofExpr(v_val_2835_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2745_, v___x_2838_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2689_, v_val_2835_, v_name_2696_, v_levelParams_2690_, v_a_2840_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
v___y_2772_ = v_a_2810_;
v___y_2773_ = v___x_2829_;
v___y_2774_ = v___x_2841_;
goto v___jp_2771_;
}
else
{
lean_object* v_a_2842_; 
lean_dec(v_val_2835_);
lean_dec(v_name_2696_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v_a_2842_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2839_, 1);
v___y_2762_ = v_a_2810_;
v___y_2763_ = v___x_2829_;
v_a_2764_ = v_a_2842_;
goto v___jp_2761_;
}
}
}
else
{
lean_object* v___x_2843_; 
lean_dec(v_a_2831_);
lean_dec(v_name_2696_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v___x_2843_ = lean_box(0);
v___y_2767_ = v_a_2810_;
v___y_2768_ = v___x_2829_;
v_a_2769_ = v___x_2843_;
goto v___jp_2766_;
}
}
else
{
lean_object* v_a_2844_; 
lean_dec(v_name_2696_);
lean_dec(v_levelParams_2690_);
lean_dec(v_name_2689_);
v_a_2844_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2830_, 1);
v___y_2762_ = v_a_2810_;
v___y_2763_ = v___x_2829_;
v_a_2764_ = v_a_2844_;
goto v___jp_2761_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_00_u03b1_2912_, lean_object* v_x_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2913_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2920_, lean_object* v_x_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_00_u03b1_2920_, v_x_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2931_){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2933_ = l_Lean_Name_append(v_ctorName_2931_, v___x_2932_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
uint8_t v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = 1;
v___x_2941_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2934_, v___x_2940_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2949_, lean_object* v_t_2950_, lean_object* v_acc_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2950_, v_a_2952_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
v___x_2959_ = l_Lean_Expr_cleanupAnnotations(v_a_2958_);
lean_dec(v_a_2958_);
v___x_2960_ = l_Lean_Expr_isApp(v___x_2959_);
if (v___x_2960_ == 0)
{
lean_dec_ref(v___x_2959_);
goto v___jp_2954_;
}
else
{
lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2959_);
v___x_2962_ = l_Lean_Expr_isApp(v___x_2961_);
if (v___x_2962_ == 0)
{
lean_dec_ref(v___x_2961_);
lean_dec_ref(v___x_2959_);
goto v___jp_2954_;
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2961_);
v___x_2964_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_2965_ = l_Lean_Expr_isConstOf(v___x_2963_, v___x_2964_);
lean_dec_ref(v___x_2963_);
if (v___x_2965_ == 0)
{
lean_dec_ref(v___x_2961_);
lean_dec_ref(v___x_2959_);
goto v___jp_2954_;
}
else
{
lean_object* v_arg_2966_; lean_object* v_arg_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v_arg_2966_ = lean_ctor_get(v___x_2959_, 1);
lean_inc_ref(v_arg_2966_);
lean_dec_ref(v___x_2959_);
v_arg_2967_ = lean_ctor_get(v___x_2961_, 1);
lean_inc_ref(v_arg_2967_);
lean_dec_ref(v___x_2961_);
v___x_2968_ = lean_unsigned_to_nat(0u);
v___x_2969_ = l_Lean_mkProj(v___x_2964_, v___x_2968_, v_e_2949_);
lean_inc_ref(v___x_2969_);
v___x_2970_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2969_, v_arg_2967_, v_acc_2951_, v_a_2952_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2970_, 1);
v_e_2949_ = v___x_2969_;
v_t_2950_ = v_arg_2966_;
v_acc_2951_ = v_a_2971_;
goto _start;
}
else
{
lean_dec_ref(v___x_2969_);
lean_dec_ref(v_arg_2966_);
return v___x_2970_;
}
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v_acc_2951_);
lean_dec_ref(v_e_2949_);
v_a_2973_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2957_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2957_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
v___jp_2954_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_array_push(v_acc_2951_, v_e_2949_);
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
return v___x_2956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_2981_, lean_object* v_t_2982_, lean_object* v_acc_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2981_, v_t_2982_, v_acc_2983_, v_a_2984_);
lean_dec(v_a_2984_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_2987_, lean_object* v_t_2988_, lean_object* v_acc_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2987_, v_t_2988_, v_acc_2989_, v_a_2991_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_2996_, lean_object* v_t_2997_, lean_object* v_acc_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_2996_, v_t_2997_, v_acc_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v___x_3011_; 
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc_ref(v_e_3005_);
v___x_3011_ = lean_infer_type(v_e_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3014_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3005_, v_a_3012_, v___x_3013_, v_a_3007_);
return v___x_3014_;
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v_e_3005_);
v_a_3015_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3011_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3011_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3030_, lean_object* v_x_3031_, lean_object* v_x_3032_, lean_object* v_x_3033_){
_start:
{
lean_object* v_ks_3034_; lean_object* v_vs_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3059_; 
v_ks_3034_ = lean_ctor_get(v_x_3030_, 0);
v_vs_3035_ = lean_ctor_get(v_x_3030_, 1);
v_isSharedCheck_3059_ = !lean_is_exclusive(v_x_3030_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3037_ = v_x_3030_;
v_isShared_3038_ = v_isSharedCheck_3059_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_vs_3035_);
lean_inc(v_ks_3034_);
lean_dec(v_x_3030_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3059_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; uint8_t v___x_3040_; 
v___x_3039_ = lean_array_get_size(v_ks_3034_);
v___x_3040_ = lean_nat_dec_lt(v_x_3031_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3044_; 
lean_dec(v_x_3031_);
v___x_3041_ = lean_array_push(v_ks_3034_, v_x_3032_);
v___x_3042_ = lean_array_push(v_vs_3035_, v_x_3033_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v___x_3042_);
lean_ctor_set(v___x_3037_, 0, v___x_3041_);
v___x_3044_ = v___x_3037_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
else
{
lean_object* v_k_x27_3046_; uint8_t v___x_3047_; 
v_k_x27_3046_ = lean_array_fget_borrowed(v_ks_3034_, v_x_3031_);
v___x_3047_ = l_Lean_instBEqMVarId_beq(v_x_3032_, v_k_x27_3046_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3049_; 
if (v_isShared_3038_ == 0)
{
v___x_3049_ = v___x_3037_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_ks_3034_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_vs_3035_);
v___x_3049_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_unsigned_to_nat(1u);
v___x_3051_ = lean_nat_add(v_x_3031_, v___x_3050_);
lean_dec(v_x_3031_);
v_x_3030_ = v___x_3049_;
v_x_3031_ = v___x_3051_;
goto _start;
}
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3054_ = lean_array_fset(v_ks_3034_, v_x_3031_, v_x_3032_);
v___x_3055_ = lean_array_fset(v_vs_3035_, v_x_3031_, v_x_3033_);
lean_dec(v_x_3031_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v___x_3055_);
lean_ctor_set(v___x_3037_, 0, v___x_3054_);
v___x_3057_ = v___x_3037_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3060_, lean_object* v_k_3061_, lean_object* v_v_3062_){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3060_, v___x_3063_, v_k_3061_, v_v_3062_);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3066_, size_t v_x_3067_, size_t v_x_3068_, lean_object* v_x_3069_, lean_object* v_x_3070_){
_start:
{
if (lean_obj_tag(v_x_3066_) == 0)
{
lean_object* v_es_3071_; size_t v___x_3072_; size_t v___x_3073_; lean_object* v_j_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v_es_3071_ = lean_ctor_get(v_x_3066_, 0);
v___x_3072_ = ((size_t)31ULL);
v___x_3073_ = lean_usize_land(v_x_3067_, v___x_3072_);
v_j_3074_ = lean_usize_to_nat(v___x_3073_);
v___x_3075_ = lean_array_get_size(v_es_3071_);
v___x_3076_ = lean_nat_dec_lt(v_j_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_dec(v_j_3074_);
lean_dec(v_x_3070_);
lean_dec(v_x_3069_);
return v_x_3066_;
}
else
{
lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3115_; 
lean_inc_ref(v_es_3071_);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_x_3066_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v_x_3066_, 0);
lean_dec(v_unused_3116_);
v___x_3078_ = v_x_3066_;
v_isShared_3079_ = v_isSharedCheck_3115_;
goto v_resetjp_3077_;
}
else
{
lean_dec(v_x_3066_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3115_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_v_3080_; lean_object* v___x_3081_; lean_object* v_xs_x27_3082_; lean_object* v___y_3084_; 
v_v_3080_ = lean_array_fget(v_es_3071_, v_j_3074_);
v___x_3081_ = lean_box(0);
v_xs_x27_3082_ = lean_array_fset(v_es_3071_, v_j_3074_, v___x_3081_);
switch(lean_obj_tag(v_v_3080_))
{
case 0:
{
lean_object* v_key_3089_; lean_object* v_val_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3100_; 
v_key_3089_ = lean_ctor_get(v_v_3080_, 0);
v_val_3090_ = lean_ctor_get(v_v_3080_, 1);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_v_3080_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3092_ = v_v_3080_;
v_isShared_3093_ = v_isSharedCheck_3100_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_val_3090_);
lean_inc(v_key_3089_);
lean_dec(v_v_3080_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3100_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
uint8_t v___x_3094_; 
v___x_3094_ = l_Lean_instBEqMVarId_beq(v_x_3069_, v_key_3089_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
lean_del_object(v___x_3092_);
v___x_3095_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3089_, v_val_3090_, v_x_3069_, v_x_3070_);
v___x_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
v___y_3084_ = v___x_3096_;
goto v___jp_3083_;
}
else
{
lean_object* v___x_3098_; 
lean_dec(v_val_3090_);
lean_dec(v_key_3089_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v_x_3070_);
lean_ctor_set(v___x_3092_, 0, v_x_3069_);
v___x_3098_ = v___x_3092_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_x_3069_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_x_3070_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
v___y_3084_ = v___x_3098_;
goto v___jp_3083_;
}
}
}
}
case 1:
{
lean_object* v_node_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3113_; 
v_node_3101_ = lean_ctor_get(v_v_3080_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_v_3080_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3103_ = v_v_3080_;
v_isShared_3104_ = v_isSharedCheck_3113_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_node_3101_);
lean_dec(v_v_3080_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3113_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
size_t v___x_3105_; size_t v___x_3106_; size_t v___x_3107_; size_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3105_ = ((size_t)5ULL);
v___x_3106_ = lean_usize_shift_right(v_x_3067_, v___x_3105_);
v___x_3107_ = ((size_t)1ULL);
v___x_3108_ = lean_usize_add(v_x_3068_, v___x_3107_);
v___x_3109_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3101_, v___x_3106_, v___x_3108_, v_x_3069_, v_x_3070_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3109_);
v___x_3111_ = v___x_3103_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
v___y_3084_ = v___x_3111_;
goto v___jp_3083_;
}
}
}
default: 
{
lean_object* v___x_3114_; 
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_x_3069_);
lean_ctor_set(v___x_3114_, 1, v_x_3070_);
v___y_3084_ = v___x_3114_;
goto v___jp_3083_;
}
}
v___jp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3085_ = lean_array_fset(v_xs_x27_3082_, v_j_3074_, v___y_3084_);
lean_dec(v_j_3074_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3085_);
v___x_3087_ = v___x_3078_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
else
{
lean_object* v_ks_3117_; lean_object* v_vs_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3136_; 
v_ks_3117_ = lean_ctor_get(v_x_3066_, 0);
v_vs_3118_ = lean_ctor_get(v_x_3066_, 1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_x_3066_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3120_ = v_x_3066_;
v_isShared_3121_ = v_isSharedCheck_3136_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_vs_3118_);
lean_inc(v_ks_3117_);
lean_dec(v_x_3066_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3136_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_ks_3117_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_vs_3118_);
v___x_3123_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v_newNode_3124_; size_t v___x_3125_; uint8_t v___x_3126_; 
v_newNode_3124_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3123_, v_x_3069_, v_x_3070_);
v___x_3125_ = ((size_t)7ULL);
v___x_3126_ = lean_usize_dec_le(v___x_3125_, v_x_3068_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3127_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3124_);
v___x_3128_ = lean_unsigned_to_nat(4u);
v___x_3129_ = lean_nat_dec_lt(v___x_3127_, v___x_3128_);
lean_dec(v___x_3127_);
if (v___x_3129_ == 0)
{
lean_object* v_ks_3130_; lean_object* v_vs_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v_ks_3130_ = lean_ctor_get(v_newNode_3124_, 0);
lean_inc_ref(v_ks_3130_);
v_vs_3131_ = lean_ctor_get(v_newNode_3124_, 1);
lean_inc_ref(v_vs_3131_);
lean_dec_ref(v_newNode_3124_);
v___x_3132_ = lean_unsigned_to_nat(0u);
v___x_3133_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3068_, v_ks_3130_, v_vs_3131_, v___x_3132_, v___x_3133_);
lean_dec_ref(v_vs_3131_);
lean_dec_ref(v_ks_3130_);
return v___x_3134_;
}
else
{
return v_newNode_3124_;
}
}
else
{
return v_newNode_3124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3137_, lean_object* v_keys_3138_, lean_object* v_vals_3139_, lean_object* v_i_3140_, lean_object* v_entries_3141_){
_start:
{
lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3142_ = lean_array_get_size(v_keys_3138_);
v___x_3143_ = lean_nat_dec_lt(v_i_3140_, v___x_3142_);
if (v___x_3143_ == 0)
{
lean_dec(v_i_3140_);
return v_entries_3141_;
}
else
{
lean_object* v_k_3144_; lean_object* v_v_3145_; uint64_t v___x_3146_; size_t v_h_3147_; size_t v___x_3148_; lean_object* v___x_3149_; size_t v___x_3150_; size_t v___x_3151_; size_t v___x_3152_; size_t v_h_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v_k_3144_ = lean_array_fget_borrowed(v_keys_3138_, v_i_3140_);
v_v_3145_ = lean_array_fget_borrowed(v_vals_3139_, v_i_3140_);
v___x_3146_ = l_Lean_instHashableMVarId_hash(v_k_3144_);
v_h_3147_ = lean_uint64_to_usize(v___x_3146_);
v___x_3148_ = ((size_t)5ULL);
v___x_3149_ = lean_unsigned_to_nat(1u);
v___x_3150_ = ((size_t)1ULL);
v___x_3151_ = lean_usize_sub(v_depth_3137_, v___x_3150_);
v___x_3152_ = lean_usize_mul(v___x_3148_, v___x_3151_);
v_h_3153_ = lean_usize_shift_right(v_h_3147_, v___x_3152_);
v___x_3154_ = lean_nat_add(v_i_3140_, v___x_3149_);
lean_dec(v_i_3140_);
lean_inc(v_v_3145_);
lean_inc(v_k_3144_);
v___x_3155_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3141_, v_h_3153_, v_depth_3137_, v_k_3144_, v_v_3145_);
v_i_3140_ = v___x_3154_;
v_entries_3141_ = v___x_3155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3157_, lean_object* v_keys_3158_, lean_object* v_vals_3159_, lean_object* v_i_3160_, lean_object* v_entries_3161_){
_start:
{
size_t v_depth_boxed_3162_; lean_object* v_res_3163_; 
v_depth_boxed_3162_ = lean_unbox_usize(v_depth_3157_);
lean_dec(v_depth_3157_);
v_res_3163_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3162_, v_keys_3158_, v_vals_3159_, v_i_3160_, v_entries_3161_);
lean_dec_ref(v_vals_3159_);
lean_dec_ref(v_keys_3158_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3164_, lean_object* v_x_3165_, lean_object* v_x_3166_, lean_object* v_x_3167_, lean_object* v_x_3168_){
_start:
{
size_t v_x_4971__boxed_3169_; size_t v_x_4972__boxed_3170_; lean_object* v_res_3171_; 
v_x_4971__boxed_3169_ = lean_unbox_usize(v_x_3165_);
lean_dec(v_x_3165_);
v_x_4972__boxed_3170_ = lean_unbox_usize(v_x_3166_);
lean_dec(v_x_3166_);
v_res_3171_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3164_, v_x_4971__boxed_3169_, v_x_4972__boxed_3170_, v_x_3167_, v_x_3168_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3172_, lean_object* v_x_3173_, lean_object* v_x_3174_){
_start:
{
uint64_t v___x_3175_; size_t v___x_3176_; size_t v___x_3177_; lean_object* v___x_3178_; 
v___x_3175_ = l_Lean_instHashableMVarId_hash(v_x_3173_);
v___x_3176_ = lean_uint64_to_usize(v___x_3175_);
v___x_3177_ = ((size_t)1ULL);
v___x_3178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3172_, v___x_3176_, v___x_3177_, v_x_3173_, v_x_3174_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3179_, lean_object* v_val_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; lean_object* v_mctx_3184_; lean_object* v_cache_3185_; lean_object* v_zetaDeltaFVarIds_3186_; lean_object* v_postponed_3187_; lean_object* v_diag_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3218_; 
v___x_3183_ = lean_st_ref_take(v___y_3181_);
v_mctx_3184_ = lean_ctor_get(v___x_3183_, 0);
v_cache_3185_ = lean_ctor_get(v___x_3183_, 1);
v_zetaDeltaFVarIds_3186_ = lean_ctor_get(v___x_3183_, 2);
v_postponed_3187_ = lean_ctor_get(v___x_3183_, 3);
v_diag_3188_ = lean_ctor_get(v___x_3183_, 4);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3190_ = v___x_3183_;
v_isShared_3191_ = v_isSharedCheck_3218_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_diag_3188_);
lean_inc(v_postponed_3187_);
lean_inc(v_zetaDeltaFVarIds_3186_);
lean_inc(v_cache_3185_);
lean_inc(v_mctx_3184_);
lean_dec(v___x_3183_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3218_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v_depth_3192_; lean_object* v_levelAssignDepth_3193_; lean_object* v_lmvarCounter_3194_; lean_object* v_mvarCounter_3195_; lean_object* v_lDecls_3196_; lean_object* v_decls_3197_; lean_object* v_userNames_3198_; lean_object* v_lAssignment_3199_; lean_object* v_eAssignment_3200_; lean_object* v_dAssignment_3201_; lean_object* v_instanceTypedMVars_3202_; lean_object* v_synthNormMemo_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3217_; 
v_depth_3192_ = lean_ctor_get(v_mctx_3184_, 0);
v_levelAssignDepth_3193_ = lean_ctor_get(v_mctx_3184_, 1);
v_lmvarCounter_3194_ = lean_ctor_get(v_mctx_3184_, 2);
v_mvarCounter_3195_ = lean_ctor_get(v_mctx_3184_, 3);
v_lDecls_3196_ = lean_ctor_get(v_mctx_3184_, 4);
v_decls_3197_ = lean_ctor_get(v_mctx_3184_, 5);
v_userNames_3198_ = lean_ctor_get(v_mctx_3184_, 6);
v_lAssignment_3199_ = lean_ctor_get(v_mctx_3184_, 7);
v_eAssignment_3200_ = lean_ctor_get(v_mctx_3184_, 8);
v_dAssignment_3201_ = lean_ctor_get(v_mctx_3184_, 9);
v_instanceTypedMVars_3202_ = lean_ctor_get(v_mctx_3184_, 10);
v_synthNormMemo_3203_ = lean_ctor_get(v_mctx_3184_, 11);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_mctx_3184_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3205_ = v_mctx_3184_;
v_isShared_3206_ = v_isSharedCheck_3217_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_synthNormMemo_3203_);
lean_inc(v_instanceTypedMVars_3202_);
lean_inc(v_dAssignment_3201_);
lean_inc(v_eAssignment_3200_);
lean_inc(v_lAssignment_3199_);
lean_inc(v_userNames_3198_);
lean_inc(v_decls_3197_);
lean_inc(v_lDecls_3196_);
lean_inc(v_mvarCounter_3195_);
lean_inc(v_lmvarCounter_3194_);
lean_inc(v_levelAssignDepth_3193_);
lean_inc(v_depth_3192_);
lean_dec(v_mctx_3184_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3217_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3207_ = lean_box(0);
v___x_3208_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3200_, v_mvarId_3179_, v_val_3180_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 8, v___x_3208_);
v___x_3210_ = v___x_3205_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_depth_3192_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_levelAssignDepth_3193_);
lean_ctor_set(v_reuseFailAlloc_3216_, 2, v_lmvarCounter_3194_);
lean_ctor_set(v_reuseFailAlloc_3216_, 3, v_mvarCounter_3195_);
lean_ctor_set(v_reuseFailAlloc_3216_, 4, v_lDecls_3196_);
lean_ctor_set(v_reuseFailAlloc_3216_, 5, v_decls_3197_);
lean_ctor_set(v_reuseFailAlloc_3216_, 6, v_userNames_3198_);
lean_ctor_set(v_reuseFailAlloc_3216_, 7, v_lAssignment_3199_);
lean_ctor_set(v_reuseFailAlloc_3216_, 8, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3216_, 9, v_dAssignment_3201_);
lean_ctor_set(v_reuseFailAlloc_3216_, 10, v_instanceTypedMVars_3202_);
lean_ctor_set(v_reuseFailAlloc_3216_, 11, v_synthNormMemo_3203_);
v___x_3210_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3212_; 
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 0, v___x_3210_);
v___x_3212_ = v___x_3190_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_cache_3185_);
lean_ctor_set(v_reuseFailAlloc_3215_, 2, v_zetaDeltaFVarIds_3186_);
lean_ctor_set(v_reuseFailAlloc_3215_, 3, v_postponed_3187_);
lean_ctor_set(v_reuseFailAlloc_3215_, 4, v_diag_3188_);
v___x_3212_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_st_ref_put(v___y_3181_, v___x_3212_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3207_);
return v___x_3214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3219_, lean_object* v_val_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3219_, v_val_3220_, v___y_3221_);
lean_dec(v___y_3221_);
return v_res_3223_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0));
v___x_3226_ = l_Lean_stringToMessageData(v___x_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3227_, lean_object* v_a_3228_, lean_object* v_x_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1);
v___x_3236_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3235_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3238_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3236_, 1);
lean_inc(v___y_3233_);
lean_inc_ref(v___y_3232_);
lean_inc(v___y_3231_);
lean_inc_ref(v___y_3230_);
v___x_3238_ = lean_apply_7(v___f_3227_, v_a_3237_, v_a_3228_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, lean_box(0));
return v___x_3238_;
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec(v_a_3228_);
lean_dec_ref(v___f_3227_);
v_a_3239_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3236_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3236_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3247_, lean_object* v_a_3248_, lean_object* v_x_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3247_, v_a_3248_, v_x_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v_x_3249_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3256_, lean_object* v_a_3257_, lean_object* v_x_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = lean_box(0);
lean_inc(v___y_3262_);
lean_inc_ref(v___y_3261_);
lean_inc(v___y_3260_);
lean_inc_ref(v___y_3259_);
v___x_3265_ = lean_apply_7(v___f_3256_, v___x_3264_, v_a_3257_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, lean_box(0));
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3266_, lean_object* v_a_3267_, lean_object* v_x_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3266_, v_a_3267_, v_x_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3275_, lean_object* v_____r_3276_, lean_object* v_mvarId_u2082_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3277_, v___x_3275_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3293_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3293_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3293_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_snd_3288_; lean_object* v___x_3289_; lean_object* v___x_3291_; 
v_snd_3288_ = lean_ctor_get(v_a_3284_, 1);
lean_inc(v_snd_3288_);
lean_dec(v_a_3284_);
v___x_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3289_, 0, v_snd_3288_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 0, v___x_3289_);
v___x_3291_ = v___x_3286_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_a_3294_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3283_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3283_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3302_, lean_object* v_____r_3303_, lean_object* v_mvarId_u2082_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
uint8_t v___x_5259__boxed_3310_; lean_object* v_res_3311_; 
v___x_5259__boxed_3310_ = lean_unbox(v___x_3302_);
v_res_3311_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5259__boxed_3310_, v_____r_3303_, v_mvarId_u2082_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
return v_res_3311_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = lean_box(0);
v___x_3321_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3));
v___x_3322_ = l_Lean_mkConst(v___x_3321_, v___x_3320_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v___y_3330_; uint8_t v___x_3350_; lean_object* v___f_3351_; uint8_t v___x_3352_; lean_object* v___x_3353_; 
v___x_3350_ = 0;
v___f_3351_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0));
v___x_3352_ = 1;
lean_inc(v_a_3323_);
v___x_3353_ = l_Lean_MVarId_getType(v_a_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3411_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3411_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3411_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
if (lean_obj_tag(v_a_3354_) == 7)
{
lean_object* v_binderType_3358_; lean_object* v_body_3359_; uint8_t v___x_3360_; 
v_binderType_3358_ = lean_ctor_get(v_a_3354_, 1);
lean_inc_ref(v_binderType_3358_);
v_body_3359_ = lean_ctor_get(v_a_3354_, 2);
lean_inc_ref(v_body_3359_);
lean_dec_ref_known(v_a_3354_, 3);
v___x_3360_ = l_Lean_Expr_hasLooseBVars(v_body_3359_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; 
lean_del_object(v___x_3356_);
v___x_3361_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3358_, v___y_3325_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3363_; uint8_t v___x_3364_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
v___x_3363_ = l_Lean_Expr_cleanupAnnotations(v_a_3362_);
lean_dec(v_a_3362_);
v___x_3364_ = l_Lean_Expr_isApp(v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec_ref(v___x_3363_);
lean_dec_ref(v_body_3359_);
v___x_3365_ = lean_box(0);
v___x_3366_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3351_, v_a_3323_, v___x_3365_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
v___y_3330_ = v___x_3366_;
goto v___jp_3329_;
}
else
{
lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3363_);
v___x_3368_ = l_Lean_Expr_isApp(v___x_3367_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec_ref(v___x_3367_);
lean_dec_ref(v___x_3363_);
lean_dec_ref(v_body_3359_);
v___x_3369_ = lean_box(0);
v___x_3370_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3351_, v_a_3323_, v___x_3369_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
v___y_3330_ = v___x_3370_;
goto v___jp_3329_;
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3371_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3367_);
v___x_3372_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3373_ = l_Lean_Expr_isConstOf(v___x_3371_, v___x_3372_);
lean_dec_ref(v___x_3371_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v___x_3367_);
lean_dec_ref(v___x_3363_);
lean_dec_ref(v_body_3359_);
v___x_3374_ = lean_box(0);
v___x_3375_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3351_, v_a_3323_, v___x_3374_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
v___y_3330_ = v___x_3375_;
goto v___jp_3329_;
}
else
{
lean_object* v_arg_3376_; lean_object* v_arg_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_arg_3376_ = lean_ctor_get(v___x_3363_, 1);
lean_inc_ref(v_arg_3376_);
lean_dec_ref(v___x_3363_);
v_arg_3377_ = lean_ctor_get(v___x_3367_, 1);
lean_inc_ref(v_arg_3377_);
lean_dec_ref(v___x_3367_);
v___x_3378_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4);
v___x_3379_ = l_Lean_mkApp3(v___x_3378_, v_arg_3377_, v_arg_3376_, v_body_3359_);
v___x_3380_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3323_);
v___x_3381_ = l_Lean_MVarId_applyN(v_a_3323_, v___x_3379_, v___x_3380_, v___x_3352_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
if (lean_obj_tag(v_a_3382_) == 1)
{
lean_object* v_tail_3383_; 
v_tail_3383_ = lean_ctor_get(v_a_3382_, 1);
if (lean_obj_tag(v_tail_3383_) == 0)
{
lean_object* v_head_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_dec(v_a_3323_);
v_head_3384_ = lean_ctor_get(v_a_3382_, 0);
lean_inc(v_head_3384_);
lean_dec_ref_known(v_a_3382_, 2);
v___x_3385_ = lean_box(0);
v___x_3386_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3350_, v___x_3385_, v_head_3384_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
v___y_3330_ = v___x_3386_;
goto v___jp_3329_;
}
else
{
lean_object* v___x_3387_; 
v___x_3387_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3351_, v_a_3323_, v_a_3382_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec_ref_known(v_a_3382_, 2);
v___y_3330_ = v___x_3387_;
goto v___jp_3329_;
}
}
else
{
lean_object* v___x_3388_; 
v___x_3388_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3351_, v_a_3323_, v_a_3382_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v_a_3382_);
v___y_3330_ = v___x_3388_;
goto v___jp_3329_;
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v_a_3323_);
v_a_3389_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3381_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3381_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec_ref(v_body_3359_);
lean_dec(v_a_3323_);
v_a_3397_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3361_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3361_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v___x_3406_; 
lean_dec_ref(v_body_3359_);
lean_dec_ref(v_binderType_3358_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v_a_3323_);
v___x_3406_ = v___x_3356_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3323_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
else
{
lean_object* v___x_3409_; 
lean_dec(v_a_3354_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v_a_3323_);
v___x_3409_ = v___x_3356_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3323_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec(v_a_3323_);
v_a_3412_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3353_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3353_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
v___jp_3329_:
{
if (lean_obj_tag(v___y_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3341_; 
v_a_3331_ = lean_ctor_get(v___y_3330_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___y_3330_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3333_ = v___y_3330_;
v_isShared_3334_ = v_isSharedCheck_3341_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___y_3330_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3341_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
if (lean_obj_tag(v_a_3331_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; 
v_a_3335_ = lean_ctor_get(v_a_3331_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v_a_3331_, 1);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v_a_3335_);
v___x_3337_ = v___x_3333_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
else
{
lean_object* v_a_3339_; 
lean_del_object(v___x_3333_);
v_a_3339_ = lean_ctor_get(v_a_3331_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v_a_3331_, 1);
v_a_3323_ = v_a_3339_;
goto _start;
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
v_a_3342_ = lean_ctor_get(v___y_3330_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___y_3330_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___y_3330_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___y_3330_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
return v_res_3426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0));
v___x_3429_ = l_Lean_stringToMessageData(v___x_3428_);
return v___x_3429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = lean_box(0);
v___x_3436_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3437_ = l_Lean_mkConst(v___x_3436_, v___x_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3442_, lean_object* v_xs_3443_, lean_object* v_type_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_box(0);
v___x_3460_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3444_, v___x_3459_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; uint8_t v___x_3465_; uint8_t v___x_3466_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v___x_3462_ = l_Lean_Expr_mvarId_x21(v_a_3461_);
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5);
v___x_3465_ = 1;
v___x_3466_ = 0;
v___x_3470_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6));
v___x_3471_ = lean_box(0);
v___x_3472_ = l_Lean_MVarId_apply(v___x_3462_, v___x_3464_, v___x_3470_, v___x_3471_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3472_, 1);
if (lean_obj_tag(v_a_3473_) == 1)
{
lean_object* v_tail_3474_; 
v_tail_3474_ = lean_ctor_get(v_a_3473_, 1);
lean_inc(v_tail_3474_);
if (lean_obj_tag(v_tail_3474_) == 1)
{
lean_object* v_tail_3475_; 
v_tail_3475_ = lean_ctor_get(v_tail_3474_, 1);
if (lean_obj_tag(v_tail_3475_) == 0)
{
lean_object* v_toConstantVal_3476_; lean_object* v_head_3477_; lean_object* v_head_3478_; lean_object* v_name_3479_; lean_object* v_levelParams_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_toConstantVal_3476_ = lean_ctor_get(v_ctorVal_3442_, 0);
lean_inc_ref(v_toConstantVal_3476_);
lean_dec_ref(v_ctorVal_3442_);
v_head_3477_ = lean_ctor_get(v_a_3473_, 0);
lean_inc(v_head_3477_);
lean_dec_ref_known(v_a_3473_, 2);
v_head_3478_ = lean_ctor_get(v_tail_3474_, 0);
lean_inc(v_head_3478_);
lean_dec_ref_known(v_tail_3474_, 2);
v_name_3479_ = lean_ctor_get(v_toConstantVal_3476_, 0);
lean_inc_n(v_name_3479_, 2);
v_levelParams_3480_ = lean_ctor_get(v_toConstantVal_3476_, 1);
lean_inc(v_levelParams_3480_);
lean_dec_ref(v_toConstantVal_3476_);
v___x_3481_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3479_);
v___x_3482_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3480_, v___x_3463_);
v___x_3483_ = l_Lean_mkConst(v___x_3481_, v___x_3482_);
v___x_3484_ = l_Lean_mkAppN(v___x_3483_, v_xs_3443_);
v___x_3485_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3477_, v___x_3484_, v___y_3446_);
lean_dec_ref(v___x_3485_);
v___x_3486_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3478_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3488_ = l_Lean_MVarId_refl(v_a_3487_, v___x_3465_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_dec_ref_known(v___x_3488_, 1);
lean_dec(v_name_3479_);
goto v___jp_3467_;
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3511_; 
lean_dec(v_a_3461_);
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3511_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3511_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
uint8_t v___x_3493_; 
v___x_3493_ = l_Lean_Exception_isInterrupt(v_a_3489_);
if (v___x_3493_ == 0)
{
uint8_t v___x_3494_; 
lean_inc(v_a_3489_);
v___x_3494_ = l_Lean_Exception_isRuntime(v_a_3489_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_del_object(v___x_3491_);
lean_dec(v_a_3489_);
v___x_3495_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3479_);
v___x_3496_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3495_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
else
{
lean_object* v___x_3506_; 
lean_dec(v_name_3479_);
if (v_isShared_3492_ == 0)
{
v___x_3506_ = v___x_3491_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3489_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
else
{
lean_object* v___x_3509_; 
lean_dec(v_name_3479_);
if (v_isShared_3492_ == 0)
{
v___x_3509_ = v___x_3491_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3489_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec(v_name_3479_);
lean_dec(v_a_3461_);
v_a_3512_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3486_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3486_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3474_, 2);
lean_dec_ref_known(v_a_3473_, 2);
lean_dec(v_a_3461_);
goto v___jp_3450_;
}
}
else
{
lean_dec(v_tail_3474_);
lean_dec_ref_known(v_a_3473_, 2);
lean_dec(v_a_3461_);
goto v___jp_3450_;
}
}
else
{
lean_dec(v_a_3473_);
lean_dec(v_a_3461_);
goto v___jp_3450_;
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec(v_a_3461_);
lean_dec_ref(v_ctorVal_3442_);
v_a_3520_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3472_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3472_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
v___jp_3467_:
{
uint8_t v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = 1;
v___x_3469_ = l_Lean_Meta_mkLambdaFVars(v_xs_3443_, v_a_3461_, v___x_3466_, v___x_3465_, v___x_3466_, v___x_3465_, v___x_3468_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
return v___x_3469_;
}
}
else
{
lean_dec_ref(v_ctorVal_3442_);
return v___x_3460_;
}
v___jp_3450_:
{
lean_object* v_toConstantVal_3451_; lean_object* v_name_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_toConstantVal_3451_ = lean_ctor_get(v_ctorVal_3442_, 0);
lean_inc_ref(v_toConstantVal_3451_);
lean_dec_ref(v_ctorVal_3442_);
v_name_3452_ = lean_ctor_get(v_toConstantVal_3451_, 0);
lean_inc(v_name_3452_);
lean_dec_ref(v_toConstantVal_3451_);
v___x_3453_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1);
v___x_3454_ = l_Lean_MessageData_ofName(v_name_3452_);
v___x_3455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3453_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3457_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
return v___x_3458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3528_, lean_object* v_xs_3529_, lean_object* v_type_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3528_, v_xs_3529_, v_type_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v_xs_3529_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3537_, lean_object* v_targetType_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v___f_3544_; uint8_t v___x_3545_; lean_object* v___x_3546_; 
v___f_3544_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3544_, 0, v_ctorVal_3537_);
v___x_3545_ = 0;
v___x_3546_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3538_, v___f_3544_, v___x_3545_, v___x_3545_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3547_, lean_object* v_targetType_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3547_, v_targetType_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3555_, lean_object* v_val_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3555_, v_val_3556_, v___y_3558_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3563_, lean_object* v_val_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3563_, v_val_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3571_, lean_object* v_a_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3579_, lean_object* v_a_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3579_, v_a_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3588_, v_x_3589_, v_x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3592_, lean_object* v_x_3593_, size_t v_x_3594_, size_t v_x_3595_, lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3593_, v_x_3594_, v_x_3595_, v_x_3596_, v_x_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3599_, lean_object* v_x_3600_, lean_object* v_x_3601_, lean_object* v_x_3602_, lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
size_t v_x_5825__boxed_3605_; size_t v_x_5826__boxed_3606_; lean_object* v_res_3607_; 
v_x_5825__boxed_3605_ = lean_unbox_usize(v_x_3601_);
lean_dec(v_x_3601_);
v_x_5826__boxed_3606_ = lean_unbox_usize(v_x_3602_);
lean_dec(v_x_3602_);
v_res_3607_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3599_, v_x_3600_, v_x_5825__boxed_3605_, v_x_5826__boxed_3606_, v_x_3603_, v_x_3604_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3608_, lean_object* v_n_3609_, lean_object* v_k_3610_, lean_object* v_v_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3609_, v_k_3610_, v_v_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3613_, size_t v_depth_3614_, lean_object* v_keys_3615_, lean_object* v_vals_3616_, lean_object* v_heq_3617_, lean_object* v_i_3618_, lean_object* v_entries_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3614_, v_keys_3615_, v_vals_3616_, v_i_3618_, v_entries_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3621_, lean_object* v_depth_3622_, lean_object* v_keys_3623_, lean_object* v_vals_3624_, lean_object* v_heq_3625_, lean_object* v_i_3626_, lean_object* v_entries_3627_){
_start:
{
size_t v_depth_boxed_3628_; lean_object* v_res_3629_; 
v_depth_boxed_3628_ = lean_unbox_usize(v_depth_3622_);
lean_dec(v_depth_3622_);
v_res_3629_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3621_, v_depth_boxed_3628_, v_keys_3623_, v_vals_3624_, v_heq_3625_, v_i_3626_, v_entries_3627_);
lean_dec_ref(v_vals_3624_);
lean_dec_ref(v_keys_3623_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_, lean_object* v_x_3633_, lean_object* v_x_3634_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3631_, v_x_3632_, v_x_3633_, v_x_3634_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3636_, lean_object* v_val_3637_, lean_object* v_name_3638_, lean_object* v_levelParams_3639_, uint8_t v___x_3640_, uint8_t v_hasTrace_3641_, lean_object* v_____r_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; 
lean_inc_ref(v_val_3637_);
v___x_3648_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3636_, v_val_3637_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3669_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref_known(v___x_3648_, 1);
v___x_3650_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3637_, v___y_3644_);
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3650_);
v___x_3652_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3649_, v___y_3644_);
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3669_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3669_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
lean_inc_n(v_name_3638_, 2);
v___x_3657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3657_, 0, v_name_3638_);
lean_ctor_set(v___x_3657_, 1, v_levelParams_3639_);
lean_ctor_set(v___x_3657_, 2, v_a_3651_);
v___x_3658_ = lean_box(0);
v___x_3659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3659_, 0, v_name_3638_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3657_);
lean_ctor_set(v___x_3660_, 1, v_a_3653_);
lean_ctor_set(v___x_3660_, 2, v___x_3659_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 2);
lean_ctor_set(v___x_3655_, 0, v___x_3660_);
v___x_3662_ = v___x_3655_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_addDecl(v___x_3662_, v___x_3640_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v___x_3664_; uint8_t v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_dec_ref_known(v___x_3663_, 1);
v___x_3664_ = l_Lean_Meta_simpExtension;
v___x_3665_ = 0;
v___x_3666_ = lean_unsigned_to_nat(1000u);
v___x_3667_ = l_Lean_Meta_addSimpTheorem(v___x_3664_, v_name_3638_, v_hasTrace_3641_, v___x_3640_, v___x_3665_, v___x_3666_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
return v___x_3667_;
}
else
{
lean_dec(v_name_3638_);
return v___x_3663_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v_levelParams_3639_);
lean_dec(v_name_3638_);
lean_dec_ref(v_val_3637_);
v_a_3670_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3648_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3648_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3678_, lean_object* v_val_3679_, lean_object* v_name_3680_, lean_object* v_levelParams_3681_, lean_object* v___x_3682_, lean_object* v_hasTrace_3683_, lean_object* v_____r_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
uint8_t v___x_8728__boxed_3690_; uint8_t v_hasTrace_boxed_3691_; lean_object* v_res_3692_; 
v___x_8728__boxed_3690_ = lean_unbox(v___x_3682_);
v_hasTrace_boxed_3691_ = lean_unbox(v_hasTrace_3683_);
v_res_3692_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3678_, v_val_3679_, v_name_3680_, v_levelParams_3681_, v___x_8728__boxed_3690_, v_hasTrace_boxed_3691_, v_____r_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3693_, lean_object* v_val_3694_, lean_object* v_name_3695_, lean_object* v_levelParams_3696_, uint8_t v___x_3697_, lean_object* v_____r_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; 
lean_inc_ref(v_val_3694_);
v___x_3704_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3693_, v_val_3694_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3706_; lean_object* v_a_3707_; lean_object* v___x_3708_; lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3726_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___x_3706_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3694_, v___y_3700_);
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref(v___x_3706_);
v___x_3708_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3705_, v___y_3700_);
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3711_ = v___x_3708_;
v_isShared_3712_ = v_isSharedCheck_3726_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3726_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_inc_n(v_name_3695_, 2);
v___x_3713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3713_, 0, v_name_3695_);
lean_ctor_set(v___x_3713_, 1, v_levelParams_3696_);
lean_ctor_set(v___x_3713_, 2, v_a_3707_);
v___x_3714_ = lean_box(0);
v___x_3715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3715_, 0, v_name_3695_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3713_);
lean_ctor_set(v___x_3716_, 1, v_a_3709_);
lean_ctor_set(v___x_3716_, 2, v___x_3715_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set_tag(v___x_3711_, 2);
lean_ctor_set(v___x_3711_, 0, v___x_3716_);
v___x_3718_ = v___x_3711_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
uint8_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = 0;
v___x_3720_ = l_Lean_addDecl(v___x_3718_, v___x_3719_, v___y_3701_, v___y_3702_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v___x_3721_; uint8_t v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec_ref_known(v___x_3720_, 1);
v___x_3721_ = l_Lean_Meta_simpExtension;
v___x_3722_ = 0;
v___x_3723_ = lean_unsigned_to_nat(1000u);
v___x_3724_ = l_Lean_Meta_addSimpTheorem(v___x_3721_, v_name_3695_, v___x_3697_, v___x_3719_, v___x_3722_, v___x_3723_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
return v___x_3724_;
}
else
{
lean_dec(v_name_3695_);
return v___x_3720_;
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v_levelParams_3696_);
lean_dec(v_name_3695_);
lean_dec_ref(v_val_3694_);
v_a_3727_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3704_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3704_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3735_, lean_object* v_val_3736_, lean_object* v_name_3737_, lean_object* v_levelParams_3738_, lean_object* v___x_3739_, lean_object* v_____r_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
uint8_t v___x_8816__boxed_3746_; lean_object* v_res_3747_; 
v___x_8816__boxed_3746_ = lean_unbox(v___x_3739_);
v_res_3747_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3735_, v_val_3736_, v_name_3737_, v_levelParams_3738_, v___x_8816__boxed_3746_, v_____r_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_){
_start:
{
lean_object* v_toConstantVal_3754_; lean_object* v_toCold_3755_; lean_object* v_options_3756_; lean_object* v_name_3757_; lean_object* v_levelParams_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3980_; 
v_toConstantVal_3754_ = lean_ctor_get(v_ctorVal_3748_, 0);
lean_inc_ref(v_toConstantVal_3754_);
v_toCold_3755_ = lean_ctor_get(v_a_3751_, 0);
v_options_3756_ = lean_ctor_get(v_toCold_3755_, 2);
v_name_3757_ = lean_ctor_get(v_toConstantVal_3754_, 0);
v_levelParams_3758_ = lean_ctor_get(v_toConstantVal_3754_, 1);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_toConstantVal_3754_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; 
v_unused_3981_ = lean_ctor_get(v_toConstantVal_3754_, 2);
lean_dec(v_unused_3981_);
v___x_3760_ = v_toConstantVal_3754_;
v_isShared_3761_ = v_isSharedCheck_3980_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_levelParams_3758_);
lean_inc(v_name_3757_);
lean_dec(v_toConstantVal_3754_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3980_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v_inheritedTraceOptions_3762_; uint8_t v_hasTrace_3763_; lean_object* v_name_3764_; 
v_inheritedTraceOptions_3762_ = lean_ctor_get(v_toCold_3755_, 11);
v_hasTrace_3763_ = lean_ctor_get_uint8(v_options_3756_, sizeof(void*)*1);
v_name_3764_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3757_);
if (v_hasTrace_3763_ == 0)
{
lean_object* v___x_3765_; 
lean_inc_ref(v_ctorVal_3748_);
v___x_3765_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3808_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3768_ = v___x_3765_;
v_isShared_3769_ = v_isSharedCheck_3808_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3808_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
if (lean_obj_tag(v_a_3766_) == 1)
{
lean_object* v_val_3770_; lean_object* v___x_3771_; 
lean_del_object(v___x_3768_);
v_val_3770_ = lean_ctor_get(v_a_3766_, 0);
lean_inc_n(v_val_3770_, 2);
lean_dec_ref_known(v_a_3766_, 1);
v___x_3771_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3748_, v_val_3770_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v___x_3773_; lean_object* v_a_3774_; lean_object* v___x_3775_; lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3795_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___x_3773_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3770_, v_a_3750_);
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref(v___x_3773_);
v___x_3775_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3772_, v_a_3750_);
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3795_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3795_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
lean_inc(v_name_3764_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 2, v_a_3774_);
lean_ctor_set(v___x_3760_, 0, v_name_3764_);
v___x_3781_ = v___x_3760_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_name_3764_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_levelParams_3758_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_a_3774_);
v___x_3781_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
v___x_3782_ = lean_box(0);
lean_inc(v_name_3764_);
v___x_3783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3783_, 0, v_name_3764_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3781_);
lean_ctor_set(v___x_3784_, 1, v_a_3776_);
lean_ctor_set(v___x_3784_, 2, v___x_3783_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set_tag(v___x_3778_, 2);
lean_ctor_set(v___x_3778_, 0, v___x_3784_);
v___x_3786_ = v___x_3778_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3787_; 
v___x_3787_ = l_Lean_addDecl(v___x_3786_, v_hasTrace_3763_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v___x_3788_; uint8_t v___x_3789_; uint8_t v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_dec_ref_known(v___x_3787_, 1);
v___x_3788_ = l_Lean_Meta_simpExtension;
v___x_3789_ = 1;
v___x_3790_ = 0;
v___x_3791_ = lean_unsigned_to_nat(1000u);
v___x_3792_ = l_Lean_Meta_addSimpTheorem(v___x_3788_, v_name_3764_, v___x_3789_, v_hasTrace_3763_, v___x_3790_, v___x_3791_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
return v___x_3792_;
}
else
{
lean_dec(v_name_3764_);
return v___x_3787_;
}
}
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec(v_val_3770_);
lean_dec(v_name_3764_);
lean_del_object(v___x_3760_);
lean_dec(v_levelParams_3758_);
v_a_3796_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3771_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3771_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3806_; 
lean_dec(v_a_3766_);
lean_dec(v_name_3764_);
lean_del_object(v___x_3760_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v___x_3804_ = lean_box(0);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v___x_3804_);
v___x_3806_ = v___x_3768_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
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
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_name_3764_);
lean_del_object(v___x_3760_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v_a_3809_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3765_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3765_);
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
else
{
lean_object* v___f_3817_; lean_object* v_cls_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v_a_3825_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v_a_3837_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v_a_3842_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v_a_3853_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v_a_3868_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v_a_3873_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; 
lean_inc(v_name_3764_);
v___f_3817_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3817_, 0, v_name_3764_);
v_cls_3818_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3819_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3820_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3821_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3762_, v_options_3756_, v___x_3820_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3918_; uint8_t v___x_3919_; 
v___x_3918_ = l_Lean_trace_profiler;
v___x_3919_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3756_, v___x_3918_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; 
lean_dec_ref(v___f_3817_);
lean_inc_ref(v_ctorVal_3748_);
v___x_3920_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3971_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3923_ = v___x_3920_;
v_isShared_3924_ = v_isSharedCheck_3971_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3971_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
if (lean_obj_tag(v_a_3921_) == 1)
{
lean_object* v_val_3925_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; 
lean_del_object(v___x_3923_);
v_val_3925_ = lean_ctor_get(v_a_3921_, 0);
lean_inc(v_val_3925_);
lean_dec_ref_known(v_a_3921_, 1);
if (v___x_3821_ == 0)
{
v___y_3927_ = v_a_3749_;
v___y_3928_ = v_a_3750_;
v___y_3929_ = v_a_3751_;
v___y_3930_ = v_a_3752_;
goto v___jp_3926_;
}
else
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3963_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3925_);
v___x_3964_ = l_Lean_MessageData_ofExpr(v_val_3925_);
v___x_3965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3963_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3818_, v___x_3965_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_dec_ref_known(v___x_3966_, 1);
v___y_3927_ = v_a_3749_;
v___y_3928_ = v_a_3750_;
v___y_3929_ = v_a_3751_;
v___y_3930_ = v_a_3752_;
goto v___jp_3926_;
}
else
{
lean_dec(v_val_3925_);
lean_dec(v_name_3764_);
lean_del_object(v___x_3760_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
return v___x_3966_;
}
}
v___jp_3926_:
{
lean_object* v___x_3931_; 
lean_inc(v_val_3925_);
v___x_3931_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3748_, v_val_3925_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; lean_object* v_a_3934_; lean_object* v___x_3935_; lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3954_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3933_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3925_, v___y_3928_);
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v___x_3933_);
v___x_3935_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3932_, v___y_3928_);
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3938_ = v___x_3935_;
v_isShared_3939_ = v_isSharedCheck_3954_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3935_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3954_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
lean_inc(v_name_3764_);
if (v_isShared_3761_ == 0)
{
lean_ctor_set(v___x_3760_, 2, v_a_3934_);
lean_ctor_set(v___x_3760_, 0, v_name_3764_);
v___x_3941_ = v___x_3760_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_name_3764_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_levelParams_3758_);
lean_ctor_set(v_reuseFailAlloc_3953_, 2, v_a_3934_);
v___x_3941_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3942_ = lean_box(0);
lean_inc(v_name_3764_);
v___x_3943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3943_, 0, v_name_3764_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3941_);
lean_ctor_set(v___x_3944_, 1, v_a_3936_);
lean_ctor_set(v___x_3944_, 2, v___x_3943_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set_tag(v___x_3938_, 2);
lean_ctor_set(v___x_3938_, 0, v___x_3944_);
v___x_3946_ = v___x_3938_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_addDecl(v___x_3946_, v___x_3919_, v___y_3929_, v___y_3930_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v___x_3948_; uint8_t v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_dec_ref_known(v___x_3947_, 1);
v___x_3948_ = l_Lean_Meta_simpExtension;
v___x_3949_ = 0;
v___x_3950_ = lean_unsigned_to_nat(1000u);
v___x_3951_ = l_Lean_Meta_addSimpTheorem(v___x_3948_, v_name_3764_, v_hasTrace_3763_, v___x_3919_, v___x_3949_, v___x_3950_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
return v___x_3951_;
}
else
{
lean_dec(v_name_3764_);
return v___x_3947_;
}
}
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_val_3925_);
lean_dec(v_name_3764_);
lean_del_object(v___x_3760_);
lean_dec(v_levelParams_3758_);
v_a_3955_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3931_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3931_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
lean_dec(v_a_3921_);
lean_dec(v_name_3764_);
lean_del_object(v___x_3760_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v___x_3967_ = lean_box(0);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v___x_3967_);
v___x_3969_ = v___x_3923_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v_name_3764_);
lean_del_object(v___x_3760_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v_a_3972_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3920_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3920_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
else
{
lean_del_object(v___x_3760_);
goto v___jp_3881_;
}
}
else
{
lean_del_object(v___x_3760_);
goto v___jp_3881_;
}
v___jp_3822_:
{
lean_object* v___x_3826_; double v___x_3827_; double v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3826_ = lean_io_get_num_heartbeats();
v___x_3827_ = lean_float_of_nat(v___y_3824_);
v___x_3828_ = lean_float_of_nat(v___x_3826_);
v___x_3829_ = lean_box_float(v___x_3827_);
v___x_3830_ = lean_box_float(v___x_3828_);
v___x_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3829_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
v___x_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3832_, 0, v_a_3825_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
v___x_3833_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3818_, v_hasTrace_3763_, v___x_3819_, v_options_3756_, v___x_3821_, v___y_3823_, v___f_3817_, v___x_3832_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
return v___x_3833_;
}
v___jp_3834_:
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v_a_3837_);
v___y_3823_ = v___y_3835_;
v___y_3824_ = v___y_3836_;
v_a_3825_ = v___x_3838_;
goto v___jp_3822_;
}
v___jp_3839_:
{
lean_object* v___x_3843_; 
v___x_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_a_3842_);
v___y_3823_ = v___y_3840_;
v___y_3824_ = v___y_3841_;
v_a_3825_ = v___x_3843_;
goto v___jp_3822_;
}
v___jp_3844_:
{
if (lean_obj_tag(v___y_3847_) == 0)
{
lean_object* v_a_3848_; 
v_a_3848_ = lean_ctor_get(v___y_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___y_3847_, 1);
v___y_3840_ = v___y_3845_;
v___y_3841_ = v___y_3846_;
v_a_3842_ = v_a_3848_;
goto v___jp_3839_;
}
else
{
lean_object* v_a_3849_; 
v_a_3849_ = lean_ctor_get(v___y_3847_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___y_3847_, 1);
v___y_3835_ = v___y_3845_;
v___y_3836_ = v___y_3846_;
v_a_3837_ = v_a_3849_;
goto v___jp_3834_;
}
}
v___jp_3850_:
{
lean_object* v___x_3854_; double v___x_3855_; double v___x_3856_; double v___x_3857_; double v___x_3858_; double v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3854_ = lean_io_mono_nanos_now();
v___x_3855_ = lean_float_of_nat(v___y_3851_);
v___x_3856_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3857_ = lean_float_div(v___x_3855_, v___x_3856_);
v___x_3858_ = lean_float_of_nat(v___x_3854_);
v___x_3859_ = lean_float_div(v___x_3858_, v___x_3856_);
v___x_3860_ = lean_box_float(v___x_3857_);
v___x_3861_ = lean_box_float(v___x_3859_);
v___x_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3860_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
v___x_3863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3863_, 0, v_a_3853_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3818_, v_hasTrace_3763_, v___x_3819_, v_options_3756_, v___x_3821_, v___y_3852_, v___f_3817_, v___x_3863_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
return v___x_3864_;
}
v___jp_3865_:
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3869_, 0, v_a_3868_);
v___y_3851_ = v___y_3866_;
v___y_3852_ = v___y_3867_;
v_a_3853_ = v___x_3869_;
goto v___jp_3850_;
}
v___jp_3870_:
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3874_, 0, v_a_3873_);
v___y_3851_ = v___y_3871_;
v___y_3852_ = v___y_3872_;
v_a_3853_ = v___x_3874_;
goto v___jp_3850_;
}
v___jp_3875_:
{
if (lean_obj_tag(v___y_3878_) == 0)
{
lean_object* v_a_3879_; 
v_a_3879_ = lean_ctor_get(v___y_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___y_3878_, 1);
v___y_3866_ = v___y_3876_;
v___y_3867_ = v___y_3877_;
v_a_3868_ = v_a_3879_;
goto v___jp_3865_;
}
else
{
lean_object* v_a_3880_; 
v_a_3880_ = lean_ctor_get(v___y_3878_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___y_3878_, 1);
v___y_3871_ = v___y_3876_;
v___y_3872_ = v___y_3877_;
v_a_3873_ = v_a_3880_;
goto v___jp_3870_;
}
}
v___jp_3881_:
{
lean_object* v___x_3882_; lean_object* v_a_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; 
v___x_3882_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3752_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref(v___x_3882_);
v___x_3884_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3885_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3756_, v___x_3884_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3748_);
v___x_3887_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
if (lean_obj_tag(v_a_3888_) == 1)
{
if (v___x_3821_ == 0)
{
lean_object* v_val_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_val_3889_ = lean_ctor_get(v_a_3888_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v_a_3888_, 1);
v___x_3890_ = lean_box(0);
v___x_3891_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3748_, v_val_3889_, v_name_3764_, v_levelParams_3758_, v___x_3885_, v_hasTrace_3763_, v___x_3890_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
v___y_3876_ = v___x_3886_;
v___y_3877_ = v_a_3883_;
v___y_3878_ = v___x_3891_;
goto v___jp_3875_;
}
else
{
lean_object* v_val_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_val_3892_ = lean_ctor_get(v_a_3888_, 0);
lean_inc_n(v_val_3892_, 2);
lean_dec_ref_known(v_a_3888_, 1);
v___x_3893_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3894_ = l_Lean_MessageData_ofExpr(v_val_3892_);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3893_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3818_, v___x_3895_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3898_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3896_, 1);
v___x_3898_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3748_, v_val_3892_, v_name_3764_, v_levelParams_3758_, v___x_3885_, v_hasTrace_3763_, v_a_3897_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
v___y_3876_ = v___x_3886_;
v___y_3877_ = v_a_3883_;
v___y_3878_ = v___x_3898_;
goto v___jp_3875_;
}
else
{
lean_object* v_a_3899_; 
lean_dec(v_val_3892_);
lean_dec(v_name_3764_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v_a_3899_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3896_, 1);
v___y_3871_ = v___x_3886_;
v___y_3872_ = v_a_3883_;
v_a_3873_ = v_a_3899_;
goto v___jp_3870_;
}
}
}
else
{
lean_object* v___x_3900_; 
lean_dec(v_a_3888_);
lean_dec(v_name_3764_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v___x_3900_ = lean_box(0);
v___y_3866_ = v___x_3886_;
v___y_3867_ = v_a_3883_;
v_a_3868_ = v___x_3900_;
goto v___jp_3865_;
}
}
else
{
lean_object* v_a_3901_; 
lean_dec(v_name_3764_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v_a_3901_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3887_, 1);
v___y_3871_ = v___x_3886_;
v___y_3872_ = v_a_3883_;
v_a_3873_ = v_a_3901_;
goto v___jp_3870_;
}
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3748_);
v___x_3903_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
if (lean_obj_tag(v_a_3904_) == 1)
{
if (v___x_3821_ == 0)
{
lean_object* v_val_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_val_3905_ = lean_ctor_get(v_a_3904_, 0);
lean_inc(v_val_3905_);
lean_dec_ref_known(v_a_3904_, 1);
v___x_3906_ = lean_box(0);
v___x_3907_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3748_, v_val_3905_, v_name_3764_, v_levelParams_3758_, v___x_3885_, v___x_3906_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
v___y_3845_ = v_a_3883_;
v___y_3846_ = v___x_3902_;
v___y_3847_ = v___x_3907_;
goto v___jp_3844_;
}
else
{
lean_object* v_val_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_val_3908_ = lean_ctor_get(v_a_3904_, 0);
lean_inc_n(v_val_3908_, 2);
lean_dec_ref_known(v_a_3904_, 1);
v___x_3909_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3910_ = l_Lean_MessageData_ofExpr(v_val_3908_);
v___x_3911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3818_, v___x_3911_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3748_, v_val_3908_, v_name_3764_, v_levelParams_3758_, v___x_3885_, v_a_3913_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
v___y_3845_ = v_a_3883_;
v___y_3846_ = v___x_3902_;
v___y_3847_ = v___x_3914_;
goto v___jp_3844_;
}
else
{
lean_object* v_a_3915_; 
lean_dec(v_val_3908_);
lean_dec(v_name_3764_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v_a_3915_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3912_, 1);
v___y_3835_ = v_a_3883_;
v___y_3836_ = v___x_3902_;
v_a_3837_ = v_a_3915_;
goto v___jp_3834_;
}
}
}
else
{
lean_object* v___x_3916_; 
lean_dec(v_a_3904_);
lean_dec(v_name_3764_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v___x_3916_ = lean_box(0);
v___y_3840_ = v_a_3883_;
v___y_3841_ = v___x_3902_;
v_a_3842_ = v___x_3916_;
goto v___jp_3839_;
}
}
else
{
lean_object* v_a_3917_; 
lean_dec(v_name_3764_);
lean_dec(v_levelParams_3758_);
lean_dec_ref(v_ctorVal_3748_);
v_a_3917_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3903_, 1);
v___y_3835_ = v_a_3883_;
v___y_3836_ = v___x_3902_;
v_a_3837_ = v_a_3917_;
goto v___jp_3834_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3989_, lean_object* v_decl_3990_, lean_object* v_ref_3991_){
_start:
{
lean_object* v_defValue_3993_; lean_object* v_descr_3994_; lean_object* v_deprecation_x3f_3995_; lean_object* v___x_3996_; uint8_t v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_defValue_3993_ = lean_ctor_get(v_decl_3990_, 0);
v_descr_3994_ = lean_ctor_get(v_decl_3990_, 1);
v_deprecation_x3f_3995_ = lean_ctor_get(v_decl_3990_, 2);
v___x_3996_ = lean_alloc_ctor(1, 0, 1);
v___x_3997_ = lean_unbox(v_defValue_3993_);
lean_ctor_set_uint8(v___x_3996_, 0, v___x_3997_);
lean_inc(v_deprecation_x3f_3995_);
lean_inc_ref(v_descr_3994_);
lean_inc_n(v_name_3989_, 2);
v___x_3998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3998_, 0, v_name_3989_);
lean_ctor_set(v___x_3998_, 1, v_ref_3991_);
lean_ctor_set(v___x_3998_, 2, v___x_3996_);
lean_ctor_set(v___x_3998_, 3, v_descr_3994_);
lean_ctor_set(v___x_3998_, 4, v_deprecation_x3f_3995_);
v___x_3999_ = lean_register_option(v_name_3989_, v___x_3998_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4007_; 
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4007_ == 0)
{
lean_object* v_unused_4008_; 
v_unused_4008_ = lean_ctor_get(v___x_3999_, 0);
lean_dec(v_unused_4008_);
v___x_4001_ = v___x_3999_;
v_isShared_4002_ = v_isSharedCheck_4007_;
goto v_resetjp_4000_;
}
else
{
lean_dec(v___x_3999_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4007_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4003_; lean_object* v___x_4005_; 
lean_inc(v_defValue_3993_);
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v_name_3989_);
lean_ctor_set(v___x_4003_, 1, v_defValue_3993_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_4003_);
v___x_4005_ = v___x_4001_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v_name_3989_);
v_a_4009_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3999_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3999_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4017_, lean_object* v_decl_4018_, lean_object* v_ref_4019_, lean_object* v_a_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4017_, v_decl_4018_, v_ref_4019_);
lean_dec_ref(v_decl_4018_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4036_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4037_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4038_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4039_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4036_, v___x_4037_, v___x_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4042_, uint8_t v_isExporting_4043_, lean_object* v___x_4044_, lean_object* v___y_4045_, lean_object* v___x_4046_, lean_object* v_a_x3f_4047_){
_start:
{
lean_object* v___x_4049_; lean_object* v_env_4050_; lean_object* v_nextMacroScope_4051_; lean_object* v_ngen_4052_; lean_object* v_auxDeclNGen_4053_; lean_object* v_traceState_4054_; lean_object* v_recordedDeps_4055_; lean_object* v_messages_4056_; lean_object* v_infoState_4057_; lean_object* v_snapshotTasks_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4083_; 
v___x_4049_ = lean_st_ref_take(v___y_4042_);
v_env_4050_ = lean_ctor_get(v___x_4049_, 0);
v_nextMacroScope_4051_ = lean_ctor_get(v___x_4049_, 1);
v_ngen_4052_ = lean_ctor_get(v___x_4049_, 2);
v_auxDeclNGen_4053_ = lean_ctor_get(v___x_4049_, 3);
v_traceState_4054_ = lean_ctor_get(v___x_4049_, 4);
v_recordedDeps_4055_ = lean_ctor_get(v___x_4049_, 6);
v_messages_4056_ = lean_ctor_get(v___x_4049_, 7);
v_infoState_4057_ = lean_ctor_get(v___x_4049_, 8);
v_snapshotTasks_4058_ = lean_ctor_get(v___x_4049_, 9);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; 
v_unused_4084_ = lean_ctor_get(v___x_4049_, 5);
lean_dec(v_unused_4084_);
v___x_4060_ = v___x_4049_;
v_isShared_4061_ = v_isSharedCheck_4083_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_snapshotTasks_4058_);
lean_inc(v_infoState_4057_);
lean_inc(v_messages_4056_);
lean_inc(v_recordedDeps_4055_);
lean_inc(v_traceState_4054_);
lean_inc(v_auxDeclNGen_4053_);
lean_inc(v_ngen_4052_);
lean_inc(v_nextMacroScope_4051_);
lean_inc(v_env_4050_);
lean_dec(v___x_4049_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4083_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4062_; lean_object* v___x_4064_; 
v___x_4062_ = l_Lean_Environment_setExporting(v_env_4050_, v_isExporting_4043_);
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 5, v___x_4044_);
lean_ctor_set(v___x_4060_, 0, v___x_4062_);
v___x_4064_ = v___x_4060_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_nextMacroScope_4051_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_ngen_4052_);
lean_ctor_set(v_reuseFailAlloc_4082_, 3, v_auxDeclNGen_4053_);
lean_ctor_set(v_reuseFailAlloc_4082_, 4, v_traceState_4054_);
lean_ctor_set(v_reuseFailAlloc_4082_, 5, v___x_4044_);
lean_ctor_set(v_reuseFailAlloc_4082_, 6, v_recordedDeps_4055_);
lean_ctor_set(v_reuseFailAlloc_4082_, 7, v_messages_4056_);
lean_ctor_set(v_reuseFailAlloc_4082_, 8, v_infoState_4057_);
lean_ctor_set(v_reuseFailAlloc_4082_, 9, v_snapshotTasks_4058_);
v___x_4064_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v_mctx_4067_; lean_object* v_zetaDeltaFVarIds_4068_; lean_object* v_postponed_4069_; lean_object* v_diag_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4080_; 
v___x_4065_ = lean_st_ref_put(v___y_4042_, v___x_4064_);
v___x_4066_ = lean_st_ref_take(v___y_4045_);
v_mctx_4067_ = lean_ctor_get(v___x_4066_, 0);
v_zetaDeltaFVarIds_4068_ = lean_ctor_get(v___x_4066_, 2);
v_postponed_4069_ = lean_ctor_get(v___x_4066_, 3);
v_diag_4070_ = lean_ctor_get(v___x_4066_, 4);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; 
v_unused_4081_ = lean_ctor_get(v___x_4066_, 1);
lean_dec(v_unused_4081_);
v___x_4072_ = v___x_4066_;
v_isShared_4073_ = v_isSharedCheck_4080_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_diag_4070_);
lean_inc(v_postponed_4069_);
lean_inc(v_zetaDeltaFVarIds_4068_);
lean_inc(v_mctx_4067_);
lean_dec(v___x_4066_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4080_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4074_; lean_object* v___x_4076_; 
v___x_4074_ = lean_box(0);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 1, v___x_4046_);
v___x_4076_ = v___x_4072_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_mctx_4067_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_zetaDeltaFVarIds_4068_);
lean_ctor_set(v_reuseFailAlloc_4079_, 3, v_postponed_4069_);
lean_ctor_set(v_reuseFailAlloc_4079_, 4, v_diag_4070_);
v___x_4076_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_st_ref_put(v___y_4045_, v___x_4076_);
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4074_);
return v___x_4078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4085_, lean_object* v_isExporting_4086_, lean_object* v___x_4087_, lean_object* v___y_4088_, lean_object* v___x_4089_, lean_object* v_a_x3f_4090_, lean_object* v___y_4091_){
_start:
{
uint8_t v_isExporting_boxed_4092_; lean_object* v_res_4093_; 
v_isExporting_boxed_4092_ = lean_unbox(v_isExporting_4086_);
v_res_4093_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4085_, v_isExporting_boxed_4092_, v___x_4087_, v___y_4088_, v___x_4089_, v_a_x3f_4090_);
lean_dec(v_a_x3f_4090_);
lean_dec(v___y_4088_);
lean_dec(v___y_4085_);
return v_res_4093_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4094_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
return v___x_4096_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4097_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
return v___x_4098_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4100_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
lean_ctor_set(v___x_4100_, 2, v___x_4099_);
lean_ctor_set(v___x_4100_, 3, v___x_4099_);
lean_ctor_set(v___x_4100_, 4, v___x_4099_);
lean_ctor_set(v___x_4100_, 5, v___x_4099_);
lean_ctor_set(v___x_4100_, 6, v___x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4101_, uint8_t v_isExporting_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v___x_4108_; lean_object* v_env_4109_; lean_object* v___x_4110_; uint8_t v_isModule_4111_; 
v___x_4108_ = lean_st_ref_get(v___y_4106_);
v_env_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc_ref(v_env_4109_);
lean_dec(v___x_4108_);
v___x_4110_ = l_Lean_Environment_header(v_env_4109_);
v_isModule_4111_ = lean_ctor_get_uint8(v___x_4110_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4110_);
if (v_isModule_4111_ == 0)
{
lean_object* v___x_4112_; 
lean_dec_ref(v_env_4109_);
lean_inc(v___y_4106_);
lean_inc_ref(v___y_4105_);
lean_inc(v___y_4104_);
lean_inc_ref(v___y_4103_);
v___x_4112_ = lean_apply_5(v_x_4101_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, lean_box(0));
return v___x_4112_;
}
else
{
uint8_t v_isExporting_4113_; 
v_isExporting_4113_ = lean_ctor_get_uint8(v_env_4109_, sizeof(void*)*13);
lean_dec_ref(v_env_4109_);
if (v_isExporting_4102_ == 0)
{
if (v_isExporting_4113_ == 0)
{
lean_object* v___x_4180_; 
lean_inc(v___y_4106_);
lean_inc_ref(v___y_4105_);
lean_inc(v___y_4104_);
lean_inc_ref(v___y_4103_);
v___x_4180_ = lean_apply_5(v_x_4101_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, lean_box(0));
return v___x_4180_;
}
else
{
goto v___jp_4114_;
}
}
else
{
if (v_isExporting_4113_ == 0)
{
goto v___jp_4114_;
}
else
{
lean_object* v___x_4181_; 
lean_inc(v___y_4106_);
lean_inc_ref(v___y_4105_);
lean_inc(v___y_4104_);
lean_inc_ref(v___y_4103_);
v___x_4181_ = lean_apply_5(v_x_4101_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, lean_box(0));
return v___x_4181_;
}
}
v___jp_4114_:
{
lean_object* v___x_4115_; lean_object* v_env_4116_; lean_object* v_nextMacroScope_4117_; lean_object* v_ngen_4118_; lean_object* v_auxDeclNGen_4119_; lean_object* v_traceState_4120_; lean_object* v_recordedDeps_4121_; lean_object* v_messages_4122_; lean_object* v_infoState_4123_; lean_object* v_snapshotTasks_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4178_; 
v___x_4115_ = lean_st_ref_take(v___y_4106_);
v_env_4116_ = lean_ctor_get(v___x_4115_, 0);
v_nextMacroScope_4117_ = lean_ctor_get(v___x_4115_, 1);
v_ngen_4118_ = lean_ctor_get(v___x_4115_, 2);
v_auxDeclNGen_4119_ = lean_ctor_get(v___x_4115_, 3);
v_traceState_4120_ = lean_ctor_get(v___x_4115_, 4);
v_recordedDeps_4121_ = lean_ctor_get(v___x_4115_, 6);
v_messages_4122_ = lean_ctor_get(v___x_4115_, 7);
v_infoState_4123_ = lean_ctor_get(v___x_4115_, 8);
v_snapshotTasks_4124_ = lean_ctor_get(v___x_4115_, 9);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4178_ == 0)
{
lean_object* v_unused_4179_; 
v_unused_4179_ = lean_ctor_get(v___x_4115_, 5);
lean_dec(v_unused_4179_);
v___x_4126_ = v___x_4115_;
v_isShared_4127_ = v_isSharedCheck_4178_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_snapshotTasks_4124_);
lean_inc(v_infoState_4123_);
lean_inc(v_messages_4122_);
lean_inc(v_recordedDeps_4121_);
lean_inc(v_traceState_4120_);
lean_inc(v_auxDeclNGen_4119_);
lean_inc(v_ngen_4118_);
lean_inc(v_nextMacroScope_4117_);
lean_inc(v_env_4116_);
lean_dec(v___x_4115_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4178_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4128_ = l_Lean_Environment_setExporting(v_env_4116_, v_isExporting_4102_);
v___x_4129_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 5, v___x_4129_);
lean_ctor_set(v___x_4126_, 0, v___x_4128_);
v___x_4131_ = v___x_4126_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4128_);
lean_ctor_set(v_reuseFailAlloc_4177_, 1, v_nextMacroScope_4117_);
lean_ctor_set(v_reuseFailAlloc_4177_, 2, v_ngen_4118_);
lean_ctor_set(v_reuseFailAlloc_4177_, 3, v_auxDeclNGen_4119_);
lean_ctor_set(v_reuseFailAlloc_4177_, 4, v_traceState_4120_);
lean_ctor_set(v_reuseFailAlloc_4177_, 5, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4177_, 6, v_recordedDeps_4121_);
lean_ctor_set(v_reuseFailAlloc_4177_, 7, v_messages_4122_);
lean_ctor_set(v_reuseFailAlloc_4177_, 8, v_infoState_4123_);
lean_ctor_set(v_reuseFailAlloc_4177_, 9, v_snapshotTasks_4124_);
v___x_4131_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v_mctx_4134_; lean_object* v_zetaDeltaFVarIds_4135_; lean_object* v_postponed_4136_; lean_object* v_diag_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4175_; 
v___x_4132_ = lean_st_ref_put(v___y_4106_, v___x_4131_);
v___x_4133_ = lean_st_ref_take(v___y_4104_);
v_mctx_4134_ = lean_ctor_get(v___x_4133_, 0);
v_zetaDeltaFVarIds_4135_ = lean_ctor_get(v___x_4133_, 2);
v_postponed_4136_ = lean_ctor_get(v___x_4133_, 3);
v_diag_4137_ = lean_ctor_get(v___x_4133_, 4);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4175_ == 0)
{
lean_object* v_unused_4176_; 
v_unused_4176_ = lean_ctor_get(v___x_4133_, 1);
lean_dec(v_unused_4176_);
v___x_4139_ = v___x_4133_;
v_isShared_4140_ = v_isSharedCheck_4175_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_diag_4137_);
lean_inc(v_postponed_4136_);
lean_inc(v_zetaDeltaFVarIds_4135_);
lean_inc(v_mctx_4134_);
lean_dec(v___x_4133_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4175_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4141_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 1, v___x_4141_);
v___x_4143_ = v___x_4139_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_mctx_4134_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4141_);
lean_ctor_set(v_reuseFailAlloc_4174_, 2, v_zetaDeltaFVarIds_4135_);
lean_ctor_set(v_reuseFailAlloc_4174_, 3, v_postponed_4136_);
lean_ctor_set(v_reuseFailAlloc_4174_, 4, v_diag_4137_);
v___x_4143_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
lean_object* v___x_4144_; lean_object* v_r_4145_; 
v___x_4144_ = lean_st_ref_put(v___y_4104_, v___x_4143_);
lean_inc(v___y_4106_);
lean_inc_ref(v___y_4105_);
lean_inc(v___y_4104_);
lean_inc_ref(v___y_4103_);
v_r_4145_ = lean_apply_5(v_x_4101_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, lean_box(0));
if (lean_obj_tag(v_r_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4162_; 
v_a_4146_ = lean_ctor_get(v_r_4145_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_r_4145_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4148_ = v_r_4145_;
v_isShared_4149_ = v_isSharedCheck_4162_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v_r_4145_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4162_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
lean_inc(v_a_4146_);
if (v_isShared_4149_ == 0)
{
lean_ctor_set_tag(v___x_4148_, 1);
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
v___x_4152_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4106_, v_isExporting_4113_, v___x_4129_, v___y_4104_, v___x_4141_, v___x_4151_);
lean_dec_ref(v___x_4151_);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4159_ == 0)
{
lean_object* v_unused_4160_; 
v_unused_4160_ = lean_ctor_get(v___x_4152_, 0);
lean_dec(v_unused_4160_);
v___x_4154_ = v___x_4152_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_dec(v___x_4152_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v_a_4146_);
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4146_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
v_a_4163_ = lean_ctor_get(v_r_4145_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v_r_4145_, 1);
v___x_4164_ = lean_box(0);
v___x_4165_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4106_, v_isExporting_4113_, v___x_4129_, v___y_4104_, v___x_4141_, v___x_4164_);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4172_ == 0)
{
lean_object* v_unused_4173_; 
v_unused_4173_ = lean_ctor_get(v___x_4165_, 0);
lean_dec(v_unused_4173_);
v___x_4167_ = v___x_4165_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v___x_4165_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
lean_ctor_set_tag(v___x_4167_, 1);
lean_ctor_set(v___x_4167_, 0, v_a_4163_);
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4163_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4182_, lean_object* v_isExporting_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
uint8_t v_isExporting_boxed_4189_; lean_object* v_res_4190_; 
v_isExporting_boxed_4189_ = lean_unbox(v_isExporting_4183_);
v_res_4190_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4182_, v_isExporting_boxed_4189_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4191_, lean_object* v_x_4192_, uint8_t v_isExporting_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4192_, v_isExporting_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4200_, lean_object* v_x_4201_, lean_object* v_isExporting_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
uint8_t v_isExporting_boxed_4208_; lean_object* v_res_4209_; 
v_isExporting_boxed_4208_ = lean_unbox(v_isExporting_4202_);
v_res_4209_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4200_, v_x_4201_, v_isExporting_boxed_4208_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4210_, lean_object* v_localInsts_4211_, lean_object* v_x_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4210_, v_localInsts_4211_, v_x_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
v_a_4227_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4218_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4218_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4235_, lean_object* v_localInsts_4236_, lean_object* v_x_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4235_, v_localInsts_4236_, v_x_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4244_, lean_object* v_lctx_4245_, lean_object* v_localInsts_4246_, lean_object* v_x_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4245_, v_localInsts_4246_, v_x_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4254_, lean_object* v_lctx_4255_, lean_object* v_localInsts_4256_, lean_object* v_x_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4254_, v_lctx_4255_, v_localInsts_4256_, v_x_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4264_, lean_object* v_x_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4271_ = l_Lean_MessageData_ofName(v_declName_4264_);
v___x_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4273_, lean_object* v_x_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4273_, v_x_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec_ref(v_x_4274_);
return v_res_4280_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_instMonadEIO___redArg();
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v_toApplicative_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4355_; 
v___x_4292_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4293_ = l_StateRefT_x27_instMonad___redArg(v___x_4292_);
v_toApplicative_4294_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4355_ == 0)
{
lean_object* v_unused_4356_; 
v_unused_4356_ = lean_ctor_get(v___x_4293_, 1);
lean_dec(v_unused_4356_);
v___x_4296_ = v___x_4293_;
v_isShared_4297_ = v_isSharedCheck_4355_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_toApplicative_4294_);
lean_dec(v___x_4293_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4355_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v_toFunctor_4298_; lean_object* v_toSeq_4299_; lean_object* v_toSeqLeft_4300_; lean_object* v_toSeqRight_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4353_; 
v_toFunctor_4298_ = lean_ctor_get(v_toApplicative_4294_, 0);
v_toSeq_4299_ = lean_ctor_get(v_toApplicative_4294_, 2);
v_toSeqLeft_4300_ = lean_ctor_get(v_toApplicative_4294_, 3);
v_toSeqRight_4301_ = lean_ctor_get(v_toApplicative_4294_, 4);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_toApplicative_4294_);
if (v_isSharedCheck_4353_ == 0)
{
lean_object* v_unused_4354_; 
v_unused_4354_ = lean_ctor_get(v_toApplicative_4294_, 1);
lean_dec(v_unused_4354_);
v___x_4303_ = v_toApplicative_4294_;
v_isShared_4304_ = v_isSharedCheck_4353_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_toSeqRight_4301_);
lean_inc(v_toSeqLeft_4300_);
lean_inc(v_toSeq_4299_);
lean_inc(v_toFunctor_4298_);
lean_dec(v_toApplicative_4294_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4353_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___f_4305_; lean_object* v___f_4306_; lean_object* v___f_4307_; lean_object* v___f_4308_; lean_object* v___x_4309_; lean_object* v___f_4310_; lean_object* v___f_4311_; lean_object* v___f_4312_; lean_object* v___x_4314_; 
v___f_4305_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4306_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4298_);
v___f_4307_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4307_, 0, v_toFunctor_4298_);
v___f_4308_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4308_, 0, v_toFunctor_4298_);
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___f_4307_);
lean_ctor_set(v___x_4309_, 1, v___f_4308_);
v___f_4310_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4310_, 0, v_toSeqRight_4301_);
v___f_4311_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4311_, 0, v_toSeqLeft_4300_);
v___f_4312_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4312_, 0, v_toSeq_4299_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 4, v___f_4310_);
lean_ctor_set(v___x_4303_, 3, v___f_4311_);
lean_ctor_set(v___x_4303_, 2, v___f_4312_);
lean_ctor_set(v___x_4303_, 1, v___f_4305_);
lean_ctor_set(v___x_4303_, 0, v___x_4309_);
v___x_4314_ = v___x_4303_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4309_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v___f_4305_);
lean_ctor_set(v_reuseFailAlloc_4352_, 2, v___f_4312_);
lean_ctor_set(v_reuseFailAlloc_4352_, 3, v___f_4311_);
lean_ctor_set(v_reuseFailAlloc_4352_, 4, v___f_4310_);
v___x_4314_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
lean_object* v___x_4316_; 
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 1, v___f_4306_);
lean_ctor_set(v___x_4296_, 0, v___x_4314_);
v___x_4316_ = v___x_4296_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4314_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v___f_4306_);
v___x_4316_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
lean_object* v___x_4317_; lean_object* v_toApplicative_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4349_; 
v___x_4317_ = l_StateRefT_x27_instMonad___redArg(v___x_4316_);
v_toApplicative_4318_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4349_ == 0)
{
lean_object* v_unused_4350_; 
v_unused_4350_ = lean_ctor_get(v___x_4317_, 1);
lean_dec(v_unused_4350_);
v___x_4320_ = v___x_4317_;
v_isShared_4321_ = v_isSharedCheck_4349_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_toApplicative_4318_);
lean_dec(v___x_4317_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4349_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v_toFunctor_4322_; lean_object* v_toSeq_4323_; lean_object* v_toSeqLeft_4324_; lean_object* v_toSeqRight_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4347_; 
v_toFunctor_4322_ = lean_ctor_get(v_toApplicative_4318_, 0);
v_toSeq_4323_ = lean_ctor_get(v_toApplicative_4318_, 2);
v_toSeqLeft_4324_ = lean_ctor_get(v_toApplicative_4318_, 3);
v_toSeqRight_4325_ = lean_ctor_get(v_toApplicative_4318_, 4);
v_isSharedCheck_4347_ = !lean_is_exclusive(v_toApplicative_4318_);
if (v_isSharedCheck_4347_ == 0)
{
lean_object* v_unused_4348_; 
v_unused_4348_ = lean_ctor_get(v_toApplicative_4318_, 1);
lean_dec(v_unused_4348_);
v___x_4327_ = v_toApplicative_4318_;
v_isShared_4328_ = v_isSharedCheck_4347_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_toSeqRight_4325_);
lean_inc(v_toSeqLeft_4324_);
lean_inc(v_toSeq_4323_);
lean_inc(v_toFunctor_4322_);
lean_dec(v_toApplicative_4318_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4347_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___f_4329_; lean_object* v___f_4330_; lean_object* v___f_4331_; lean_object* v___f_4332_; lean_object* v___x_4333_; lean_object* v___f_4334_; lean_object* v___f_4335_; lean_object* v___f_4336_; lean_object* v___x_4338_; 
v___f_4329_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4330_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4322_);
v___f_4331_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4331_, 0, v_toFunctor_4322_);
v___f_4332_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4332_, 0, v_toFunctor_4322_);
v___x_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___f_4331_);
lean_ctor_set(v___x_4333_, 1, v___f_4332_);
v___f_4334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4334_, 0, v_toSeqRight_4325_);
v___f_4335_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4335_, 0, v_toSeqLeft_4324_);
v___f_4336_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4336_, 0, v_toSeq_4323_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 4, v___f_4334_);
lean_ctor_set(v___x_4327_, 3, v___f_4335_);
lean_ctor_set(v___x_4327_, 2, v___f_4336_);
lean_ctor_set(v___x_4327_, 1, v___f_4329_);
lean_ctor_set(v___x_4327_, 0, v___x_4333_);
v___x_4338_ = v___x_4327_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4333_);
lean_ctor_set(v_reuseFailAlloc_4346_, 1, v___f_4329_);
lean_ctor_set(v_reuseFailAlloc_4346_, 2, v___f_4336_);
lean_ctor_set(v_reuseFailAlloc_4346_, 3, v___f_4335_);
lean_ctor_set(v_reuseFailAlloc_4346_, 4, v___f_4334_);
v___x_4338_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v___x_4340_; 
if (v_isShared_4321_ == 0)
{
lean_ctor_set(v___x_4320_, 1, v___f_4330_);
lean_ctor_set(v___x_4320_, 0, v___x_4338_);
v___x_4340_ = v___x_4320_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4338_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v___f_4330_);
v___x_4340_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_16241__overap_4343_; lean_object* v___x_4344_; 
v___x_4341_ = lean_box(0);
v___x_4342_ = l_instInhabitedOfMonad___redArg(v___x_4340_, v___x_4341_);
v___x_16241__overap_4343_ = lean_panic_fn_borrowed(v___x_4342_, v_msg_4286_);
lean_dec(v___x_4342_);
lean_inc(v___y_4290_);
lean_inc_ref(v___y_4289_);
lean_inc(v___y_4288_);
lean_inc_ref(v___y_4287_);
v___x_4344_ = lean_apply_5(v___x_16241__overap_4343_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, lean_box(0));
return v___x_4344_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
return v_res_4363_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4365_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4366_ = l_Lean_stringToMessageData(v___x_4365_);
return v___x_4366_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4369_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4370_ = lean_unsigned_to_nat(11u);
v___x_4371_ = lean_unsigned_to_nat(122u);
v___x_4372_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4373_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4374_ = l_mkPanicMessageWithDecl(v___x_4373_, v___x_4372_, v___x_4371_, v___x_4370_, v___x_4369_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
lean_object* v___x_4389_; lean_object* v_env_4390_; uint8_t v___x_4391_; lean_object* v___x_4392_; 
v___x_4389_ = lean_st_ref_get(v___y_4379_);
v_env_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc_ref(v_env_4390_);
lean_dec(v___x_4389_);
v___x_4391_ = 0;
lean_inc(v_constName_4375_);
v___x_4392_ = l_Lean_Environment_findAsync_x3f(v_env_4390_, v_constName_4375_, v___x_4391_);
if (lean_obj_tag(v___x_4392_) == 1)
{
lean_object* v_val_4393_; uint8_t v_kind_4394_; 
v_val_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_val_4393_);
lean_dec_ref_known(v___x_4392_, 1);
v_kind_4394_ = lean_ctor_get_uint8(v_val_4393_, sizeof(void*)*3);
if (v_kind_4394_ == 6)
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4393_);
if (lean_obj_tag(v___x_4395_) == 6)
{
lean_object* v_val_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec(v_constName_4375_);
v_val_4396_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4395_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_val_4396_);
lean_dec(v___x_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
lean_ctor_set_tag(v___x_4398_, 0);
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_val_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
else
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
lean_dec_ref(v___x_4395_);
v___x_4404_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4405_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4404_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4414_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4408_ = v___x_4405_;
v_isShared_4409_ = v_isSharedCheck_4414_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4405_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4414_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
if (lean_obj_tag(v_a_4406_) == 0)
{
lean_del_object(v___x_4408_);
goto v___jp_4381_;
}
else
{
lean_object* v_val_4410_; lean_object* v___x_4412_; 
lean_dec(v_constName_4375_);
v_val_4410_ = lean_ctor_get(v_a_4406_, 0);
lean_inc(v_val_4410_);
lean_dec_ref_known(v_a_4406_, 1);
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 0, v_val_4410_);
v___x_4412_ = v___x_4408_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_val_4410_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec(v_constName_4375_);
v_a_4415_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4405_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4405_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
else
{
lean_dec(v_val_4393_);
goto v___jp_4381_;
}
}
else
{
lean_dec(v___x_4392_);
goto v___jp_4381_;
}
v___jp_4381_:
{
lean_object* v___x_4382_; uint8_t v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4382_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4383_ = 0;
v___x_4384_ = l_Lean_MessageData_ofConstName(v_constName_4375_, v___x_4383_);
v___x_4385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4382_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4387_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
return v___x_4388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4430_, lean_object* v___x_4431_, lean_object* v___x_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4430_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4450_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4441_ = v___x_4438_;
v_isShared_4442_ = v_isSharedCheck_4450_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4438_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4450_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v_numFields_4443_; uint8_t v___x_4444_; 
v_numFields_4443_ = lean_ctor_get(v_a_4439_, 4);
v___x_4444_ = lean_nat_dec_lt(v___x_4431_, v_numFields_4443_);
if (v___x_4444_ == 0)
{
lean_object* v___x_4446_; 
lean_dec(v_a_4439_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v___x_4432_);
v___x_4446_ = v___x_4441_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4432_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
else
{
lean_object* v___x_4448_; 
lean_del_object(v___x_4441_);
lean_inc(v_a_4439_);
v___x_4448_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4439_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v___x_4449_; 
lean_dec_ref_known(v___x_4448_, 1);
v___x_4449_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4439_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
return v___x_4449_;
}
else
{
lean_dec(v_a_4439_);
return v___x_4448_;
}
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
v_a_4451_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4438_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4438_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4459_, lean_object* v___x_4460_, lean_object* v___x_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4459_, v___x_4460_, v___x_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec(v___x_4460_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___x_4468_, uint8_t v___x_4469_, lean_object* v_as_x27_4470_, lean_object* v_b_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
if (lean_obj_tag(v_as_x27_4470_) == 0)
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v_b_4471_);
return v___x_4477_;
}
else
{
lean_object* v_head_4478_; lean_object* v_tail_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___f_4482_; uint8_t v___y_4484_; uint8_t v___x_4487_; 
v_head_4478_ = lean_ctor_get(v_as_x27_4470_, 0);
v_tail_4479_ = lean_ctor_get(v_as_x27_4470_, 1);
v___x_4480_ = lean_unsigned_to_nat(0u);
v___x_4481_ = lean_box(0);
lean_inc(v_head_4478_);
v___f_4482_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4482_, 0, v_head_4478_);
lean_closure_set(v___f_4482_, 1, v___x_4480_);
lean_closure_set(v___f_4482_, 2, v___x_4481_);
v___x_4487_ = l_Lean_isPrivateName(v_head_4478_);
if (v___x_4487_ == 0)
{
v___y_4484_ = v___x_4468_;
goto v___jp_4483_;
}
else
{
v___y_4484_ = v___x_4469_;
goto v___jp_4483_;
}
v___jp_4483_:
{
lean_object* v___x_4485_; 
v___x_4485_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4482_, v___y_4484_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_dec_ref_known(v___x_4485_, 1);
v_as_x27_4470_ = v_tail_4479_;
v_b_4471_ = v___x_4481_;
goto _start;
}
else
{
return v___x_4485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___x_4488_, lean_object* v___x_4489_, lean_object* v_as_x27_4490_, lean_object* v_b_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
uint8_t v___x_17336__boxed_4497_; uint8_t v___x_17337__boxed_4498_; lean_object* v_res_4499_; 
v___x_17336__boxed_4497_ = lean_unbox(v___x_4488_);
v___x_17337__boxed_4498_ = lean_unbox(v___x_4489_);
v_res_4499_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_17336__boxed_4497_, v___x_17337__boxed_4498_, v_as_x27_4490_, v_b_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec(v_as_x27_4490_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___x_4500_, uint8_t v_isUnsafe_4501_, lean_object* v_ctors_4502_, lean_object* v___x_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4500_, v_isUnsafe_4501_, v_ctors_4502_, v___x_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4516_ == 0)
{
lean_object* v_unused_4517_; 
v_unused_4517_ = lean_ctor_get(v___x_4509_, 0);
lean_dec(v_unused_4517_);
v___x_4511_ = v___x_4509_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_dec(v___x_4509_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 0, v___x_4503_);
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4503_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
else
{
return v___x_4509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___x_4518_, lean_object* v_isUnsafe_4519_, lean_object* v_ctors_4520_, lean_object* v___x_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
uint8_t v___x_17381__boxed_4527_; uint8_t v_isUnsafe_boxed_4528_; lean_object* v_res_4529_; 
v___x_17381__boxed_4527_ = lean_unbox(v___x_4518_);
v_isUnsafe_boxed_4528_ = lean_unbox(v_isUnsafe_4519_);
v_res_4529_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___x_17381__boxed_4527_, v_isUnsafe_boxed_4528_, v_ctors_4520_, v___x_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec(v_ctors_4520_);
return v_res_4529_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4532_ = l_Lean_stringToMessageData(v___x_4531_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v___x_4539_; lean_object* v_env_4540_; lean_object* v___x_4541_; 
v___x_4539_ = lean_st_ref_get(v___y_4537_);
v_env_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc_ref(v_env_4540_);
lean_dec(v___x_4539_);
lean_inc(v_constName_4533_);
v___x_4541_ = l_Lean_isInductiveCore_x3f(v_env_4540_, v_constName_4533_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v___x_4542_; uint8_t v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4542_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4543_ = 0;
v___x_4544_ = l_Lean_MessageData_ofConstName(v_constName_4533_, v___x_4543_);
v___x_4545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4542_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
v___x_4546_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4545_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
v___x_4548_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4547_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
return v___x_4548_;
}
else
{
lean_object* v_val_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec(v_constName_4533_);
v_val_4549_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4541_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_val_4549_);
lean_dec(v___x_4541_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
lean_ctor_set_tag(v___x_4551_, 0);
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_val_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
return v_res_4563_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4564_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
return v___x_4565_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4566_ = lean_unsigned_to_nat(32u);
v___x_4567_ = lean_mk_empty_array_with_capacity(v___x_4566_);
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
return v___x_4568_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
size_t v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4569_ = ((size_t)5ULL);
v___x_4570_ = lean_unsigned_to_nat(0u);
v___x_4571_ = lean_unsigned_to_nat(32u);
v___x_4572_ = lean_mk_empty_array_with_capacity(v___x_4571_);
v___x_4573_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4574_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4574_, 0, v___x_4573_);
lean_ctor_set(v___x_4574_, 1, v___x_4572_);
lean_ctor_set(v___x_4574_, 2, v___x_4570_);
lean_ctor_set(v___x_4574_, 3, v___x_4570_);
lean_ctor_set_usize(v___x_4574_, 4, v___x_4569_);
return v___x_4574_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4575_ = lean_box(1);
v___x_4576_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4577_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
lean_ctor_set(v___x_4578_, 1, v___x_4576_);
lean_ctor_set(v___x_4578_, 2, v___x_4575_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v___f_4587_; lean_object* v___x_4588_; lean_object* v_env_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
lean_inc_n(v_declName_4581_, 2);
v___f_4587_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4587_, 0, v_declName_4581_);
v___x_4588_ = lean_st_ref_get(v_a_4585_);
v_env_4589_ = lean_ctor_get(v___x_4588_, 0);
lean_inc_ref(v_env_4589_);
lean_dec(v___x_4588_);
v___x_4590_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4584_);
v___x_4591_ = l_Lean_Meta_isInductivePredicate(v_declName_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4755_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4594_ = v___x_4591_;
v_isShared_4595_ = v_isSharedCheck_4755_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4591_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4755_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4601_; uint8_t v___x_4602_; uint8_t v___x_4603_; 
v___x_4601_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_4602_ = 1;
v___x_4603_ = l_Lean_Environment_contains(v_env_4589_, v___x_4601_, v___x_4602_);
if (v___x_4603_ == 0)
{
lean_dec(v_a_4592_);
lean_dec_ref(v___x_4590_);
lean_dec_ref(v___f_4587_);
lean_dec(v_declName_4581_);
goto v___jp_4596_;
}
else
{
lean_object* v___x_4604_; uint8_t v___x_4605_; 
v___x_4604_ = l_Lean_Meta_genInjectivity;
v___x_4605_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___x_4590_, v___x_4604_);
lean_dec_ref(v___x_4590_);
if (v___x_4605_ == 0)
{
lean_dec(v_a_4592_);
lean_dec_ref(v___f_4587_);
lean_dec(v_declName_4581_);
goto v___jp_4596_;
}
else
{
uint8_t v___x_4606_; 
v___x_4606_ = lean_unbox(v_a_4592_);
lean_dec(v_a_4592_);
if (v___x_4606_ == 0)
{
lean_object* v_toCold_4607_; lean_object* v_options_4608_; uint8_t v_hasTrace_4609_; 
lean_del_object(v___x_4594_);
v_toCold_4607_ = lean_ctor_get(v_a_4584_, 0);
v_options_4608_ = lean_ctor_get(v_toCold_4607_, 2);
v_hasTrace_4609_ = lean_ctor_get_uint8(v_options_4608_, sizeof(void*)*1);
if (v_hasTrace_4609_ == 0)
{
lean_object* v___x_4610_; 
lean_dec_ref(v___f_4587_);
v___x_4610_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4628_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4628_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4628_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
uint8_t v_isUnsafe_4615_; 
v_isUnsafe_4615_ = lean_ctor_get_uint8(v_a_4611_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4615_ == 0)
{
lean_object* v_ctors_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___f_4622_; lean_object* v___x_4623_; 
lean_del_object(v___x_4613_);
v_ctors_4616_ = lean_ctor_get(v_a_4611_, 4);
lean_inc(v_ctors_4616_);
lean_dec(v_a_4611_);
v___x_4617_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4618_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4619_ = lean_box(0);
v___x_4620_ = lean_box(v___x_4605_);
v___x_4621_ = lean_box(v_isUnsafe_4615_);
v___f_4622_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4622_, 0, v___x_4620_);
lean_closure_set(v___f_4622_, 1, v___x_4621_);
lean_closure_set(v___f_4622_, 2, v_ctors_4616_);
lean_closure_set(v___f_4622_, 3, v___x_4619_);
v___x_4623_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4617_, v___x_4618_, v___f_4622_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4623_;
}
else
{
lean_object* v___x_4624_; lean_object* v___x_4626_; 
lean_dec(v_a_4611_);
v___x_4624_ = lean_box(0);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4624_);
v___x_4626_ = v___x_4613_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4624_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4636_; 
v_a_4629_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4631_ = v___x_4610_;
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4610_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4636_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4634_; 
if (v_isShared_4632_ == 0)
{
v___x_4634_ = v___x_4631_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; uint8_t v___x_4641_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v_a_4645_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v_a_4660_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v_a_4665_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v_a_4670_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v_a_4682_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v_a_4687_; 
v_inheritedTraceOptions_4637_ = lean_ctor_get(v_toCold_4607_, 11);
v___x_4638_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4639_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4640_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4641_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4637_, v_options_4608_, v___x_4640_);
if (v___x_4641_ == 0)
{
lean_object* v___x_4726_; uint8_t v___x_4727_; 
v___x_4726_ = l_Lean_trace_profiler;
v___x_4727_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4608_, v___x_4726_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4728_; 
lean_dec_ref(v___f_4587_);
v___x_4728_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4746_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4731_ = v___x_4728_;
v_isShared_4732_ = v_isSharedCheck_4746_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4728_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4746_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
uint8_t v_isUnsafe_4733_; 
v_isUnsafe_4733_ = lean_ctor_get_uint8(v_a_4729_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4733_ == 0)
{
lean_object* v_ctors_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___f_4740_; lean_object* v___x_4741_; 
lean_del_object(v___x_4731_);
v_ctors_4734_ = lean_ctor_get(v_a_4729_, 4);
lean_inc(v_ctors_4734_);
lean_dec(v_a_4729_);
v___x_4735_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4736_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4737_ = lean_box(0);
v___x_4738_ = lean_box(v___x_4605_);
v___x_4739_ = lean_box(v_isUnsafe_4733_);
v___f_4740_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4740_, 0, v___x_4738_);
lean_closure_set(v___f_4740_, 1, v___x_4739_);
lean_closure_set(v___f_4740_, 2, v_ctors_4734_);
lean_closure_set(v___f_4740_, 3, v___x_4737_);
v___x_4741_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4735_, v___x_4736_, v___f_4740_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4741_;
}
else
{
lean_object* v___x_4742_; lean_object* v___x_4744_; 
lean_dec(v_a_4729_);
v___x_4742_ = lean_box(0);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 0, v___x_4742_);
v___x_4744_ = v___x_4731_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4742_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
}
else
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4754_; 
v_a_4747_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4749_ = v___x_4728_;
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4728_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4752_; 
if (v_isShared_4750_ == 0)
{
v___x_4752_ = v___x_4749_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
else
{
goto v___jp_4689_;
}
}
else
{
goto v___jp_4689_;
}
v___jp_4642_:
{
lean_object* v___x_4646_; double v___x_4647_; double v___x_4648_; double v___x_4649_; double v___x_4650_; double v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4646_ = lean_io_mono_nanos_now();
v___x_4647_ = lean_float_of_nat(v___y_4643_);
v___x_4648_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4649_ = lean_float_div(v___x_4647_, v___x_4648_);
v___x_4650_ = lean_float_of_nat(v___x_4646_);
v___x_4651_ = lean_float_div(v___x_4650_, v___x_4648_);
v___x_4652_ = lean_box_float(v___x_4649_);
v___x_4653_ = lean_box_float(v___x_4651_);
v___x_4654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4652_);
lean_ctor_set(v___x_4654_, 1, v___x_4653_);
v___x_4655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4655_, 0, v_a_4645_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
v___x_4656_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___x_4638_, v___x_4602_, v___x_4639_, v_options_4608_, v___x_4641_, v___y_4644_, v___f_4587_, v___x_4655_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4656_;
}
v___jp_4657_:
{
lean_object* v___x_4661_; 
v___x_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4661_, 0, v_a_4660_);
v___y_4643_ = v___y_4658_;
v___y_4644_ = v___y_4659_;
v_a_4645_ = v___x_4661_;
goto v___jp_4642_;
}
v___jp_4662_:
{
lean_object* v___x_4666_; 
v___x_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4666_, 0, v_a_4665_);
v___y_4643_ = v___y_4663_;
v___y_4644_ = v___y_4664_;
v_a_4645_ = v___x_4666_;
goto v___jp_4642_;
}
v___jp_4667_:
{
lean_object* v___x_4671_; double v___x_4672_; double v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4671_ = lean_io_get_num_heartbeats();
v___x_4672_ = lean_float_of_nat(v___y_4668_);
v___x_4673_ = lean_float_of_nat(v___x_4671_);
v___x_4674_ = lean_box_float(v___x_4672_);
v___x_4675_ = lean_box_float(v___x_4673_);
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4674_);
lean_ctor_set(v___x_4676_, 1, v___x_4675_);
v___x_4677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4677_, 0, v_a_4670_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
v___x_4678_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___x_4638_, v___x_4602_, v___x_4639_, v_options_4608_, v___x_4641_, v___y_4669_, v___f_4587_, v___x_4677_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
return v___x_4678_;
}
v___jp_4679_:
{
lean_object* v___x_4683_; 
v___x_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4683_, 0, v_a_4682_);
v___y_4668_ = v___y_4680_;
v___y_4669_ = v___y_4681_;
v_a_4670_ = v___x_4683_;
goto v___jp_4667_;
}
v___jp_4684_:
{
lean_object* v___x_4688_; 
v___x_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4688_, 0, v_a_4687_);
v___y_4668_ = v___y_4685_;
v___y_4669_ = v___y_4686_;
v_a_4670_ = v___x_4688_;
goto v___jp_4667_;
}
v___jp_4689_:
{
lean_object* v___x_4690_; lean_object* v_a_4691_; lean_object* v___x_4692_; uint8_t v___x_4693_; 
v___x_4690_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4585_);
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_a_4691_);
lean_dec_ref(v___x_4690_);
v___x_4692_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4693_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4608_, v___x_4692_);
if (v___x_4693_ == 0)
{
lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4694_ = lean_io_mono_nanos_now();
v___x_4695_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; uint8_t v_isUnsafe_4697_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v_isUnsafe_4697_ = lean_ctor_get_uint8(v_a_4696_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4697_ == 0)
{
lean_object* v_ctors_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___f_4704_; lean_object* v___x_4705_; 
v_ctors_4698_ = lean_ctor_get(v_a_4696_, 4);
lean_inc(v_ctors_4698_);
lean_dec(v_a_4696_);
v___x_4699_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4700_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4701_ = lean_box(0);
v___x_4702_ = lean_box(v___x_4605_);
v___x_4703_ = lean_box(v_isUnsafe_4697_);
v___f_4704_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4704_, 0, v___x_4702_);
lean_closure_set(v___f_4704_, 1, v___x_4703_);
lean_closure_set(v___f_4704_, 2, v_ctors_4698_);
lean_closure_set(v___f_4704_, 3, v___x_4701_);
v___x_4705_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4699_, v___x_4700_, v___f_4704_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v_a_4706_; 
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
lean_inc(v_a_4706_);
lean_dec_ref_known(v___x_4705_, 1);
v___y_4663_ = v___x_4694_;
v___y_4664_ = v_a_4691_;
v_a_4665_ = v_a_4706_;
goto v___jp_4662_;
}
else
{
lean_object* v_a_4707_; 
v_a_4707_ = lean_ctor_get(v___x_4705_, 0);
lean_inc(v_a_4707_);
lean_dec_ref_known(v___x_4705_, 1);
v___y_4658_ = v___x_4694_;
v___y_4659_ = v_a_4691_;
v_a_4660_ = v_a_4707_;
goto v___jp_4657_;
}
}
else
{
lean_object* v___x_4708_; 
lean_dec(v_a_4696_);
v___x_4708_ = lean_box(0);
v___y_4663_ = v___x_4694_;
v___y_4664_ = v_a_4691_;
v_a_4665_ = v___x_4708_;
goto v___jp_4662_;
}
}
else
{
lean_object* v_a_4709_; 
v_a_4709_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4709_);
lean_dec_ref_known(v___x_4695_, 1);
v___y_4658_ = v___x_4694_;
v___y_4659_ = v_a_4691_;
v_a_4660_ = v_a_4709_;
goto v___jp_4657_;
}
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = lean_io_get_num_heartbeats();
v___x_4711_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4712_; uint8_t v_isUnsafe_4713_; 
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4712_);
lean_dec_ref_known(v___x_4711_, 1);
v_isUnsafe_4713_ = lean_ctor_get_uint8(v_a_4712_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4713_ == 0)
{
lean_object* v_ctors_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___f_4720_; lean_object* v___x_4721_; 
v_ctors_4714_ = lean_ctor_get(v_a_4712_, 4);
lean_inc(v_ctors_4714_);
lean_dec(v_a_4712_);
v___x_4715_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4716_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4717_ = lean_box(0);
v___x_4718_ = lean_box(v___x_4605_);
v___x_4719_ = lean_box(v_isUnsafe_4713_);
v___f_4720_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4720_, 0, v___x_4718_);
lean_closure_set(v___f_4720_, 1, v___x_4719_);
lean_closure_set(v___f_4720_, 2, v_ctors_4714_);
lean_closure_set(v___f_4720_, 3, v___x_4717_);
v___x_4721_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4715_, v___x_4716_, v___f_4720_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4722_);
lean_dec_ref_known(v___x_4721_, 1);
v___y_4680_ = v___x_4710_;
v___y_4681_ = v_a_4691_;
v_a_4682_ = v_a_4722_;
goto v___jp_4679_;
}
else
{
lean_object* v_a_4723_; 
v_a_4723_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4723_);
lean_dec_ref_known(v___x_4721_, 1);
v___y_4685_ = v___x_4710_;
v___y_4686_ = v_a_4691_;
v_a_4687_ = v_a_4723_;
goto v___jp_4684_;
}
}
else
{
lean_object* v___x_4724_; 
lean_dec(v_a_4712_);
v___x_4724_ = lean_box(0);
v___y_4680_ = v___x_4710_;
v___y_4681_ = v_a_4691_;
v_a_4682_ = v___x_4724_;
goto v___jp_4679_;
}
}
else
{
lean_object* v_a_4725_; 
v_a_4725_ = lean_ctor_get(v___x_4711_, 0);
lean_inc(v_a_4725_);
lean_dec_ref_known(v___x_4711_, 1);
v___y_4685_ = v___x_4710_;
v___y_4686_ = v_a_4691_;
v_a_4687_ = v_a_4725_;
goto v___jp_4684_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_4587_);
lean_dec(v_declName_4581_);
goto v___jp_4596_;
}
}
}
v___jp_4596_:
{
lean_object* v___x_4597_; lean_object* v___x_4599_; 
v___x_4597_ = lean_box(0);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v___x_4597_);
v___x_4599_ = v___x_4594_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4597_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec_ref(v___x_4590_);
lean_dec_ref(v_env_4589_);
lean_dec_ref(v___f_4587_);
lean_dec(v_declName_4581_);
v_a_4756_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4591_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4591_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___x_4771_, uint8_t v___x_4772_, lean_object* v_as_4773_, lean_object* v_as_x27_4774_, lean_object* v_b_4775_, lean_object* v_a_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4771_, v___x_4772_, v_as_x27_4774_, v_b_4775_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___x_4783_, lean_object* v___x_4784_, lean_object* v_as_4785_, lean_object* v_as_x27_4786_, lean_object* v_b_4787_, lean_object* v_a_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_){
_start:
{
uint8_t v___x_17945__boxed_4794_; uint8_t v___x_17946__boxed_4795_; lean_object* v_res_4796_; 
v___x_17945__boxed_4794_ = lean_unbox(v___x_4783_);
v___x_17946__boxed_4795_ = lean_unbox(v___x_4784_);
v_res_4796_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___x_17945__boxed_4794_, v___x_17946__boxed_4795_, v_as_4785_, v_as_x27_4786_, v_b_4787_, v_a_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
lean_dec(v_as_x27_4786_);
lean_dec(v_as_4785_);
return v_res_4796_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4837_ = lean_unsigned_to_nat(4172903888u);
v___x_4838_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4839_ = l_Lean_Name_num___override(v___x_4838_, v___x_4837_);
return v___x_4839_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4841_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4842_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4843_ = l_Lean_Name_str___override(v___x_4842_, v___x_4841_);
return v___x_4843_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4845_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4846_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4847_ = l_Lean_Name_str___override(v___x_4846_, v___x_4845_);
return v___x_4847_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4848_ = lean_unsigned_to_nat(2u);
v___x_4849_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4850_ = l_Lean_Name_num___override(v___x_4849_, v___x_4848_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4852_; uint8_t v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4852_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4853_ = 0;
v___x_4854_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4855_ = l_Lean_registerTraceClass(v___x_4852_, v___x_4853_, v___x_4854_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4858_, lean_object* v_b_4859_){
_start:
{
lean_object* v_array_4860_; lean_object* v_start_4861_; lean_object* v_stop_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4875_; 
v_array_4860_ = lean_ctor_get(v_a_4858_, 0);
v_start_4861_ = lean_ctor_get(v_a_4858_, 1);
v_stop_4862_ = lean_ctor_get(v_a_4858_, 2);
v_isSharedCheck_4875_ = !lean_is_exclusive(v_a_4858_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4864_ = v_a_4858_;
v_isShared_4865_ = v_isSharedCheck_4875_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_stop_4862_);
lean_inc(v_start_4861_);
lean_inc(v_array_4860_);
lean_dec(v_a_4858_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4875_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
uint8_t v___x_4866_; 
v___x_4866_ = lean_nat_dec_lt(v_start_4861_, v_stop_4862_);
if (v___x_4866_ == 0)
{
lean_del_object(v___x_4864_);
lean_dec(v_stop_4862_);
lean_dec(v_start_4861_);
lean_dec_ref(v_array_4860_);
return v_b_4859_;
}
else
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4870_; 
v___x_4867_ = lean_unsigned_to_nat(1u);
v___x_4868_ = lean_nat_add(v_start_4861_, v___x_4867_);
lean_inc_ref(v_array_4860_);
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 1, v___x_4868_);
v___x_4870_ = v___x_4864_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_array_4860_);
lean_ctor_set(v_reuseFailAlloc_4874_, 1, v___x_4868_);
lean_ctor_set(v_reuseFailAlloc_4874_, 2, v_stop_4862_);
v___x_4870_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = lean_array_fget(v_array_4860_, v_start_4861_);
lean_dec(v_start_4861_);
lean_dec_ref(v_array_4860_);
v___x_4872_ = lean_array_push(v_b_4859_, v___x_4871_);
v_a_4858_ = v___x_4870_;
v_b_4859_ = v___x_4872_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4876_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
return v___x_4877_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4878_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4879_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4880_ = lean_unsigned_to_nat(0u);
v___x_4881_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4880_);
lean_ctor_set(v___x_4881_, 1, v___x_4880_);
lean_ctor_set(v___x_4881_, 2, v___x_4880_);
lean_ctor_set(v___x_4881_, 3, v___x_4880_);
lean_ctor_set(v___x_4881_, 4, v___x_4879_);
lean_ctor_set(v___x_4881_, 5, v___x_4879_);
lean_ctor_set(v___x_4881_, 6, v___x_4879_);
lean_ctor_set(v___x_4881_, 7, v___x_4879_);
lean_ctor_set(v___x_4881_, 8, v___x_4879_);
lean_ctor_set(v___x_4881_, 9, v___x_4879_);
lean_ctor_set(v___x_4881_, 10, v___x_4879_);
lean_ctor_set(v___x_4881_, 11, v___x_4878_);
return v___x_4881_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4882_ = lean_box(1);
v___x_4883_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4884_);
lean_ctor_set(v___x_4885_, 1, v___x_4883_);
lean_ctor_set(v___x_4885_, 2, v___x_4882_);
return v___x_4885_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4887_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3));
v___x_4888_ = l_Lean_stringToMessageData(v___x_4887_);
return v___x_4888_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5));
v___x_4891_ = l_Lean_stringToMessageData(v___x_4890_);
return v___x_4891_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4893_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7));
v___x_4894_ = l_Lean_stringToMessageData(v___x_4893_);
return v___x_4894_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10(void){
_start:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4896_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9));
v___x_4897_ = l_Lean_stringToMessageData(v___x_4896_);
return v___x_4897_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12(void){
_start:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4899_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11));
v___x_4900_ = l_Lean_stringToMessageData(v___x_4899_);
return v___x_4900_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14(void){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4902_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13));
v___x_4903_ = l_Lean_stringToMessageData(v___x_4902_);
return v___x_4903_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16(void){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15));
v___x_4906_ = l_Lean_stringToMessageData(v___x_4905_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4907_, lean_object* v_declHint_4908_, lean_object* v___y_4909_){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v_env_4913_; uint8_t v___x_4914_; 
v___x_4911_ = lean_box(0);
v___x_4912_ = lean_st_ref_get(v___y_4909_);
v_env_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc_ref(v_env_4913_);
lean_dec(v___x_4912_);
v___x_4914_ = l_Lean_Name_isAnonymous(v_declHint_4908_);
if (v___x_4914_ == 0)
{
uint8_t v_isExporting_4915_; 
v_isExporting_4915_ = lean_ctor_get_uint8(v_env_4913_, sizeof(void*)*13);
if (v_isExporting_4915_ == 0)
{
lean_object* v___x_4916_; 
lean_dec_ref(v_env_4913_);
lean_dec(v_declHint_4908_);
v___x_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4916_, 0, v_msg_4907_);
return v___x_4916_;
}
else
{
lean_object* v___x_4917_; uint8_t v___x_4918_; 
lean_inc_ref(v_env_4913_);
v___x_4917_ = l_Lean_Environment_setExporting(v_env_4913_, v___x_4914_);
lean_inc(v_declHint_4908_);
lean_inc_ref(v___x_4917_);
v___x_4918_ = l_Lean_Environment_contains(v___x_4917_, v_declHint_4908_, v_isExporting_4915_);
if (v___x_4918_ == 0)
{
lean_object* v___x_4919_; 
lean_dec_ref(v___x_4917_);
lean_dec_ref(v_env_4913_);
lean_dec(v_declHint_4908_);
v___x_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4919_, 0, v_msg_4907_);
return v___x_4919_;
}
else
{
lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v_c_4925_; lean_object* v___x_4926_; 
v___x_4920_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4922_ = l_Lean_Options_empty;
lean_inc_ref(v___x_4917_);
v___x_4923_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4917_);
lean_ctor_set(v___x_4923_, 1, v___x_4920_);
lean_ctor_set(v___x_4923_, 2, v___x_4921_);
lean_ctor_set(v___x_4923_, 3, v___x_4922_);
lean_inc(v_declHint_4908_);
v___x_4924_ = l_Lean_MessageData_ofConstName(v_declHint_4908_, v___x_4914_);
v_c_4925_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4925_, 0, v___x_4923_);
lean_ctor_set(v_c_4925_, 1, v___x_4924_);
v___x_4926_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_4917_, v_declHint_4908_);
lean_dec_ref(v___x_4917_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_dec_ref(v_env_4913_);
lean_dec(v_declHint_4908_);
v___x_4927_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
lean_ctor_set(v___x_4928_, 1, v_c_4925_);
v___x_4929_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_4930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4928_);
lean_ctor_set(v___x_4930_, 1, v___x_4929_);
v___x_4931_ = l_Lean_MessageData_note(v___x_4930_);
v___x_4932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4932_, 0, v_msg_4907_);
lean_ctor_set(v___x_4932_, 1, v___x_4931_);
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4932_);
return v___x_4933_;
}
else
{
lean_object* v_val_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4968_; 
v_val_4934_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4936_ = v___x_4926_;
v_isShared_4937_ = v_isSharedCheck_4968_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_val_4934_);
lean_dec(v___x_4926_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4968_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4938_; lean_object* v_moduleNames_4939_; lean_object* v_mod_4940_; uint8_t v___x_4941_; 
v___x_4938_ = l_Lean_Environment_header(v_env_4913_);
lean_dec_ref(v_env_4913_);
v_moduleNames_4939_ = lean_ctor_get(v___x_4938_, 4);
lean_inc_ref(v_moduleNames_4939_);
lean_dec_ref(v___x_4938_);
v_mod_4940_ = lean_array_get(v___x_4911_, v_moduleNames_4939_, v_val_4934_);
lean_dec(v_val_4934_);
lean_dec_ref(v_moduleNames_4939_);
v___x_4941_ = l_Lean_isPrivateName(v_declHint_4908_);
lean_dec(v_declHint_4908_);
if (v___x_4941_ == 0)
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4953_; 
v___x_4942_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8);
v___x_4943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4942_);
lean_ctor_set(v___x_4943_, 1, v_c_4925_);
v___x_4944_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10);
v___x_4945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4943_);
lean_ctor_set(v___x_4945_, 1, v___x_4944_);
v___x_4946_ = l_Lean_MessageData_ofName(v_mod_4940_);
v___x_4947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4945_);
lean_ctor_set(v___x_4947_, 1, v___x_4946_);
v___x_4948_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12);
v___x_4949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4947_);
lean_ctor_set(v___x_4949_, 1, v___x_4948_);
v___x_4950_ = l_Lean_MessageData_note(v___x_4949_);
v___x_4951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4951_, 0, v_msg_4907_);
lean_ctor_set(v___x_4951_, 1, v___x_4950_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set_tag(v___x_4936_, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4951_);
v___x_4953_ = v___x_4936_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4951_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
else
{
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4966_; 
v___x_4955_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
lean_ctor_set(v___x_4956_, 1, v_c_4925_);
v___x_4957_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14);
v___x_4958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4956_);
lean_ctor_set(v___x_4958_, 1, v___x_4957_);
v___x_4959_ = l_Lean_MessageData_ofName(v_mod_4940_);
v___x_4960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4958_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___x_4961_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16);
v___x_4962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4960_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = l_Lean_MessageData_note(v___x_4962_);
v___x_4964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4964_, 0, v_msg_4907_);
lean_ctor_set(v___x_4964_, 1, v___x_4963_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set_tag(v___x_4936_, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4964_);
v___x_4966_ = v___x_4936_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4964_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4969_; 
lean_dec_ref(v_env_4913_);
lean_dec(v_declHint_4908_);
v___x_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4969_, 0, v_msg_4907_);
return v___x_4969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_4970_, lean_object* v_declHint_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4970_, v_declHint_4971_, v___y_4972_);
lean_dec(v___y_4972_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_4975_, lean_object* v_declHint_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_){
_start:
{
lean_object* v___x_4982_; lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4992_; 
v___x_4982_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4975_, v_declHint_4976_, v___y_4980_);
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4985_ = v___x_4982_;
v_isShared_4986_ = v_isSharedCheck_4992_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4982_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4992_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4990_; 
v___x_4987_ = l_Lean_unknownIdentifierMessageTag;
v___x_4988_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4988_, 0, v___x_4987_);
lean_ctor_set(v___x_4988_, 1, v_a_4983_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_4988_);
v___x_4990_ = v___x_4985_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4988_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_4993_, lean_object* v_declHint_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_4993_, v_declHint_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5001_, lean_object* v_msg_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_toCold_5008_; lean_object* v_currRecDepth_5009_; lean_object* v_ref_5010_; uint16_t v_optionFlags_5011_; uint8_t v_suppressElabErrors_5012_; uint8_t v_checkDeprecated_5013_; uint8_t v_isRecordingDeps_5014_; lean_object* v_ref_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v_toCold_5008_ = lean_ctor_get(v___y_5005_, 0);
v_currRecDepth_5009_ = lean_ctor_get(v___y_5005_, 1);
v_ref_5010_ = lean_ctor_get(v___y_5005_, 2);
v_optionFlags_5011_ = lean_ctor_get_uint16(v___y_5005_, sizeof(void*)*3);
v_suppressElabErrors_5012_ = lean_ctor_get_uint8(v___y_5005_, sizeof(void*)*3 + 2);
v_checkDeprecated_5013_ = lean_ctor_get_uint8(v___y_5005_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5014_ = lean_ctor_get_uint8(v___y_5005_, sizeof(void*)*3 + 4);
v_ref_5015_ = l_Lean_replaceRef(v_ref_5001_, v_ref_5010_);
lean_inc(v_currRecDepth_5009_);
lean_inc_ref(v_toCold_5008_);
v___x_5016_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5016_, 0, v_toCold_5008_);
lean_ctor_set(v___x_5016_, 1, v_currRecDepth_5009_);
lean_ctor_set(v___x_5016_, 2, v_ref_5015_);
lean_ctor_set_uint16(v___x_5016_, sizeof(void*)*3, v_optionFlags_5011_);
lean_ctor_set_uint8(v___x_5016_, sizeof(void*)*3 + 2, v_suppressElabErrors_5012_);
lean_ctor_set_uint8(v___x_5016_, sizeof(void*)*3 + 3, v_checkDeprecated_5013_);
lean_ctor_set_uint8(v___x_5016_, sizeof(void*)*3 + 4, v_isRecordingDeps_5014_);
v___x_5017_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5002_, v___y_5003_, v___y_5004_, v___x_5016_, v___y_5006_);
lean_dec_ref_known(v___x_5016_, 3);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5018_, lean_object* v_msg_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5018_, v_msg_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v_ref_5018_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5026_, lean_object* v_msg_5027_, lean_object* v_declHint_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v___x_5034_; lean_object* v_a_5035_; lean_object* v___x_5036_; 
v___x_5034_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5027_, v_declHint_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref(v___x_5034_);
v___x_5036_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5026_, v_a_5035_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5037_, lean_object* v_msg_5038_, lean_object* v_declHint_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5037_, v_msg_5038_, v_declHint_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec(v___y_5041_);
lean_dec_ref(v___y_5040_);
lean_dec(v_ref_5037_);
return v_res_5045_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5048_ = l_Lean_stringToMessageData(v___x_5047_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5049_, lean_object* v_constName_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v___x_5056_; uint8_t v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5056_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5057_ = 0;
lean_inc(v_constName_5050_);
v___x_5058_ = l_Lean_MessageData_ofConstName(v_constName_5050_, v___x_5057_);
v___x_5059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5056_);
lean_ctor_set(v___x_5059_, 1, v___x_5058_);
v___x_5060_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5061_, 0, v___x_5059_);
lean_ctor_set(v___x_5061_, 1, v___x_5060_);
v___x_5062_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5049_, v___x_5061_, v_constName_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
return v___x_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5063_, lean_object* v_constName_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5063_, v_constName_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
lean_dec(v___y_5068_);
lean_dec_ref(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5065_);
lean_dec(v_ref_5063_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v_ref_5077_; lean_object* v___x_5078_; 
v_ref_5077_ = lean_ctor_get(v___y_5074_, 2);
v___x_5078_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5077_, v_constName_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
return v___x_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_);
lean_dec(v___y_5083_);
lean_dec_ref(v___y_5082_);
lean_dec(v___y_5081_);
lean_dec_ref(v___y_5080_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
lean_object* v___x_5092_; lean_object* v_env_5093_; uint8_t v___x_5094_; lean_object* v___x_5095_; 
v___x_5092_ = lean_st_ref_get(v___y_5090_);
v_env_5093_ = lean_ctor_get(v___x_5092_, 0);
lean_inc_ref(v_env_5093_);
lean_dec(v___x_5092_);
v___x_5094_ = 0;
lean_inc(v_constName_5086_);
v___x_5095_ = l_Lean_Environment_find_x3f(v_env_5093_, v_constName_5086_, v___x_5094_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_object* v___x_5096_; 
v___x_5096_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_);
return v___x_5096_;
}
else
{
lean_object* v_val_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5104_; 
lean_dec(v_constName_5086_);
v_val_5097_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5099_ = v___x_5095_;
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_val_5097_);
lean_dec(v___x_5095_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
lean_ctor_set_tag(v___x_5099_, 0);
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_val_5097_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
lean_dec(v___y_5109_);
lean_dec_ref(v___y_5108_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5114_, lean_object* v_x_5115_, lean_object* v_x_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
if (lean_obj_tag(v_x_5114_) == 5)
{
lean_object* v_fn_5122_; lean_object* v_arg_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v_fn_5122_ = lean_ctor_get(v_x_5114_, 0);
lean_inc_ref(v_fn_5122_);
v_arg_5123_ = lean_ctor_get(v_x_5114_, 1);
lean_inc_ref(v_arg_5123_);
lean_dec_ref_known(v_x_5114_, 2);
v___x_5124_ = lean_array_set(v_x_5115_, v_x_5116_, v_arg_5123_);
v___x_5125_ = lean_unsigned_to_nat(1u);
v___x_5126_ = lean_nat_sub(v_x_5116_, v___x_5125_);
lean_dec(v_x_5116_);
v_x_5114_ = v_fn_5122_;
v_x_5115_ = v___x_5124_;
v_x_5116_ = v___x_5126_;
goto _start;
}
else
{
lean_dec(v_x_5116_);
if (lean_obj_tag(v_x_5114_) == 4)
{
lean_object* v_declName_5128_; lean_object* v___x_5129_; 
v_declName_5128_ = lean_ctor_get(v_x_5114_, 0);
lean_inc(v_declName_5128_);
lean_dec_ref_known(v_x_5114_, 2);
v___x_5129_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5128_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5161_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5132_ = v___x_5129_;
v_isShared_5133_ = v_isSharedCheck_5161_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5129_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5161_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v_lower_5135_; lean_object* v_upper_5136_; 
if (lean_obj_tag(v_a_5130_) == 5)
{
lean_object* v_val_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5158_; 
v_val_5144_ = lean_ctor_get(v_a_5130_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_a_5130_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5146_ = v_a_5130_;
v_isShared_5147_ = v_isSharedCheck_5158_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_val_5144_);
lean_dec(v_a_5130_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5158_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v_numParams_5148_; lean_object* v_numIndices_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; 
v_numParams_5148_ = lean_ctor_get(v_val_5144_, 1);
lean_inc(v_numParams_5148_);
v_numIndices_5149_ = lean_ctor_get(v_val_5144_, 2);
lean_inc(v_numIndices_5149_);
lean_dec_ref(v_val_5144_);
v___x_5150_ = lean_unsigned_to_nat(0u);
v___x_5151_ = lean_nat_dec_eq(v_numIndices_5149_, v___x_5150_);
lean_dec(v_numIndices_5149_);
if (v___x_5151_ == 0)
{
lean_object* v___x_5152_; uint8_t v___x_5153_; 
lean_del_object(v___x_5146_);
v___x_5152_ = lean_array_get_size(v_x_5115_);
v___x_5153_ = lean_nat_dec_le(v_numParams_5148_, v___x_5150_);
if (v___x_5153_ == 0)
{
v_lower_5135_ = v_numParams_5148_;
v_upper_5136_ = v___x_5152_;
goto v___jp_5134_;
}
else
{
lean_dec(v_numParams_5148_);
v_lower_5135_ = v___x_5150_;
v_upper_5136_ = v___x_5152_;
goto v___jp_5134_;
}
}
else
{
lean_object* v___x_5154_; lean_object* v___x_5156_; 
lean_dec(v_numParams_5148_);
lean_del_object(v___x_5132_);
lean_dec_ref(v_x_5115_);
v___x_5154_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5147_ == 0)
{
lean_ctor_set_tag(v___x_5146_, 0);
lean_ctor_set(v___x_5146_, 0, v___x_5154_);
v___x_5156_ = v___x_5146_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5154_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5160_; 
lean_del_object(v___x_5132_);
lean_dec(v_a_5130_);
lean_dec_ref(v_x_5115_);
v___x_5159_ = lean_box(0);
v___x_5160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5160_, 0, v___x_5159_);
return v___x_5160_;
}
v___jp_5134_:
{
lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5142_; 
v___x_5137_ = l_Array_toSubarray___redArg(v_x_5115_, v_lower_5135_, v_upper_5136_);
v___x_5138_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5139_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5137_, v___x_5138_);
v___x_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5140_, 0, v___x_5139_);
if (v_isShared_5133_ == 0)
{
lean_ctor_set(v___x_5132_, 0, v___x_5140_);
v___x_5142_ = v___x_5132_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v___x_5140_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
else
{
lean_object* v_a_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5169_; 
lean_dec_ref(v_x_5115_);
v_a_5162_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5164_ = v___x_5129_;
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_a_5162_);
lean_dec(v___x_5129_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5167_; 
if (v_isShared_5165_ == 0)
{
v___x_5167_ = v___x_5164_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
v___x_5167_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
return v___x_5167_;
}
}
}
}
else
{
lean_object* v___x_5170_; lean_object* v___x_5171_; 
lean_dec_ref(v_x_5115_);
lean_dec_ref(v_x_5114_);
v___x_5170_ = lean_box(0);
v___x_5171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5170_);
return v___x_5171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5172_, lean_object* v_x_5173_, lean_object* v_x_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5172_, v_x_5173_, v_x_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_);
lean_dec(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v___x_5187_; 
lean_inc(v_a_5185_);
lean_inc_ref(v_a_5184_);
lean_inc(v_a_5183_);
lean_inc_ref(v_a_5182_);
v___x_5187_ = lean_infer_type(v_ctorApp_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_a_5188_; lean_object* v___x_5189_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_a_5188_);
lean_dec_ref_known(v___x_5187_, 1);
v___x_5189_ = l_Lean_Meta_whnfD(v_a_5188_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_object* v_a_5190_; lean_object* v_dummy_5191_; lean_object* v_nargs_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_a_5190_);
lean_dec_ref_known(v___x_5189_, 1);
v_dummy_5191_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5192_ = l_Lean_Expr_getAppNumArgs(v_a_5190_);
lean_inc(v_nargs_5192_);
v___x_5193_ = lean_mk_array(v_nargs_5192_, v_dummy_5191_);
v___x_5194_ = lean_unsigned_to_nat(1u);
v___x_5195_ = lean_nat_sub(v_nargs_5192_, v___x_5194_);
lean_dec(v_nargs_5192_);
v___x_5196_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5190_, v___x_5193_, v___x_5195_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
return v___x_5196_;
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
v_a_5197_ = lean_ctor_get(v___x_5189_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5189_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5189_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
v_a_5205_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5187_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5187_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5208_ == 0)
{
v___x_5210_ = v___x_5207_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5220_, lean_object* v_R_5221_, lean_object* v_a_5222_, lean_object* v_b_5223_){
_start:
{
lean_object* v___x_5224_; 
v___x_5224_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5222_, v_b_5223_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5225_, lean_object* v_constName_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_){
_start:
{
lean_object* v___x_5232_; 
v___x_5232_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5233_, lean_object* v_constName_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5233_, v_constName_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5241_, lean_object* v_ref_5242_, lean_object* v_constName_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v___x_5249_; 
v___x_5249_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5242_, v_constName_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
return v___x_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5250_, lean_object* v_ref_5251_, lean_object* v_constName_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5250_, v_ref_5251_, v_constName_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v_ref_5251_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5259_, lean_object* v_ref_5260_, lean_object* v_msg_5261_, lean_object* v_declHint_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5260_, v_msg_5261_, v_declHint_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5269_, lean_object* v_ref_5270_, lean_object* v_msg_5271_, lean_object* v_declHint_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
lean_object* v_res_5278_; 
v_res_5278_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5269_, v_ref_5270_, v_msg_5271_, v_declHint_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v_ref_5270_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5279_, lean_object* v_declHint_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5279_, v_declHint_5280_, v___y_5284_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5287_, lean_object* v_declHint_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5287_, v_declHint_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5295_, lean_object* v_ref_5296_, lean_object* v_msg_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_){
_start:
{
lean_object* v___x_5303_; 
v___x_5303_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5296_, v_msg_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
return v___x_5303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5304_, lean_object* v_ref_5305_, lean_object* v_msg_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5304_, v_ref_5305_, v_msg_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_);
lean_dec(v___y_5310_);
lean_dec_ref(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v_ref_5305_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5313_, lean_object* v_body_5314_, lean_object* v_args2_5315_, lean_object* v_ctorVal_5316_, lean_object* v_args1_5317_, lean_object* v_k_5318_, lean_object* v_arg2_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5313_, v_body_5314_, v_args2_5315_, v_ctorVal_5316_, v_args1_5317_, v_k_5318_, v_arg2_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
lean_dec(v___y_5323_);
lean_dec_ref(v___y_5322_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
lean_dec_ref(v_body_5314_);
lean_dec(v_i_5313_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5326_, lean_object* v_args1_5327_, lean_object* v_k_5328_, lean_object* v_i_5329_, lean_object* v_type_5330_, lean_object* v_args2_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_){
_start:
{
lean_object* v___x_5337_; uint8_t v___x_5338_; 
v___x_5337_ = lean_array_get_size(v_args1_5327_);
v___x_5338_ = lean_nat_dec_lt(v_i_5329_, v___x_5337_);
if (v___x_5338_ == 0)
{
lean_object* v___x_5339_; 
lean_dec_ref(v_type_5330_);
lean_dec(v_i_5329_);
lean_dec_ref(v_args1_5327_);
lean_dec_ref(v_ctorVal_5326_);
lean_inc(v_a_5335_);
lean_inc_ref(v_a_5334_);
lean_inc(v_a_5333_);
lean_inc_ref(v_a_5332_);
v___x_5339_ = lean_apply_6(v_k_5328_, v_args2_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, lean_box(0));
return v___x_5339_;
}
else
{
lean_object* v___x_5340_; 
lean_inc(v_a_5335_);
lean_inc_ref(v_a_5334_);
lean_inc(v_a_5333_);
lean_inc_ref(v_a_5332_);
v___x_5340_ = lean_whnf(v_type_5330_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v_a_5341_; 
v_a_5341_ = lean_ctor_get(v___x_5340_, 0);
lean_inc(v_a_5341_);
lean_dec_ref_known(v___x_5340_, 1);
if (lean_obj_tag(v_a_5341_) == 7)
{
lean_object* v_binderName_5342_; lean_object* v_binderType_5343_; lean_object* v_body_5344_; lean_object* v___f_5345_; uint8_t v___x_5346_; uint8_t v___x_5347_; lean_object* v___x_5348_; 
v_binderName_5342_ = lean_ctor_get(v_a_5341_, 0);
lean_inc(v_binderName_5342_);
v_binderType_5343_ = lean_ctor_get(v_a_5341_, 1);
lean_inc_ref(v_binderType_5343_);
v_body_5344_ = lean_ctor_get(v_a_5341_, 2);
lean_inc_ref(v_body_5344_);
lean_dec_ref_known(v_a_5341_, 3);
v___f_5345_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5345_, 0, v_i_5329_);
lean_closure_set(v___f_5345_, 1, v_body_5344_);
lean_closure_set(v___f_5345_, 2, v_args2_5331_);
lean_closure_set(v___f_5345_, 3, v_ctorVal_5326_);
lean_closure_set(v___f_5345_, 4, v_args1_5327_);
lean_closure_set(v___f_5345_, 5, v_k_5328_);
v___x_5346_ = 1;
v___x_5347_ = 0;
v___x_5348_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5342_, v___x_5346_, v_binderType_5343_, v___f_5345_, v___x_5347_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
return v___x_5348_;
}
else
{
lean_object* v_toConstantVal_5349_; lean_object* v_name_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; 
lean_dec(v_a_5341_);
lean_dec_ref(v_args2_5331_);
lean_dec(v_i_5329_);
lean_dec_ref(v_k_5328_);
lean_dec_ref(v_args1_5327_);
v_toConstantVal_5349_ = lean_ctor_get(v_ctorVal_5326_, 0);
lean_inc_ref(v_toConstantVal_5349_);
lean_dec_ref(v_ctorVal_5326_);
v_name_5350_ = lean_ctor_get(v_toConstantVal_5349_, 0);
lean_inc(v_name_5350_);
lean_dec_ref(v_toConstantVal_5349_);
v___x_5351_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5352_ = l_Lean_MessageData_ofName(v_name_5350_);
v___x_5353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5351_);
lean_ctor_set(v___x_5353_, 1, v___x_5352_);
v___x_5354_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5353_);
lean_ctor_set(v___x_5355_, 1, v___x_5354_);
v___x_5356_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5355_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
return v___x_5356_;
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
lean_dec_ref(v_args2_5331_);
lean_dec(v_i_5329_);
lean_dec_ref(v_k_5328_);
lean_dec_ref(v_args1_5327_);
lean_dec_ref(v_ctorVal_5326_);
v_a_5357_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5359_ = v___x_5340_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___x_5340_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5365_, lean_object* v_body_5366_, lean_object* v_args2_5367_, lean_object* v_ctorVal_5368_, lean_object* v_args1_5369_, lean_object* v_k_5370_, lean_object* v_arg2_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; 
v___x_5377_ = lean_unsigned_to_nat(1u);
v___x_5378_ = lean_nat_add(v_i_5365_, v___x_5377_);
v___x_5379_ = lean_expr_instantiate1(v_body_5366_, v_arg2_5371_);
v___x_5380_ = lean_array_push(v_args2_5367_, v_arg2_5371_);
v___x_5381_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5368_, v_args1_5369_, v_k_5370_, v___x_5378_, v___x_5379_, v___x_5380_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5382_, lean_object* v_args1_5383_, lean_object* v_k_5384_, lean_object* v_i_5385_, lean_object* v_type_5386_, lean_object* v_args2_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5382_, v_args1_5383_, v_k_5384_, v_i_5385_, v_type_5386_, v_args2_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_);
lean_dec(v_a_5391_);
lean_dec_ref(v_a_5390_);
lean_dec(v_a_5389_);
lean_dec_ref(v_a_5388_);
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v___x_5394_, lean_object* v_numParams_5395_, lean_object* v_name_5396_, lean_object* v_us_5397_, lean_object* v_args1_5398_, lean_object* v___x_5399_, lean_object* v_args2_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
lean_inc_ref(v_args2_5400_);
v___x_5406_ = l_Array_toSubarray___redArg(v_args2_5400_, v___x_5394_, v_numParams_5395_);
lean_inc(v_us_5397_);
v___x_5407_ = l_Lean_mkConst(v_name_5396_, v_us_5397_);
lean_inc_ref(v___x_5407_);
v___x_5408_ = l_Lean_mkAppN(v___x_5407_, v_args1_5398_);
v___x_5409_ = l_Lean_mkAppN(v___x_5407_, v_args2_5400_);
lean_inc_ref(v___x_5409_);
lean_inc_ref(v___x_5408_);
v___x_5410_ = l_Lean_Meta_mkEqHEq(v___x_5408_, v___x_5409_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
if (lean_obj_tag(v___x_5410_) == 0)
{
lean_object* v_a_5411_; uint8_t v___x_5412_; lean_object* v___x_5413_; 
v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
lean_inc(v_a_5411_);
lean_dec_ref_known(v___x_5410_, 1);
v___x_5412_ = 1;
lean_inc_ref(v_args2_5400_);
v___x_5413_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5398_, v_args2_5400_, v___x_5412_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v_a_5414_; lean_object* v___x_5416_; uint8_t v_isShared_5417_; uint8_t v_isSharedCheck_5534_; 
v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5534_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5416_ = v___x_5413_;
v_isShared_5417_ = v_isSharedCheck_5534_;
goto v_resetjp_5415_;
}
else
{
lean_inc(v_a_5414_);
lean_dec(v___x_5413_);
v___x_5416_ = lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5534_;
goto v_resetjp_5415_;
}
v_resetjp_5415_:
{
lean_object* v___x_5418_; 
v___x_5418_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5414_);
if (lean_obj_tag(v___x_5418_) == 1)
{
lean_object* v_val_5419_; lean_object* v___x_5420_; 
lean_del_object(v___x_5416_);
v_val_5419_ = lean_ctor_get(v___x_5418_, 0);
lean_inc(v_val_5419_);
lean_dec_ref_known(v___x_5418_, 1);
v___x_5420_ = l_Lean_mkArrow(v_a_5411_, v_val_5419_, v___y_5403_, v___y_5404_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v_a_5421_; lean_object* v___x_5422_; 
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_a_5421_);
lean_dec_ref_known(v___x_5420_, 1);
v___x_5422_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5408_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5513_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5425_ = v___x_5422_;
v_isShared_5426_ = v_isSharedCheck_5513_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_a_5423_);
lean_dec(v___x_5422_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5513_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
if (lean_obj_tag(v_a_5423_) == 1)
{
lean_object* v_val_5427_; lean_object* v___x_5428_; 
lean_del_object(v___x_5425_);
v_val_5427_ = lean_ctor_get(v_a_5423_, 0);
lean_inc(v_val_5427_);
lean_dec_ref_known(v_a_5423_, 1);
v___x_5428_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5409_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5500_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5500_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5431_ = v___x_5428_;
v_isShared_5432_ = v_isSharedCheck_5500_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5428_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5500_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
if (lean_obj_tag(v_a_5429_) == 1)
{
lean_object* v_val_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5495_; 
lean_del_object(v___x_5431_);
v_val_5433_ = lean_ctor_get(v_a_5429_, 0);
v_isSharedCheck_5495_ = !lean_is_exclusive(v_a_5429_);
if (v_isSharedCheck_5495_ == 0)
{
v___x_5435_ = v_a_5429_;
v_isShared_5436_ = v_isSharedCheck_5495_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_val_5433_);
lean_dec(v_a_5429_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5495_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; uint8_t v___x_5441_; lean_object* v___x_5442_; 
v___x_5437_ = l_Subarray_copy___redArg(v___x_5399_);
v___x_5438_ = l_Array_append___redArg(v___x_5437_, v_val_5427_);
v___x_5439_ = l_Subarray_copy___redArg(v___x_5406_);
v___x_5440_ = l_Array_append___redArg(v___x_5439_, v_val_5433_);
lean_dec(v_val_5433_);
v___x_5441_ = 0;
v___x_5442_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5438_, v___x_5440_, v___x_5441_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
lean_dec_ref(v___x_5438_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v___x_5444_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_a_5443_);
lean_dec_ref_known(v___x_5442_, 1);
v___x_5444_ = l_Lean_mkArrowN(v_a_5443_, v_a_5421_, v___y_5403_, v___y_5404_);
lean_dec(v_a_5443_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; uint8_t v___x_5446_; lean_object* v___x_5447_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
lean_inc(v_a_5445_);
lean_dec_ref_known(v___x_5444_, 1);
v___x_5446_ = 1;
v___x_5447_ = l_Lean_Meta_mkForallFVars(v_args2_5400_, v_a_5445_, v___x_5441_, v___x_5412_, v___x_5412_, v___x_5446_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
lean_dec_ref(v_args2_5400_);
if (lean_obj_tag(v___x_5447_) == 0)
{
lean_object* v_a_5448_; lean_object* v___x_5449_; 
v_a_5448_ = lean_ctor_get(v___x_5447_, 0);
lean_inc(v_a_5448_);
lean_dec_ref_known(v___x_5447_, 1);
v___x_5449_ = l_Lean_Meta_mkForallFVars(v_args1_5398_, v_a_5448_, v___x_5441_, v___x_5412_, v___x_5412_, v___x_5446_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5462_; 
v_a_5450_ = lean_ctor_get(v___x_5449_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5449_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5452_ = v___x_5449_;
v_isShared_5453_ = v_isSharedCheck_5462_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5449_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5462_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5457_; 
v___x_5454_ = lean_array_get_size(v_val_5427_);
lean_dec(v_val_5427_);
v___x_5455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5455_, 0, v_a_5450_);
lean_ctor_set(v___x_5455_, 1, v_us_5397_);
lean_ctor_set(v___x_5455_, 2, v___x_5454_);
if (v_isShared_5436_ == 0)
{
lean_ctor_set(v___x_5435_, 0, v___x_5455_);
v___x_5457_ = v___x_5435_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5455_);
v___x_5457_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
lean_object* v___x_5459_; 
if (v_isShared_5453_ == 0)
{
lean_ctor_set(v___x_5452_, 0, v___x_5457_);
v___x_5459_ = v___x_5452_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v___x_5457_);
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
else
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
lean_del_object(v___x_5435_);
lean_dec(v_val_5427_);
lean_dec(v_us_5397_);
v_a_5463_ = lean_ctor_get(v___x_5449_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5449_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5449_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5449_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
else
{
lean_object* v_a_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5478_; 
lean_del_object(v___x_5435_);
lean_dec(v_val_5427_);
lean_dec(v_us_5397_);
v_a_5471_ = lean_ctor_get(v___x_5447_, 0);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5447_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5473_ = v___x_5447_;
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_a_5471_);
lean_dec(v___x_5447_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5478_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v___x_5476_; 
if (v_isShared_5474_ == 0)
{
v___x_5476_ = v___x_5473_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_a_5471_);
v___x_5476_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
return v___x_5476_;
}
}
}
}
else
{
lean_object* v_a_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5486_; 
lean_del_object(v___x_5435_);
lean_dec(v_val_5427_);
lean_dec_ref(v_args2_5400_);
lean_dec(v_us_5397_);
v_a_5479_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5486_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5486_ == 0)
{
v___x_5481_ = v___x_5444_;
v_isShared_5482_ = v_isSharedCheck_5486_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_a_5479_);
lean_dec(v___x_5444_);
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
lean_del_object(v___x_5435_);
lean_dec(v_val_5427_);
lean_dec(v_a_5421_);
lean_dec_ref(v_args2_5400_);
lean_dec(v_us_5397_);
v_a_5487_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5442_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5442_);
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
}
else
{
lean_object* v___x_5496_; lean_object* v___x_5498_; 
lean_dec(v_a_5429_);
lean_dec(v_val_5427_);
lean_dec(v_a_5421_);
lean_dec_ref(v___x_5406_);
lean_dec_ref(v_args2_5400_);
lean_dec_ref(v___x_5399_);
lean_dec(v_us_5397_);
v___x_5496_ = lean_box(0);
if (v_isShared_5432_ == 0)
{
lean_ctor_set(v___x_5431_, 0, v___x_5496_);
v___x_5498_ = v___x_5431_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v___x_5496_);
v___x_5498_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
return v___x_5498_;
}
}
}
}
else
{
lean_object* v_a_5501_; lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5508_; 
lean_dec(v_val_5427_);
lean_dec(v_a_5421_);
lean_dec_ref(v___x_5406_);
lean_dec_ref(v_args2_5400_);
lean_dec_ref(v___x_5399_);
lean_dec(v_us_5397_);
v_a_5501_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5508_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5508_ == 0)
{
v___x_5503_ = v___x_5428_;
v_isShared_5504_ = v_isSharedCheck_5508_;
goto v_resetjp_5502_;
}
else
{
lean_inc(v_a_5501_);
lean_dec(v___x_5428_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5508_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
lean_object* v___x_5506_; 
if (v_isShared_5504_ == 0)
{
v___x_5506_ = v___x_5503_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5507_; 
v_reuseFailAlloc_5507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5501_);
v___x_5506_ = v_reuseFailAlloc_5507_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
return v___x_5506_;
}
}
}
}
else
{
lean_object* v___x_5509_; lean_object* v___x_5511_; 
lean_dec(v_a_5423_);
lean_dec(v_a_5421_);
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5406_);
lean_dec_ref(v_args2_5400_);
lean_dec_ref(v___x_5399_);
lean_dec(v_us_5397_);
v___x_5509_ = lean_box(0);
if (v_isShared_5426_ == 0)
{
lean_ctor_set(v___x_5425_, 0, v___x_5509_);
v___x_5511_ = v___x_5425_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v___x_5509_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
}
}
else
{
lean_object* v_a_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5521_; 
lean_dec(v_a_5421_);
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5406_);
lean_dec_ref(v_args2_5400_);
lean_dec_ref(v___x_5399_);
lean_dec(v_us_5397_);
v_a_5514_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5516_ = v___x_5422_;
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_a_5514_);
lean_dec(v___x_5422_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v___x_5519_; 
if (v_isShared_5517_ == 0)
{
v___x_5519_ = v___x_5516_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_a_5514_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
}
else
{
lean_object* v_a_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5529_; 
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v___x_5406_);
lean_dec_ref(v_args2_5400_);
lean_dec_ref(v___x_5399_);
lean_dec(v_us_5397_);
v_a_5522_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5524_ = v___x_5420_;
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_a_5522_);
lean_dec(v___x_5420_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5527_; 
if (v_isShared_5525_ == 0)
{
v___x_5527_ = v___x_5524_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_a_5522_);
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
lean_object* v___x_5530_; lean_object* v___x_5532_; 
lean_dec(v___x_5418_);
lean_dec(v_a_5411_);
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v___x_5406_);
lean_dec_ref(v_args2_5400_);
lean_dec_ref(v___x_5399_);
lean_dec(v_us_5397_);
v___x_5530_ = lean_box(0);
if (v_isShared_5417_ == 0)
{
lean_ctor_set(v___x_5416_, 0, v___x_5530_);
v___x_5532_ = v___x_5416_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5530_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
return v___x_5532_;
}
}
}
}
else
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5542_; 
lean_dec(v_a_5411_);
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v___x_5406_);
lean_dec_ref(v_args2_5400_);
lean_dec_ref(v___x_5399_);
lean_dec(v_us_5397_);
v_a_5535_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5537_ = v___x_5413_;
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5413_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5540_; 
if (v_isShared_5538_ == 0)
{
v___x_5540_ = v___x_5537_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_a_5535_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
}
}
else
{
lean_object* v_a_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5550_; 
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v___x_5406_);
lean_dec_ref(v_args2_5400_);
lean_dec_ref(v___x_5399_);
lean_dec(v_us_5397_);
v_a_5543_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5545_ = v___x_5410_;
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_a_5543_);
lean_dec(v___x_5410_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5548_; 
if (v_isShared_5546_ == 0)
{
v___x_5548_ = v___x_5545_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_a_5543_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v___x_5551_, lean_object* v_numParams_5552_, lean_object* v_name_5553_, lean_object* v_us_5554_, lean_object* v_args1_5555_, lean_object* v___x_5556_, lean_object* v_args2_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_){
_start:
{
lean_object* v_res_5563_; 
v_res_5563_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v___x_5551_, v_numParams_5552_, v_name_5553_, v_us_5554_, v_args1_5555_, v___x_5556_, v_args2_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5559_);
lean_dec_ref(v___y_5558_);
lean_dec_ref(v_args1_5555_);
return v_res_5563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5564_, lean_object* v_name_5565_, lean_object* v_us_5566_, lean_object* v_ctorVal_5567_, lean_object* v_a_5568_, lean_object* v_args1_5569_, lean_object* v_x_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_){
_start:
{
lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___f_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; 
v___x_5576_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5564_);
lean_inc_ref_n(v_args1_5569_, 3);
v___x_5577_ = l_Array_toSubarray___redArg(v_args1_5569_, v___x_5576_, v_numParams_5564_);
v___f_5578_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5578_, 0, v___x_5576_);
lean_closure_set(v___f_5578_, 1, v_numParams_5564_);
lean_closure_set(v___f_5578_, 2, v_name_5565_);
lean_closure_set(v___f_5578_, 3, v_us_5566_);
lean_closure_set(v___f_5578_, 4, v_args1_5569_);
lean_closure_set(v___f_5578_, 5, v___x_5577_);
v___x_5579_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5580_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5580_, 0, v_ctorVal_5567_);
lean_closure_set(v___x_5580_, 1, v_args1_5569_);
lean_closure_set(v___x_5580_, 2, v___f_5578_);
lean_closure_set(v___x_5580_, 3, v___x_5576_);
lean_closure_set(v___x_5580_, 4, v_a_5568_);
lean_closure_set(v___x_5580_, 5, v___x_5579_);
v___x_5581_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5569_, v___x_5580_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_);
return v___x_5581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5582_, lean_object* v_name_5583_, lean_object* v_us_5584_, lean_object* v_ctorVal_5585_, lean_object* v_a_5586_, lean_object* v_args1_5587_, lean_object* v_x_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_){
_start:
{
lean_object* v_res_5594_; 
v_res_5594_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5582_, v_name_5583_, v_us_5584_, v_ctorVal_5585_, v_a_5586_, v_args1_5587_, v_x_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_);
lean_dec(v___y_5592_);
lean_dec_ref(v___y_5591_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec_ref(v_x_5588_);
return v_res_5594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_){
_start:
{
lean_object* v_toConstantVal_5601_; lean_object* v_numParams_5602_; lean_object* v_name_5603_; lean_object* v_levelParams_5604_; lean_object* v_type_5605_; lean_object* v___x_5606_; lean_object* v_us_5607_; lean_object* v___x_5608_; 
v_toConstantVal_5601_ = lean_ctor_get(v_ctorVal_5595_, 0);
v_numParams_5602_ = lean_ctor_get(v_ctorVal_5595_, 3);
lean_inc(v_numParams_5602_);
v_name_5603_ = lean_ctor_get(v_toConstantVal_5601_, 0);
lean_inc(v_name_5603_);
v_levelParams_5604_ = lean_ctor_get(v_toConstantVal_5601_, 1);
v_type_5605_ = lean_ctor_get(v_toConstantVal_5601_, 2);
v___x_5606_ = lean_box(0);
lean_inc(v_levelParams_5604_);
v_us_5607_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5604_, v___x_5606_);
lean_inc_ref(v_type_5605_);
v___x_5608_ = l_Lean_Meta_elimOptParam(v_type_5605_, v_a_5598_, v_a_5599_);
if (lean_obj_tag(v___x_5608_) == 0)
{
lean_object* v_a_5609_; lean_object* v___f_5610_; uint8_t v___x_5611_; lean_object* v___x_5612_; 
v_a_5609_ = lean_ctor_get(v___x_5608_, 0);
lean_inc_n(v_a_5609_, 2);
lean_dec_ref_known(v___x_5608_, 1);
v___f_5610_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5610_, 0, v_numParams_5602_);
lean_closure_set(v___f_5610_, 1, v_name_5603_);
lean_closure_set(v___f_5610_, 2, v_us_5607_);
lean_closure_set(v___f_5610_, 3, v_ctorVal_5595_);
lean_closure_set(v___f_5610_, 4, v_a_5609_);
v___x_5611_ = 0;
v___x_5612_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5609_, v___f_5610_, v___x_5611_, v_a_5596_, v_a_5597_, v_a_5598_, v_a_5599_);
return v___x_5612_;
}
else
{
lean_object* v_a_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5620_; 
lean_dec(v_us_5607_);
lean_dec(v_name_5603_);
lean_dec(v_numParams_5602_);
lean_dec_ref(v_ctorVal_5595_);
v_a_5613_ = lean_ctor_get(v___x_5608_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5608_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5615_ = v___x_5608_;
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_a_5613_);
lean_dec(v___x_5608_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5618_; 
if (v_isShared_5616_ == 0)
{
v___x_5618_ = v___x_5615_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5613_);
v___x_5618_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
return v___x_5618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_){
_start:
{
lean_object* v_res_5627_; 
v_res_5627_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
lean_dec(v_a_5625_);
lean_dec_ref(v_a_5624_);
lean_dec(v_a_5623_);
lean_dec_ref(v_a_5622_);
return v_res_5627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5629_; lean_object* v___x_5630_; 
v___x_5629_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5630_ = l_Lean_stringToMessageData(v___x_5629_);
return v___x_5630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_){
_start:
{
lean_object* v_toConstantVal_5637_; lean_object* v_name_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; 
v_toConstantVal_5637_ = lean_ctor_get(v_ctorVal_5631_, 0);
lean_inc_ref(v_toConstantVal_5637_);
lean_dec_ref(v_ctorVal_5631_);
v_name_5638_ = lean_ctor_get(v_toConstantVal_5637_, 0);
lean_inc(v_name_5638_);
lean_dec_ref(v_toConstantVal_5637_);
v___x_5639_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5640_ = l_Lean_MessageData_ofName(v_name_5638_);
v___x_5641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5639_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5641_);
lean_ctor_set(v___x_5643_, 1, v___x_5642_);
v___x_5644_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5643_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_);
return v___x_5644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_){
_start:
{
lean_object* v_res_5651_; 
v_res_5651_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_);
lean_dec(v_a_5649_);
lean_dec_ref(v_a_5648_);
lean_dec(v_a_5647_);
lean_dec_ref(v_a_5646_);
return v_res_5651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5652_, lean_object* v_ctorVal_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_){
_start:
{
lean_object* v___x_5659_; 
v___x_5659_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5653_, v_a_5654_, v_a_5655_, v_a_5656_, v_a_5657_);
return v___x_5659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5660_, lean_object* v_ctorVal_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_){
_start:
{
lean_object* v_res_5667_; 
v_res_5667_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5660_, v_ctorVal_5661_, v_a_5662_, v_a_5663_, v_a_5664_, v_a_5665_);
lean_dec(v_a_5665_);
lean_dec_ref(v_a_5664_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5673_, size_t v_sz_5674_, size_t v_i_5675_, lean_object* v_bs_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_){
_start:
{
uint8_t v___x_5682_; 
v___x_5682_ = lean_usize_dec_lt(v_i_5675_, v_sz_5674_);
if (v___x_5682_ == 0)
{
lean_object* v___x_5683_; 
lean_dec_ref(v_ctorVal_5673_);
v___x_5683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5683_, 0, v_bs_5676_);
return v___x_5683_;
}
else
{
lean_object* v_v_5684_; lean_object* v___x_5685_; lean_object* v_bs_x27_5686_; lean_object* v_a_5688_; lean_object* v___y_5694_; lean_object* v_lhs_5705_; lean_object* v_rhs_5706_; lean_object* v___x_5708_; 
v_v_5684_ = lean_array_uget(v_bs_5676_, v_i_5675_);
v___x_5685_ = lean_unsigned_to_nat(0u);
v_bs_x27_5686_ = lean_array_uset(v_bs_5676_, v_i_5675_, v___x_5685_);
lean_inc(v___y_5680_);
lean_inc_ref(v___y_5679_);
lean_inc(v___y_5678_);
lean_inc_ref(v___y_5677_);
v___x_5708_ = lean_infer_type(v_v_5684_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
if (lean_obj_tag(v___x_5708_) == 0)
{
lean_object* v_a_5709_; lean_object* v___x_5710_; 
v_a_5709_ = lean_ctor_get(v___x_5708_, 0);
lean_inc(v_a_5709_);
lean_dec_ref_known(v___x_5708_, 1);
v___x_5710_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5709_, v___y_5678_);
if (lean_obj_tag(v___x_5710_) == 0)
{
lean_object* v_a_5711_; lean_object* v___x_5712_; uint8_t v___x_5713_; 
v_a_5711_ = lean_ctor_get(v___x_5710_, 0);
lean_inc(v_a_5711_);
lean_dec_ref_known(v___x_5710_, 1);
v___x_5712_ = l_Lean_Expr_cleanupAnnotations(v_a_5711_);
lean_dec(v_a_5711_);
v___x_5713_ = l_Lean_Expr_isApp(v___x_5712_);
if (v___x_5713_ == 0)
{
lean_object* v___x_5714_; 
lean_dec_ref(v___x_5712_);
lean_inc_ref(v_ctorVal_5673_);
v___x_5714_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5673_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
v___y_5694_ = v___x_5714_;
goto v___jp_5693_;
}
else
{
lean_object* v___x_5715_; uint8_t v___x_5716_; 
v___x_5715_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5712_);
v___x_5716_ = l_Lean_Expr_isApp(v___x_5715_);
if (v___x_5716_ == 0)
{
lean_object* v___x_5717_; 
lean_dec_ref(v___x_5715_);
lean_dec_ref(v___x_5712_);
lean_inc_ref(v_ctorVal_5673_);
v___x_5717_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5673_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
v___y_5694_ = v___x_5717_;
goto v___jp_5693_;
}
else
{
lean_object* v___x_5718_; uint8_t v___x_5719_; 
v___x_5718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5715_);
v___x_5719_ = l_Lean_Expr_isApp(v___x_5718_);
if (v___x_5719_ == 0)
{
lean_object* v___x_5720_; 
lean_dec_ref(v___x_5718_);
lean_dec_ref(v___x_5715_);
lean_dec_ref(v___x_5712_);
lean_inc_ref(v_ctorVal_5673_);
v___x_5720_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5673_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
v___y_5694_ = v___x_5720_;
goto v___jp_5693_;
}
else
{
lean_object* v_arg_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; uint8_t v___x_5724_; 
v_arg_5721_ = lean_ctor_get(v___x_5712_, 1);
lean_inc_ref(v_arg_5721_);
lean_dec_ref(v___x_5712_);
v___x_5722_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5718_);
v___x_5723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5724_ = l_Lean_Expr_isConstOf(v___x_5722_, v___x_5723_);
if (v___x_5724_ == 0)
{
uint8_t v___x_5725_; 
lean_dec_ref(v___x_5715_);
v___x_5725_ = l_Lean_Expr_isApp(v___x_5722_);
if (v___x_5725_ == 0)
{
lean_object* v___x_5726_; 
lean_dec_ref(v___x_5722_);
lean_dec_ref(v_arg_5721_);
lean_dec_ref(v___x_5718_);
lean_inc_ref(v_ctorVal_5673_);
v___x_5726_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5673_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
v___y_5694_ = v___x_5726_;
goto v___jp_5693_;
}
else
{
lean_object* v___x_5727_; lean_object* v___x_5728_; uint8_t v___x_5729_; 
v___x_5727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5722_);
lean_dec_ref(v___x_5722_);
v___x_5728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5729_ = l_Lean_Expr_isConstOf(v___x_5727_, v___x_5728_);
lean_dec_ref(v___x_5727_);
if (v___x_5729_ == 0)
{
lean_object* v___x_5730_; 
lean_dec_ref(v_arg_5721_);
lean_dec_ref(v___x_5718_);
lean_inc_ref(v_ctorVal_5673_);
v___x_5730_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5673_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
v___y_5694_ = v___x_5730_;
goto v___jp_5693_;
}
else
{
lean_object* v_arg_5731_; 
v_arg_5731_ = lean_ctor_get(v___x_5718_, 1);
lean_inc_ref(v_arg_5731_);
lean_dec_ref(v___x_5718_);
v_lhs_5705_ = v_arg_5731_;
v_rhs_5706_ = v_arg_5721_;
goto v___jp_5704_;
}
}
}
else
{
lean_object* v_arg_5732_; 
lean_dec_ref(v___x_5722_);
lean_dec_ref(v___x_5718_);
v_arg_5732_ = lean_ctor_get(v___x_5715_, 1);
lean_inc_ref(v_arg_5732_);
lean_dec_ref(v___x_5715_);
v_lhs_5705_ = v_arg_5732_;
v_rhs_5706_ = v_arg_5721_;
goto v___jp_5704_;
}
}
}
}
}
else
{
lean_object* v_a_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5740_; 
lean_dec_ref(v_bs_x27_5686_);
lean_dec_ref(v_ctorVal_5673_);
v_a_5733_ = lean_ctor_get(v___x_5710_, 0);
v_isSharedCheck_5740_ = !lean_is_exclusive(v___x_5710_);
if (v_isSharedCheck_5740_ == 0)
{
v___x_5735_ = v___x_5710_;
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_a_5733_);
lean_dec(v___x_5710_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5738_; 
if (v_isShared_5736_ == 0)
{
v___x_5738_ = v___x_5735_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_a_5733_);
v___x_5738_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
return v___x_5738_;
}
}
}
}
else
{
lean_object* v_a_5741_; lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5748_; 
lean_dec_ref(v_bs_x27_5686_);
lean_dec_ref(v_ctorVal_5673_);
v_a_5741_ = lean_ctor_get(v___x_5708_, 0);
v_isSharedCheck_5748_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5748_ == 0)
{
v___x_5743_ = v___x_5708_;
v_isShared_5744_ = v_isSharedCheck_5748_;
goto v_resetjp_5742_;
}
else
{
lean_inc(v_a_5741_);
lean_dec(v___x_5708_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5748_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v___x_5746_; 
if (v_isShared_5744_ == 0)
{
v___x_5746_ = v___x_5743_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v_a_5741_);
v___x_5746_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
return v___x_5746_;
}
}
}
v___jp_5687_:
{
size_t v___x_5689_; size_t v___x_5690_; lean_object* v___x_5691_; 
v___x_5689_ = ((size_t)1ULL);
v___x_5690_ = lean_usize_add(v_i_5675_, v___x_5689_);
v___x_5691_ = lean_array_uset(v_bs_x27_5686_, v_i_5675_, v_a_5688_);
v_i_5675_ = v___x_5690_;
v_bs_5676_ = v___x_5691_;
goto _start;
}
v___jp_5693_:
{
if (lean_obj_tag(v___y_5694_) == 0)
{
lean_object* v_a_5695_; 
v_a_5695_ = lean_ctor_get(v___y_5694_, 0);
lean_inc(v_a_5695_);
lean_dec_ref_known(v___y_5694_, 1);
v_a_5688_ = v_a_5695_;
goto v___jp_5687_;
}
else
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5703_; 
lean_dec_ref(v_bs_x27_5686_);
lean_dec_ref(v_ctorVal_5673_);
v_a_5696_ = lean_ctor_get(v___y_5694_, 0);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___y_5694_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5698_ = v___y_5694_;
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___y_5694_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5699_ == 0)
{
v___x_5701_ = v___x_5698_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
v___jp_5704_:
{
lean_object* v___x_5707_; 
v___x_5707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5707_, 0, v_lhs_5705_);
lean_ctor_set(v___x_5707_, 1, v_rhs_5706_);
v_a_5688_ = v___x_5707_;
goto v___jp_5687_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5749_, lean_object* v_sz_5750_, lean_object* v_i_5751_, lean_object* v_bs_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_){
_start:
{
size_t v_sz_boxed_5758_; size_t v_i_boxed_5759_; lean_object* v_res_5760_; 
v_sz_boxed_5758_ = lean_unbox_usize(v_sz_5750_);
lean_dec(v_sz_5750_);
v_i_boxed_5759_ = lean_unbox_usize(v_i_5751_);
lean_dec(v_i_5751_);
v_res_5760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5749_, v_sz_boxed_5758_, v_i_boxed_5759_, v_bs_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec(v___y_5754_);
lean_dec_ref(v___y_5753_);
return v_res_5760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5762_; lean_object* v___x_5763_; 
v___x_5762_ = lean_unsigned_to_nat(0u);
v___x_5763_ = l_Lean_Level_ofNat(v___x_5762_);
return v___x_5763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5764_, lean_object* v_us_5765_, lean_object* v_numIndices_5766_, lean_object* v_xs_5767_, lean_object* v_type_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_){
_start:
{
lean_object* v_toConstantVal_5774_; lean_object* v_induct_5775_; lean_object* v_numParams_5776_; lean_object* v___x_5777_; lean_object* v_noConfusionName_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v_noConfusion_5782_; lean_object* v_noConfusion_5783_; lean_object* v_lower_5785_; lean_object* v_upper_5786_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v_n_5897_; uint8_t v___x_5898_; 
v_toConstantVal_5774_ = lean_ctor_get(v_ctorVal_5764_, 0);
v_induct_5775_ = lean_ctor_get(v_ctorVal_5764_, 1);
v_numParams_5776_ = lean_ctor_get(v_ctorVal_5764_, 3);
v___x_5777_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5775_);
v_noConfusionName_5778_ = l_Lean_Name_str___override(v_induct_5775_, v___x_5777_);
v___x_5779_ = lean_unsigned_to_nat(0u);
v___x_5780_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5781_, 0, v___x_5780_);
lean_ctor_set(v___x_5781_, 1, v_us_5765_);
v_noConfusion_5782_ = l_Lean_mkConst(v_noConfusionName_5778_, v___x_5781_);
v_noConfusion_5783_ = l_Lean_Expr_app___override(v_noConfusion_5782_, v_type_5768_);
v___x_5893_ = lean_array_get_size(v_xs_5767_);
v___x_5894_ = lean_nat_sub(v___x_5893_, v_numParams_5776_);
v___x_5895_ = lean_nat_sub(v___x_5894_, v_numIndices_5766_);
lean_dec(v___x_5894_);
v___x_5896_ = lean_unsigned_to_nat(1u);
v_n_5897_ = lean_nat_sub(v___x_5895_, v___x_5896_);
lean_dec(v___x_5895_);
v___x_5898_ = lean_nat_dec_le(v_n_5897_, v___x_5779_);
if (v___x_5898_ == 0)
{
v_lower_5785_ = v_n_5897_;
v_upper_5786_ = v___x_5893_;
goto v___jp_5784_;
}
else
{
lean_dec(v_n_5897_);
v_lower_5785_ = v___x_5779_;
v_upper_5786_ = v___x_5893_;
goto v___jp_5784_;
}
v___jp_5784_:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v_eqs_5789_; size_t v_sz_5790_; size_t v___x_5791_; lean_object* v___x_5792_; 
lean_inc_ref(v_xs_5767_);
v___x_5787_ = l_Array_toSubarray___redArg(v_xs_5767_, v_lower_5785_, v_upper_5786_);
v___x_5788_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5789_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5787_, v___x_5788_);
v_sz_5790_ = lean_array_size(v_eqs_5789_);
v___x_5791_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5789_);
lean_inc_ref(v_ctorVal_5764_);
v___x_5792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5764_, v_sz_5790_, v___x_5791_, v_eqs_5789_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
if (lean_obj_tag(v___x_5792_) == 0)
{
lean_object* v_a_5793_; lean_object* v___x_5794_; lean_object* v_fst_5795_; lean_object* v_snd_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; 
v_a_5793_ = lean_ctor_get(v___x_5792_, 0);
lean_inc(v_a_5793_);
lean_dec_ref_known(v___x_5792_, 1);
v___x_5794_ = l_Array_unzip___redArg(v_a_5793_);
lean_dec(v_a_5793_);
v_fst_5795_ = lean_ctor_get(v___x_5794_, 0);
lean_inc(v_fst_5795_);
v_snd_5796_ = lean_ctor_get(v___x_5794_, 1);
lean_inc(v_snd_5796_);
lean_dec_ref(v___x_5794_);
v___x_5797_ = l_Lean_mkAppN(v_noConfusion_5783_, v_fst_5795_);
lean_dec(v_fst_5795_);
v___x_5798_ = l_Lean_mkAppN(v___x_5797_, v_snd_5796_);
lean_dec(v_snd_5796_);
v___x_5799_ = l_Lean_mkAppN(v___x_5798_, v_eqs_5789_);
lean_dec_ref(v_eqs_5789_);
lean_inc(v___y_5772_);
lean_inc_ref(v___y_5771_);
lean_inc(v___y_5770_);
lean_inc_ref(v___y_5769_);
lean_inc_ref(v___x_5799_);
v___x_5800_ = lean_infer_type(v___x_5799_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
if (lean_obj_tag(v___x_5800_) == 0)
{
lean_object* v_a_5801_; lean_object* v___x_5802_; 
v_a_5801_ = lean_ctor_get(v___x_5800_, 0);
lean_inc(v_a_5801_);
lean_dec_ref_known(v___x_5800_, 1);
lean_inc(v___y_5772_);
lean_inc_ref(v___y_5771_);
lean_inc(v___y_5770_);
lean_inc_ref(v___y_5769_);
v___x_5802_ = lean_whnf(v_a_5801_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
if (lean_obj_tag(v___x_5802_) == 0)
{
lean_object* v_a_5803_; 
v_a_5803_ = lean_ctor_get(v___x_5802_, 0);
lean_inc(v_a_5803_);
lean_dec_ref_known(v___x_5802_, 1);
if (lean_obj_tag(v_a_5803_) == 7)
{
lean_object* v_binderType_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; 
lean_inc_ref(v_toConstantVal_5774_);
lean_dec_ref(v_ctorVal_5764_);
v_binderType_5804_ = lean_ctor_get(v_a_5803_, 1);
lean_inc_ref(v_binderType_5804_);
lean_dec_ref_known(v_a_5803_, 3);
v___x_5805_ = lean_box(0);
v___x_5806_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5804_, v___x_5805_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
if (lean_obj_tag(v___x_5806_) == 0)
{
lean_object* v_a_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; 
v_a_5807_ = lean_ctor_get(v___x_5806_, 0);
lean_inc_n(v_a_5807_, 2);
lean_dec_ref_known(v___x_5806_, 1);
v___x_5808_ = l_Lean_Expr_app___override(v___x_5799_, v_a_5807_);
v___x_5809_ = l_Lean_Expr_mvarId_x21(v_a_5807_);
lean_dec(v_a_5807_);
v___x_5810_ = l_Lean_MVarId_intros(v___x_5809_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v_a_5811_; lean_object* v_snd_5812_; lean_object* v_name_5813_; lean_object* v___x_5814_; 
v_a_5811_ = lean_ctor_get(v___x_5810_, 0);
lean_inc(v_a_5811_);
lean_dec_ref_known(v___x_5810_, 1);
v_snd_5812_ = lean_ctor_get(v_a_5811_, 1);
lean_inc(v_snd_5812_);
lean_dec(v_a_5811_);
v_name_5813_ = lean_ctor_get(v_toConstantVal_5774_, 0);
lean_inc(v_name_5813_);
lean_dec_ref(v_toConstantVal_5774_);
v___x_5814_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5812_, v_name_5813_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
if (lean_obj_tag(v___x_5814_) == 0)
{
lean_object* v___x_5815_; lean_object* v_a_5816_; lean_object* v___x_5818_; uint8_t v_isShared_5819_; uint8_t v_isSharedCheck_5843_; 
lean_dec_ref_known(v___x_5814_, 1);
v___x_5815_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5808_, v___y_5770_);
v_a_5816_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5843_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5843_ == 0)
{
v___x_5818_ = v___x_5815_;
v_isShared_5819_ = v_isSharedCheck_5843_;
goto v_resetjp_5817_;
}
else
{
lean_inc(v_a_5816_);
lean_dec(v___x_5815_);
v___x_5818_ = lean_box(0);
v_isShared_5819_ = v_isSharedCheck_5843_;
goto v_resetjp_5817_;
}
v_resetjp_5817_:
{
uint8_t v___x_5820_; uint8_t v___x_5821_; uint8_t v___x_5822_; lean_object* v___x_5823_; 
v___x_5820_ = 0;
v___x_5821_ = 1;
v___x_5822_ = 1;
v___x_5823_ = l_Lean_Meta_mkLambdaFVars(v_xs_5767_, v_a_5816_, v___x_5820_, v___x_5821_, v___x_5820_, v___x_5821_, v___x_5822_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
lean_dec_ref(v_xs_5767_);
if (lean_obj_tag(v___x_5823_) == 0)
{
lean_object* v_a_5824_; lean_object* v___x_5826_; uint8_t v_isShared_5827_; uint8_t v_isSharedCheck_5834_; 
v_a_5824_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5834_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5834_ == 0)
{
v___x_5826_ = v___x_5823_;
v_isShared_5827_ = v_isSharedCheck_5834_;
goto v_resetjp_5825_;
}
else
{
lean_inc(v_a_5824_);
lean_dec(v___x_5823_);
v___x_5826_ = lean_box(0);
v_isShared_5827_ = v_isSharedCheck_5834_;
goto v_resetjp_5825_;
}
v_resetjp_5825_:
{
lean_object* v___x_5829_; 
if (v_isShared_5819_ == 0)
{
lean_ctor_set_tag(v___x_5818_, 1);
lean_ctor_set(v___x_5818_, 0, v_a_5824_);
v___x_5829_ = v___x_5818_;
goto v_reusejp_5828_;
}
else
{
lean_object* v_reuseFailAlloc_5833_; 
v_reuseFailAlloc_5833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5833_, 0, v_a_5824_);
v___x_5829_ = v_reuseFailAlloc_5833_;
goto v_reusejp_5828_;
}
v_reusejp_5828_:
{
lean_object* v___x_5831_; 
if (v_isShared_5827_ == 0)
{
lean_ctor_set(v___x_5826_, 0, v___x_5829_);
v___x_5831_ = v___x_5826_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v___x_5829_);
v___x_5831_ = v_reuseFailAlloc_5832_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
return v___x_5831_;
}
}
}
}
else
{
lean_object* v_a_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5842_; 
lean_del_object(v___x_5818_);
v_a_5835_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5842_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5842_ == 0)
{
v___x_5837_ = v___x_5823_;
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_a_5835_);
lean_dec(v___x_5823_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5842_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5840_; 
if (v_isShared_5838_ == 0)
{
v___x_5840_ = v___x_5837_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_a_5835_);
v___x_5840_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
return v___x_5840_;
}
}
}
}
}
else
{
lean_object* v_a_5844_; lean_object* v___x_5846_; uint8_t v_isShared_5847_; uint8_t v_isSharedCheck_5851_; 
lean_dec_ref(v___x_5808_);
lean_dec_ref(v_xs_5767_);
v_a_5844_ = lean_ctor_get(v___x_5814_, 0);
v_isSharedCheck_5851_ = !lean_is_exclusive(v___x_5814_);
if (v_isSharedCheck_5851_ == 0)
{
v___x_5846_ = v___x_5814_;
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
else
{
lean_inc(v_a_5844_);
lean_dec(v___x_5814_);
v___x_5846_ = lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
v_resetjp_5845_:
{
lean_object* v___x_5849_; 
if (v_isShared_5847_ == 0)
{
v___x_5849_ = v___x_5846_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5844_);
v___x_5849_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
return v___x_5849_;
}
}
}
}
else
{
lean_object* v_a_5852_; lean_object* v___x_5854_; uint8_t v_isShared_5855_; uint8_t v_isSharedCheck_5859_; 
lean_dec_ref(v___x_5808_);
lean_dec_ref(v_toConstantVal_5774_);
lean_dec_ref(v_xs_5767_);
v_a_5852_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5859_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5854_ = v___x_5810_;
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
else
{
lean_inc(v_a_5852_);
lean_dec(v___x_5810_);
v___x_5854_ = lean_box(0);
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
v_resetjp_5853_:
{
lean_object* v___x_5857_; 
if (v_isShared_5855_ == 0)
{
v___x_5857_ = v___x_5854_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_a_5852_);
v___x_5857_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5856_;
}
v_reusejp_5856_:
{
return v___x_5857_;
}
}
}
}
else
{
lean_object* v_a_5860_; lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5867_; 
lean_dec_ref(v___x_5799_);
lean_dec_ref(v_toConstantVal_5774_);
lean_dec_ref(v_xs_5767_);
v_a_5860_ = lean_ctor_get(v___x_5806_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v___x_5806_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5862_ = v___x_5806_;
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
else
{
lean_inc(v_a_5860_);
lean_dec(v___x_5806_);
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
lean_object* v___x_5868_; 
lean_dec(v_a_5803_);
lean_dec_ref(v___x_5799_);
lean_dec_ref(v_xs_5767_);
v___x_5868_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5764_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
return v___x_5868_;
}
}
else
{
lean_object* v_a_5869_; lean_object* v___x_5871_; uint8_t v_isShared_5872_; uint8_t v_isSharedCheck_5876_; 
lean_dec_ref(v___x_5799_);
lean_dec_ref(v_xs_5767_);
lean_dec_ref(v_ctorVal_5764_);
v_a_5869_ = lean_ctor_get(v___x_5802_, 0);
v_isSharedCheck_5876_ = !lean_is_exclusive(v___x_5802_);
if (v_isSharedCheck_5876_ == 0)
{
v___x_5871_ = v___x_5802_;
v_isShared_5872_ = v_isSharedCheck_5876_;
goto v_resetjp_5870_;
}
else
{
lean_inc(v_a_5869_);
lean_dec(v___x_5802_);
v___x_5871_ = lean_box(0);
v_isShared_5872_ = v_isSharedCheck_5876_;
goto v_resetjp_5870_;
}
v_resetjp_5870_:
{
lean_object* v___x_5874_; 
if (v_isShared_5872_ == 0)
{
v___x_5874_ = v___x_5871_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_a_5869_);
v___x_5874_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
return v___x_5874_;
}
}
}
}
else
{
lean_object* v_a_5877_; lean_object* v___x_5879_; uint8_t v_isShared_5880_; uint8_t v_isSharedCheck_5884_; 
lean_dec_ref(v___x_5799_);
lean_dec_ref(v_xs_5767_);
lean_dec_ref(v_ctorVal_5764_);
v_a_5877_ = lean_ctor_get(v___x_5800_, 0);
v_isSharedCheck_5884_ = !lean_is_exclusive(v___x_5800_);
if (v_isSharedCheck_5884_ == 0)
{
v___x_5879_ = v___x_5800_;
v_isShared_5880_ = v_isSharedCheck_5884_;
goto v_resetjp_5878_;
}
else
{
lean_inc(v_a_5877_);
lean_dec(v___x_5800_);
v___x_5879_ = lean_box(0);
v_isShared_5880_ = v_isSharedCheck_5884_;
goto v_resetjp_5878_;
}
v_resetjp_5878_:
{
lean_object* v___x_5882_; 
if (v_isShared_5880_ == 0)
{
v___x_5882_ = v___x_5879_;
goto v_reusejp_5881_;
}
else
{
lean_object* v_reuseFailAlloc_5883_; 
v_reuseFailAlloc_5883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5883_, 0, v_a_5877_);
v___x_5882_ = v_reuseFailAlloc_5883_;
goto v_reusejp_5881_;
}
v_reusejp_5881_:
{
return v___x_5882_;
}
}
}
}
else
{
lean_object* v_a_5885_; lean_object* v___x_5887_; uint8_t v_isShared_5888_; uint8_t v_isSharedCheck_5892_; 
lean_dec_ref(v_eqs_5789_);
lean_dec_ref(v_noConfusion_5783_);
lean_dec_ref(v_xs_5767_);
lean_dec_ref(v_ctorVal_5764_);
v_a_5885_ = lean_ctor_get(v___x_5792_, 0);
v_isSharedCheck_5892_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5892_ == 0)
{
v___x_5887_ = v___x_5792_;
v_isShared_5888_ = v_isSharedCheck_5892_;
goto v_resetjp_5886_;
}
else
{
lean_inc(v_a_5885_);
lean_dec(v___x_5792_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5899_, lean_object* v_us_5900_, lean_object* v_numIndices_5901_, lean_object* v_xs_5902_, lean_object* v_type_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_){
_start:
{
lean_object* v_res_5909_; 
v_res_5909_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5899_, v_us_5900_, v_numIndices_5901_, v_xs_5902_, v_type_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
lean_dec(v___y_5907_);
lean_dec_ref(v___y_5906_);
lean_dec(v___y_5905_);
lean_dec_ref(v___y_5904_);
lean_dec(v_numIndices_5901_);
return v_res_5909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5910_, lean_object* v_typeInfo_5911_, lean_object* v_a_5912_, lean_object* v_a_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_){
_start:
{
lean_object* v_thmType_5917_; lean_object* v_us_5918_; lean_object* v_numIndices_5919_; lean_object* v___f_5920_; uint8_t v___x_5921_; lean_object* v___x_5922_; 
v_thmType_5917_ = lean_ctor_get(v_typeInfo_5911_, 0);
lean_inc_ref(v_thmType_5917_);
v_us_5918_ = lean_ctor_get(v_typeInfo_5911_, 1);
lean_inc(v_us_5918_);
v_numIndices_5919_ = lean_ctor_get(v_typeInfo_5911_, 2);
lean_inc(v_numIndices_5919_);
lean_dec_ref(v_typeInfo_5911_);
v___f_5920_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5920_, 0, v_ctorVal_5910_);
lean_closure_set(v___f_5920_, 1, v_us_5918_);
lean_closure_set(v___f_5920_, 2, v_numIndices_5919_);
v___x_5921_ = 0;
v___x_5922_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5917_, v___f_5920_, v___x_5921_, v___x_5921_, v_a_5912_, v_a_5913_, v_a_5914_, v_a_5915_);
return v___x_5922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5923_, lean_object* v_typeInfo_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_){
_start:
{
lean_object* v_res_5930_; 
v_res_5930_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5923_, v_typeInfo_5924_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_);
lean_dec(v_a_5928_);
lean_dec_ref(v_a_5927_);
lean_dec(v_a_5926_);
lean_dec_ref(v_a_5925_);
return v_res_5930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5933_){
_start:
{
lean_object* v___x_5934_; lean_object* v___x_5935_; 
v___x_5934_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5935_ = l_Lean_Name_str___override(v_ctorName_5933_, v___x_5934_);
return v___x_5935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5936_, lean_object* v_ctorVal_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_){
_start:
{
lean_object* v___x_5943_; 
lean_inc_ref(v_ctorVal_5937_);
v___x_5943_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5937_, v_a_5938_, v_a_5939_, v_a_5940_, v_a_5941_);
if (lean_obj_tag(v___x_5943_) == 0)
{
lean_object* v_a_5944_; lean_object* v___x_5946_; uint8_t v_isShared_5947_; uint8_t v_isSharedCheck_6005_; 
v_a_5944_ = lean_ctor_get(v___x_5943_, 0);
v_isSharedCheck_6005_ = !lean_is_exclusive(v___x_5943_);
if (v_isSharedCheck_6005_ == 0)
{
v___x_5946_ = v___x_5943_;
v_isShared_5947_ = v_isSharedCheck_6005_;
goto v_resetjp_5945_;
}
else
{
lean_inc(v_a_5944_);
lean_dec(v___x_5943_);
v___x_5946_ = lean_box(0);
v_isShared_5947_ = v_isSharedCheck_6005_;
goto v_resetjp_5945_;
}
v_resetjp_5945_:
{
if (lean_obj_tag(v_a_5944_) == 1)
{
lean_object* v_val_5948_; lean_object* v___x_5949_; 
lean_del_object(v___x_5946_);
v_val_5948_ = lean_ctor_get(v_a_5944_, 0);
lean_inc_n(v_val_5948_, 2);
lean_dec_ref_known(v_a_5944_, 1);
lean_inc_ref(v_ctorVal_5937_);
v___x_5949_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5937_, v_val_5948_, v_a_5938_, v_a_5939_, v_a_5940_, v_a_5941_);
if (lean_obj_tag(v___x_5949_) == 0)
{
lean_object* v_a_5950_; lean_object* v___x_5952_; uint8_t v_isShared_5953_; uint8_t v_isSharedCheck_5992_; 
v_a_5950_ = lean_ctor_get(v___x_5949_, 0);
v_isSharedCheck_5992_ = !lean_is_exclusive(v___x_5949_);
if (v_isSharedCheck_5992_ == 0)
{
v___x_5952_ = v___x_5949_;
v_isShared_5953_ = v_isSharedCheck_5992_;
goto v_resetjp_5951_;
}
else
{
lean_inc(v_a_5950_);
lean_dec(v___x_5949_);
v___x_5952_ = lean_box(0);
v_isShared_5953_ = v_isSharedCheck_5992_;
goto v_resetjp_5951_;
}
v_resetjp_5951_:
{
if (lean_obj_tag(v_a_5950_) == 1)
{
lean_object* v_toConstantVal_5954_; lean_object* v_val_5955_; lean_object* v___x_5957_; uint8_t v_isShared_5958_; uint8_t v_isSharedCheck_5987_; 
v_toConstantVal_5954_ = lean_ctor_get(v_ctorVal_5937_, 0);
lean_inc_ref(v_toConstantVal_5954_);
lean_dec_ref(v_ctorVal_5937_);
v_val_5955_ = lean_ctor_get(v_a_5950_, 0);
v_isSharedCheck_5987_ = !lean_is_exclusive(v_a_5950_);
if (v_isSharedCheck_5987_ == 0)
{
v___x_5957_ = v_a_5950_;
v_isShared_5958_ = v_isSharedCheck_5987_;
goto v_resetjp_5956_;
}
else
{
lean_inc(v_val_5955_);
lean_dec(v_a_5950_);
v___x_5957_ = lean_box(0);
v_isShared_5958_ = v_isSharedCheck_5987_;
goto v_resetjp_5956_;
}
v_resetjp_5956_:
{
lean_object* v_levelParams_5959_; lean_object* v___x_5961_; uint8_t v_isShared_5962_; uint8_t v_isSharedCheck_5984_; 
v_levelParams_5959_ = lean_ctor_get(v_toConstantVal_5954_, 1);
v_isSharedCheck_5984_ = !lean_is_exclusive(v_toConstantVal_5954_);
if (v_isSharedCheck_5984_ == 0)
{
lean_object* v_unused_5985_; lean_object* v_unused_5986_; 
v_unused_5985_ = lean_ctor_get(v_toConstantVal_5954_, 2);
lean_dec(v_unused_5985_);
v_unused_5986_ = lean_ctor_get(v_toConstantVal_5954_, 0);
lean_dec(v_unused_5986_);
v___x_5961_ = v_toConstantVal_5954_;
v_isShared_5962_ = v_isSharedCheck_5984_;
goto v_resetjp_5960_;
}
else
{
lean_inc(v_levelParams_5959_);
lean_dec(v_toConstantVal_5954_);
v___x_5961_ = lean_box(0);
v_isShared_5962_ = v_isSharedCheck_5984_;
goto v_resetjp_5960_;
}
v_resetjp_5960_:
{
lean_object* v_thmType_5963_; lean_object* v___x_5965_; uint8_t v_isShared_5966_; uint8_t v_isSharedCheck_5981_; 
v_thmType_5963_ = lean_ctor_get(v_val_5948_, 0);
v_isSharedCheck_5981_ = !lean_is_exclusive(v_val_5948_);
if (v_isSharedCheck_5981_ == 0)
{
lean_object* v_unused_5982_; lean_object* v_unused_5983_; 
v_unused_5982_ = lean_ctor_get(v_val_5948_, 2);
lean_dec(v_unused_5982_);
v_unused_5983_ = lean_ctor_get(v_val_5948_, 1);
lean_dec(v_unused_5983_);
v___x_5965_ = v_val_5948_;
v_isShared_5966_ = v_isSharedCheck_5981_;
goto v_resetjp_5964_;
}
else
{
lean_inc(v_thmType_5963_);
lean_dec(v_val_5948_);
v___x_5965_ = lean_box(0);
v_isShared_5966_ = v_isSharedCheck_5981_;
goto v_resetjp_5964_;
}
v_resetjp_5964_:
{
lean_object* v___x_5968_; 
lean_inc(v_thmName_5936_);
if (v_isShared_5962_ == 0)
{
lean_ctor_set(v___x_5961_, 2, v_thmType_5963_);
lean_ctor_set(v___x_5961_, 0, v_thmName_5936_);
v___x_5968_ = v___x_5961_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_thmName_5936_);
lean_ctor_set(v_reuseFailAlloc_5980_, 1, v_levelParams_5959_);
lean_ctor_set(v_reuseFailAlloc_5980_, 2, v_thmType_5963_);
v___x_5968_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5972_; 
v___x_5969_ = lean_box(0);
v___x_5970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5970_, 0, v_thmName_5936_);
lean_ctor_set(v___x_5970_, 1, v___x_5969_);
if (v_isShared_5966_ == 0)
{
lean_ctor_set(v___x_5965_, 2, v___x_5970_);
lean_ctor_set(v___x_5965_, 1, v_val_5955_);
lean_ctor_set(v___x_5965_, 0, v___x_5968_);
v___x_5972_ = v___x_5965_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v___x_5968_);
lean_ctor_set(v_reuseFailAlloc_5979_, 1, v_val_5955_);
lean_ctor_set(v_reuseFailAlloc_5979_, 2, v___x_5970_);
v___x_5972_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
lean_object* v___x_5974_; 
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 0, v___x_5972_);
v___x_5974_ = v___x_5957_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5978_; 
v_reuseFailAlloc_5978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5978_, 0, v___x_5972_);
v___x_5974_ = v_reuseFailAlloc_5978_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
lean_object* v___x_5976_; 
if (v_isShared_5953_ == 0)
{
lean_ctor_set(v___x_5952_, 0, v___x_5974_);
v___x_5976_ = v___x_5952_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v___x_5974_);
v___x_5976_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
return v___x_5976_;
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
lean_object* v___x_5988_; lean_object* v___x_5990_; 
lean_dec(v_a_5950_);
lean_dec(v_val_5948_);
lean_dec_ref(v_ctorVal_5937_);
lean_dec(v_thmName_5936_);
v___x_5988_ = lean_box(0);
if (v_isShared_5953_ == 0)
{
lean_ctor_set(v___x_5952_, 0, v___x_5988_);
v___x_5990_ = v___x_5952_;
goto v_reusejp_5989_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v___x_5988_);
v___x_5990_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5989_;
}
v_reusejp_5989_:
{
return v___x_5990_;
}
}
}
}
else
{
lean_object* v_a_5993_; lean_object* v___x_5995_; uint8_t v_isShared_5996_; uint8_t v_isSharedCheck_6000_; 
lean_dec(v_val_5948_);
lean_dec_ref(v_ctorVal_5937_);
lean_dec(v_thmName_5936_);
v_a_5993_ = lean_ctor_get(v___x_5949_, 0);
v_isSharedCheck_6000_ = !lean_is_exclusive(v___x_5949_);
if (v_isSharedCheck_6000_ == 0)
{
v___x_5995_ = v___x_5949_;
v_isShared_5996_ = v_isSharedCheck_6000_;
goto v_resetjp_5994_;
}
else
{
lean_inc(v_a_5993_);
lean_dec(v___x_5949_);
v___x_5995_ = lean_box(0);
v_isShared_5996_ = v_isSharedCheck_6000_;
goto v_resetjp_5994_;
}
v_resetjp_5994_:
{
lean_object* v___x_5998_; 
if (v_isShared_5996_ == 0)
{
v___x_5998_ = v___x_5995_;
goto v_reusejp_5997_;
}
else
{
lean_object* v_reuseFailAlloc_5999_; 
v_reuseFailAlloc_5999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_a_5993_);
v___x_5998_ = v_reuseFailAlloc_5999_;
goto v_reusejp_5997_;
}
v_reusejp_5997_:
{
return v___x_5998_;
}
}
}
}
else
{
lean_object* v___x_6001_; lean_object* v___x_6003_; 
lean_dec(v_a_5944_);
lean_dec_ref(v_ctorVal_5937_);
lean_dec(v_thmName_5936_);
v___x_6001_ = lean_box(0);
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 0, v___x_6001_);
v___x_6003_ = v___x_5946_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v___x_6001_);
v___x_6003_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
return v___x_6003_;
}
}
}
}
else
{
lean_object* v_a_6006_; lean_object* v___x_6008_; uint8_t v_isShared_6009_; uint8_t v_isSharedCheck_6013_; 
lean_dec_ref(v_ctorVal_5937_);
lean_dec(v_thmName_5936_);
v_a_6006_ = lean_ctor_get(v___x_5943_, 0);
v_isSharedCheck_6013_ = !lean_is_exclusive(v___x_5943_);
if (v_isSharedCheck_6013_ == 0)
{
v___x_6008_ = v___x_5943_;
v_isShared_6009_ = v_isSharedCheck_6013_;
goto v_resetjp_6007_;
}
else
{
lean_inc(v_a_6006_);
lean_dec(v___x_5943_);
v___x_6008_ = lean_box(0);
v_isShared_6009_ = v_isSharedCheck_6013_;
goto v_resetjp_6007_;
}
v_resetjp_6007_:
{
lean_object* v___x_6011_; 
if (v_isShared_6009_ == 0)
{
v___x_6011_ = v___x_6008_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v_a_6006_);
v___x_6011_ = v_reuseFailAlloc_6012_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
return v___x_6011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6014_, lean_object* v_ctorVal_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_){
_start:
{
lean_object* v_res_6021_; 
v_res_6021_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6014_, v_ctorVal_6015_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_);
lean_dec(v_a_6019_);
lean_dec_ref(v_a_6018_);
lean_dec(v_a_6017_);
lean_dec_ref(v_a_6016_);
return v_res_6021_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6022_, lean_object* v_n_6023_){
_start:
{
if (lean_obj_tag(v_n_6023_) == 1)
{
lean_object* v_pre_6024_; lean_object* v_str_6025_; lean_object* v___x_6026_; uint8_t v___x_6027_; 
v_pre_6024_ = lean_ctor_get(v_n_6023_, 0);
lean_inc(v_pre_6024_);
v_str_6025_ = lean_ctor_get(v_n_6023_, 1);
lean_inc_ref(v_str_6025_);
lean_dec_ref_known(v_n_6023_, 2);
v___x_6026_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6027_ = lean_string_dec_eq(v_str_6025_, v___x_6026_);
lean_dec_ref(v_str_6025_);
if (v___x_6027_ == 0)
{
lean_dec(v_pre_6024_);
lean_dec_ref(v_env_6022_);
return v___x_6027_;
}
else
{
uint8_t v___x_6028_; lean_object* v___x_6029_; 
v___x_6028_ = 0;
v___x_6029_ = l_Lean_Environment_find_x3f(v_env_6022_, v_pre_6024_, v___x_6028_);
if (lean_obj_tag(v___x_6029_) == 1)
{
lean_object* v_val_6030_; 
v_val_6030_ = lean_ctor_get(v___x_6029_, 0);
lean_inc(v_val_6030_);
lean_dec_ref_known(v___x_6029_, 1);
if (lean_obj_tag(v_val_6030_) == 6)
{
lean_dec_ref_known(v_val_6030_, 1);
return v___x_6027_;
}
else
{
lean_dec(v_val_6030_);
return v___x_6028_;
}
}
else
{
lean_dec(v___x_6029_);
return v___x_6028_;
}
}
}
else
{
uint8_t v___x_6031_; 
lean_dec(v_n_6023_);
lean_dec_ref(v_env_6022_);
v___x_6031_ = 0;
return v___x_6031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6032_, lean_object* v_n_6033_){
_start:
{
uint8_t v_res_6034_; lean_object* v_r_6035_; 
v_res_6034_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6032_, v_n_6033_);
v_r_6035_ = lean_box(v_res_6034_);
return v_r_6035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6038_; lean_object* v___x_6039_; 
v___f_6038_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6039_ = l_Lean_registerReservedNamePredicate(v___f_6038_);
return v___x_6039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6040_){
_start:
{
lean_object* v_res_6041_; 
v_res_6041_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6041_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6042_, lean_object* v___y_6043_){
_start:
{
lean_object* v___x_6045_; lean_object* v_env_6046_; lean_object* v_toConstantVal_6047_; lean_object* v_value_6048_; lean_object* v_all_6049_; lean_object* v_type_6056_; uint8_t v___x_6057_; 
v___x_6045_ = lean_st_ref_get(v___y_6043_);
v_env_6046_ = lean_ctor_get(v___x_6045_, 0);
lean_inc_ref_n(v_env_6046_, 2);
lean_dec(v___x_6045_);
v_toConstantVal_6047_ = lean_ctor_get(v_thm_6042_, 0);
v_value_6048_ = lean_ctor_get(v_thm_6042_, 1);
v_all_6049_ = lean_ctor_get(v_thm_6042_, 2);
v_type_6056_ = lean_ctor_get(v_toConstantVal_6047_, 2);
v___x_6057_ = l_Lean_Environment_hasUnsafe(v_env_6046_, v_type_6056_);
if (v___x_6057_ == 0)
{
uint8_t v___x_6058_; 
v___x_6058_ = l_Lean_Environment_hasUnsafe(v_env_6046_, v_value_6048_);
if (v___x_6058_ == 0)
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6059_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6059_, 0, v_thm_6042_);
v___x_6060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6059_);
return v___x_6060_;
}
else
{
lean_inc(v_all_6049_);
lean_inc_ref(v_value_6048_);
lean_inc_ref(v_toConstantVal_6047_);
lean_dec_ref(v_thm_6042_);
goto v___jp_6050_;
}
}
else
{
lean_inc(v_all_6049_);
lean_inc_ref(v_value_6048_);
lean_inc_ref(v_toConstantVal_6047_);
lean_dec_ref(v_env_6046_);
lean_dec_ref(v_thm_6042_);
goto v___jp_6050_;
}
v___jp_6050_:
{
lean_object* v___x_6051_; uint8_t v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; 
v___x_6051_ = lean_box(0);
v___x_6052_ = 0;
v___x_6053_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6053_, 0, v_toConstantVal_6047_);
lean_ctor_set(v___x_6053_, 1, v_value_6048_);
lean_ctor_set(v___x_6053_, 2, v___x_6051_);
lean_ctor_set(v___x_6053_, 3, v_all_6049_);
lean_ctor_set_uint8(v___x_6053_, sizeof(void*)*4, v___x_6052_);
v___x_6054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
v___x_6055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
return v___x_6055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6061_, lean_object* v___y_6062_, lean_object* v___y_6063_){
_start:
{
lean_object* v_res_6064_; 
v_res_6064_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6061_, v___y_6062_);
lean_dec(v___y_6062_);
return v_res_6064_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_){
_start:
{
lean_object* v___x_6071_; 
v___x_6071_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6065_, v___y_6069_);
return v___x_6071_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_){
_start:
{
lean_object* v_res_6078_; 
v_res_6078_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_);
lean_dec(v___y_6076_);
lean_dec_ref(v___y_6075_);
lean_dec(v___y_6074_);
lean_dec_ref(v___y_6073_);
return v_res_6078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6079_, uint8_t v___x_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_){
_start:
{
lean_object* v___x_6086_; lean_object* v_a_6087_; lean_object* v___x_6088_; 
v___x_6086_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6079_, v___y_6084_);
v_a_6087_ = lean_ctor_get(v___x_6086_, 0);
lean_inc(v_a_6087_);
lean_dec_ref(v___x_6086_);
v___x_6088_ = l_Lean_addDecl(v_a_6087_, v___x_6080_, v___y_6083_, v___y_6084_);
return v___x_6088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6089_, lean_object* v___x_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_){
_start:
{
uint8_t v___x_2167__boxed_6096_; lean_object* v_res_6097_; 
v___x_2167__boxed_6096_ = lean_unbox(v___x_6090_);
v_res_6097_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6089_, v___x_2167__boxed_6096_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_);
lean_dec(v___y_6094_);
lean_dec_ref(v___y_6093_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
return v_res_6097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6100_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_6101_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6102_ = lean_unsigned_to_nat(0u);
v___x_6103_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6102_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
lean_ctor_set(v___x_6103_, 2, v___x_6102_);
lean_ctor_set(v___x_6103_, 3, v___x_6102_);
lean_ctor_set(v___x_6103_, 4, v___x_6101_);
lean_ctor_set(v___x_6103_, 5, v___x_6101_);
lean_ctor_set(v___x_6103_, 6, v___x_6101_);
lean_ctor_set(v___x_6103_, 7, v___x_6101_);
lean_ctor_set(v___x_6103_, 8, v___x_6101_);
lean_ctor_set(v___x_6103_, 9, v___x_6101_);
lean_ctor_set(v___x_6103_, 10, v___x_6101_);
lean_ctor_set(v___x_6103_, 11, v___x_6100_);
return v___x_6103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6104_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6105_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6104_);
lean_ctor_set(v___x_6105_, 1, v___x_6104_);
lean_ctor_set(v___x_6105_, 2, v___x_6104_);
lean_ctor_set(v___x_6105_, 3, v___x_6104_);
lean_ctor_set(v___x_6105_, 4, v___x_6104_);
lean_ctor_set(v___x_6105_, 5, v___x_6104_);
lean_ctor_set(v___x_6105_, 6, v___x_6104_);
return v___x_6105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6106_; lean_object* v___x_6107_; 
v___x_6106_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6106_);
lean_ctor_set(v___x_6107_, 1, v___x_6106_);
lean_ctor_set(v___x_6107_, 2, v___x_6106_);
lean_ctor_set(v___x_6107_, 3, v___x_6106_);
lean_ctor_set(v___x_6107_, 4, v___x_6106_);
return v___x_6107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6108_, lean_object* v_name_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_){
_start:
{
if (lean_obj_tag(v_name_6109_) == 1)
{
lean_object* v_pre_6121_; lean_object* v_str_6122_; lean_object* v___x_6123_; uint8_t v___x_6124_; 
v_pre_6121_ = lean_ctor_get(v_name_6109_, 0);
lean_inc(v_pre_6121_);
v_str_6122_ = lean_ctor_get(v_name_6109_, 1);
v___x_6123_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6124_ = lean_string_dec_eq(v_str_6122_, v___x_6123_);
if (v___x_6124_ == 0)
{
lean_dec_ref_known(v_name_6109_, 2);
lean_dec(v_pre_6121_);
lean_dec(v___x_6108_);
goto v___jp_6117_;
}
else
{
lean_object* v___x_6125_; lean_object* v_env_6126_; uint8_t v___x_6127_; lean_object* v___x_6128_; 
v___x_6125_ = lean_st_ref_get(v___y_6111_);
v_env_6126_ = lean_ctor_get(v___x_6125_, 0);
lean_inc_ref(v_env_6126_);
lean_dec(v___x_6125_);
v___x_6127_ = 0;
lean_inc(v_pre_6121_);
v___x_6128_ = l_Lean_Environment_find_x3f(v_env_6126_, v_pre_6121_, v___x_6127_);
if (lean_obj_tag(v___x_6128_) == 1)
{
lean_object* v_val_6129_; 
v_val_6129_ = lean_ctor_get(v___x_6128_, 0);
lean_inc(v_val_6129_);
lean_dec_ref_known(v___x_6128_, 1);
if (lean_obj_tag(v_val_6129_) == 6)
{
lean_object* v_val_6130_; lean_object* v___x_6132_; uint8_t v_isShared_6133_; uint8_t v_isSharedCheck_6180_; 
v_val_6130_ = lean_ctor_get(v_val_6129_, 0);
v_isSharedCheck_6180_ = !lean_is_exclusive(v_val_6129_);
if (v_isSharedCheck_6180_ == 0)
{
v___x_6132_ = v_val_6129_;
v_isShared_6133_ = v_isSharedCheck_6180_;
goto v_resetjp_6131_;
}
else
{
lean_inc(v_val_6130_);
lean_dec(v_val_6129_);
v___x_6132_ = lean_box(0);
v_isShared_6133_ = v_isSharedCheck_6180_;
goto v_resetjp_6131_;
}
v_resetjp_6131_:
{
uint8_t v___x_6134_; uint8_t v___x_6135_; uint8_t v___x_6136_; lean_object* v___x_6137_; uint64_t v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; uint8_t v_a_6152_; lean_object* v___x_6158_; 
v___x_6134_ = 1;
v___x_6135_ = 0;
v___x_6136_ = 2;
v___x_6137_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_6137_, 0, v___x_6127_);
lean_ctor_set_uint8(v___x_6137_, 1, v___x_6127_);
lean_ctor_set_uint8(v___x_6137_, 2, v___x_6127_);
lean_ctor_set_uint8(v___x_6137_, 3, v___x_6127_);
lean_ctor_set_uint8(v___x_6137_, 4, v___x_6127_);
lean_ctor_set_uint8(v___x_6137_, 5, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 6, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 7, v___x_6127_);
lean_ctor_set_uint8(v___x_6137_, 8, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 9, v___x_6134_);
lean_ctor_set_uint8(v___x_6137_, 10, v___x_6135_);
lean_ctor_set_uint8(v___x_6137_, 11, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 12, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 13, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 14, v___x_6136_);
lean_ctor_set_uint8(v___x_6137_, 15, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 16, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 17, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 18, v___x_6124_);
lean_ctor_set_uint8(v___x_6137_, 19, v___x_6127_);
v___x_6138_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6137_);
v___x_6139_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6139_, 0, v___x_6137_);
lean_ctor_set_uint64(v___x_6139_, sizeof(void*)*1, v___x_6138_);
v___x_6140_ = lean_unsigned_to_nat(0u);
v___x_6141_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_6142_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6143_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6144_ = lean_box(0);
lean_inc(v___x_6108_);
v___x_6145_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6145_, 0, v___x_6139_);
lean_ctor_set(v___x_6145_, 1, v___x_6108_);
lean_ctor_set(v___x_6145_, 2, v___x_6142_);
lean_ctor_set(v___x_6145_, 3, v___x_6143_);
lean_ctor_set(v___x_6145_, 4, v___x_6144_);
lean_ctor_set(v___x_6145_, 5, v___x_6140_);
lean_ctor_set(v___x_6145_, 6, v___x_6144_);
lean_ctor_set_uint8(v___x_6145_, sizeof(void*)*7, v___x_6127_);
lean_ctor_set_uint8(v___x_6145_, sizeof(void*)*7 + 1, v___x_6127_);
lean_ctor_set_uint8(v___x_6145_, sizeof(void*)*7 + 2, v___x_6127_);
lean_ctor_set_uint8(v___x_6145_, sizeof(void*)*7 + 3, v___x_6124_);
v___x_6146_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6147_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6148_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6146_);
lean_ctor_set(v___x_6149_, 1, v___x_6147_);
lean_ctor_set(v___x_6149_, 2, v___x_6108_);
lean_ctor_set(v___x_6149_, 3, v___x_6141_);
lean_ctor_set(v___x_6149_, 4, v___x_6148_);
v___x_6150_ = lean_st_mk_ref(v___x_6149_);
lean_inc_ref(v_name_6109_);
v___x_6158_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6109_, v_val_6130_, v___x_6145_, v___x_6150_, v___y_6110_, v___y_6111_);
if (lean_obj_tag(v___x_6158_) == 0)
{
lean_object* v_a_6159_; 
v_a_6159_ = lean_ctor_get(v___x_6158_, 0);
lean_inc(v_a_6159_);
lean_dec_ref_known(v___x_6158_, 1);
if (lean_obj_tag(v_a_6159_) == 1)
{
lean_object* v_val_6160_; lean_object* v___x_6161_; lean_object* v___f_6162_; lean_object* v___x_6163_; 
v_val_6160_ = lean_ctor_get(v_a_6159_, 0);
lean_inc(v_val_6160_);
lean_dec_ref_known(v_a_6159_, 1);
v___x_6161_ = lean_box(v___x_6127_);
v___f_6162_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6162_, 0, v_val_6160_);
lean_closure_set(v___f_6162_, 1, v___x_6161_);
v___x_6163_ = l_Lean_Meta_realizeConst(v_pre_6121_, v_name_6109_, v___f_6162_, v___x_6145_, v___x_6150_, v___y_6110_, v___y_6111_);
lean_dec_ref_known(v___x_6145_, 7);
if (lean_obj_tag(v___x_6163_) == 0)
{
lean_dec_ref_known(v___x_6163_, 1);
v_a_6152_ = v___x_6124_;
goto v___jp_6151_;
}
else
{
lean_object* v_a_6164_; lean_object* v___x_6166_; uint8_t v_isShared_6167_; uint8_t v_isSharedCheck_6171_; 
lean_dec(v___x_6150_);
lean_del_object(v___x_6132_);
v_a_6164_ = lean_ctor_get(v___x_6163_, 0);
v_isSharedCheck_6171_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6171_ == 0)
{
v___x_6166_ = v___x_6163_;
v_isShared_6167_ = v_isSharedCheck_6171_;
goto v_resetjp_6165_;
}
else
{
lean_inc(v_a_6164_);
lean_dec(v___x_6163_);
v___x_6166_ = lean_box(0);
v_isShared_6167_ = v_isSharedCheck_6171_;
goto v_resetjp_6165_;
}
v_resetjp_6165_:
{
lean_object* v___x_6169_; 
if (v_isShared_6167_ == 0)
{
v___x_6169_ = v___x_6166_;
goto v_reusejp_6168_;
}
else
{
lean_object* v_reuseFailAlloc_6170_; 
v_reuseFailAlloc_6170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6170_, 0, v_a_6164_);
v___x_6169_ = v_reuseFailAlloc_6170_;
goto v_reusejp_6168_;
}
v_reusejp_6168_:
{
return v___x_6169_;
}
}
}
}
else
{
lean_dec(v_a_6159_);
lean_dec_ref_known(v___x_6145_, 7);
lean_dec(v_pre_6121_);
lean_dec_ref_known(v_name_6109_, 2);
v_a_6152_ = v___x_6127_;
goto v___jp_6151_;
}
}
else
{
lean_object* v_a_6172_; lean_object* v___x_6174_; uint8_t v_isShared_6175_; uint8_t v_isSharedCheck_6179_; 
lean_dec(v___x_6150_);
lean_dec_ref_known(v___x_6145_, 7);
lean_del_object(v___x_6132_);
lean_dec_ref_known(v_name_6109_, 2);
lean_dec(v_pre_6121_);
v_a_6172_ = lean_ctor_get(v___x_6158_, 0);
v_isSharedCheck_6179_ = !lean_is_exclusive(v___x_6158_);
if (v_isSharedCheck_6179_ == 0)
{
v___x_6174_ = v___x_6158_;
v_isShared_6175_ = v_isSharedCheck_6179_;
goto v_resetjp_6173_;
}
else
{
lean_inc(v_a_6172_);
lean_dec(v___x_6158_);
v___x_6174_ = lean_box(0);
v_isShared_6175_ = v_isSharedCheck_6179_;
goto v_resetjp_6173_;
}
v_resetjp_6173_:
{
lean_object* v___x_6177_; 
if (v_isShared_6175_ == 0)
{
v___x_6177_ = v___x_6174_;
goto v_reusejp_6176_;
}
else
{
lean_object* v_reuseFailAlloc_6178_; 
v_reuseFailAlloc_6178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6178_, 0, v_a_6172_);
v___x_6177_ = v_reuseFailAlloc_6178_;
goto v_reusejp_6176_;
}
v_reusejp_6176_:
{
return v___x_6177_;
}
}
}
v___jp_6151_:
{
lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6156_; 
v___x_6153_ = lean_st_ref_get(v___x_6150_);
lean_dec(v___x_6150_);
lean_dec(v___x_6153_);
v___x_6154_ = lean_box(v_a_6152_);
if (v_isShared_6133_ == 0)
{
lean_ctor_set_tag(v___x_6132_, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6154_);
v___x_6156_ = v___x_6132_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6157_; 
v_reuseFailAlloc_6157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6157_, 0, v___x_6154_);
v___x_6156_ = v_reuseFailAlloc_6157_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
return v___x_6156_;
}
}
}
}
else
{
lean_dec(v_val_6129_);
lean_dec_ref_known(v_name_6109_, 2);
lean_dec(v_pre_6121_);
lean_dec(v___x_6108_);
goto v___jp_6113_;
}
}
else
{
lean_dec(v___x_6128_);
lean_dec_ref_known(v_name_6109_, 2);
lean_dec(v_pre_6121_);
lean_dec(v___x_6108_);
goto v___jp_6113_;
}
}
}
else
{
lean_dec(v_name_6109_);
lean_dec(v___x_6108_);
goto v___jp_6117_;
}
v___jp_6113_:
{
uint8_t v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; 
v___x_6114_ = 0;
v___x_6115_ = lean_box(v___x_6114_);
v___x_6116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
return v___x_6116_;
}
v___jp_6117_:
{
uint8_t v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; 
v___x_6118_ = 0;
v___x_6119_ = lean_box(v___x_6118_);
v___x_6120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
return v___x_6120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6181_, lean_object* v_name_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_){
_start:
{
lean_object* v_res_6186_; 
v_res_6186_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6181_, v_name_6182_, v___y_6183_, v___y_6184_);
lean_dec(v___y_6184_);
lean_dec_ref(v___y_6183_);
return v_res_6186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6190_; lean_object* v___x_6191_; 
v___f_6190_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6191_ = l_Lean_registerReservedNameAction(v___f_6190_);
return v___x_6191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6192_){
_start:
{
lean_object* v_res_6193_; 
v_res_6193_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6193_;
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
