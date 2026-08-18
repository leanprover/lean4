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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__3;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "unexpected number of goals after applying `Lean.and_imp`"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "injEq_helper"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(167, 111, 180, 146, 132, 58, 155, 57)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "propIntro"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(189, 136, 38, 165, 207, 169, 133, 34)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "unexpected number of subgoals when proving injective theorem for constructor `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6;
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__4;
static const lean_array_object l_Lean_Meta_mkInjectiveTheorems___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__5 = (const lean_object*)&l_Lean_Meta_mkInjectiveTheorems___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 101, 109, 194, 24, 99, 201, 78)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(74, 76, 255, 124, 31, 108, 47, 16)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 106, 16, 37, 3, 60, 11, 157)}};
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 151, 10, 103, 183, 199, 62, 165)}};
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17;
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_m_82_, lean_object* v_query_83_, lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_zero_87_; uint8_t v_isZero_88_; 
v_zero_87_ = lean_unsigned_to_nat(0u);
v_isZero_88_ = lean_nat_dec_eq(v_x_85_, v_zero_87_);
if (v_isZero_88_ == 1)
{
lean_dec(v_x_86_);
lean_dec(v_x_85_);
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(2);
return v___x_89_;
}
else
{
lean_object* v_val_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_val_90_ = lean_ctor_get(v_x_84_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v_x_84_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_val_90_);
lean_dec(v_x_84_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_val_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
lean_object* v_keyArray_98_; lean_object* v_valueArray_99_; lean_object* v___x_100_; uint8_t v_isSome_101_; 
v_keyArray_98_ = lean_ctor_get(v_m_82_, 1);
v_valueArray_99_ = lean_ctor_get(v_m_82_, 2);
v___x_100_ = lean_array_fget_borrowed(v_keyArray_98_, v_x_86_);
v_isSome_101_ = lean_noption_is_some(v___x_100_);
if (v_isSome_101_ == 0)
{
lean_dec(v_x_85_);
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_x_86_);
return v___x_102_;
}
else
{
lean_object* v_val_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
lean_dec(v_x_86_);
v_val_103_ = lean_ctor_get(v_x_84_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v_x_84_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_val_103_);
lean_dec(v_x_84_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_val_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
else
{
lean_object* v_one_111_; lean_object* v_n_112_; lean_object* v___y_114_; 
v_one_111_ = lean_unsigned_to_nat(1u);
v_n_112_ = lean_nat_sub(v_x_85_, v_one_111_);
lean_dec(v_x_85_);
if (v_isSome_101_ == 0)
{
goto v___jp_120_;
}
else
{
lean_object* v___x_122_; uint8_t v_isSome_123_; 
v___x_122_ = lean_array_fget_borrowed(v_valueArray_99_, v_x_86_);
v_isSome_123_ = lean_noption_is_some(v___x_122_);
if (v_isSome_123_ == 0)
{
goto v___jp_120_;
}
else
{
lean_object* v_val_124_; uint8_t v___x_125_; 
lean_inc(v___x_100_);
v_val_124_ = lean_noption_get(v___x_100_);
v___x_125_ = l_Lean_ExprStructEq_beq(v_val_124_, v_query_83_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
lean_dec(v_val_124_);
v___x_126_ = lean_array_get_size(v_keyArray_98_);
v___x_127_ = lean_nat_add(v_x_86_, v_one_111_);
lean_dec(v_x_86_);
v___x_128_ = lean_nat_dec_lt(v___x_127_, v___x_126_);
if (v___x_128_ == 0)
{
lean_dec(v___x_127_);
v_x_85_ = v_n_112_;
v_x_86_ = v_zero_87_;
goto _start;
}
else
{
v_x_85_ = v_n_112_;
v_x_86_ = v___x_127_;
goto _start;
}
}
else
{
lean_object* v_val_131_; lean_object* v___x_132_; 
lean_dec(v_n_112_);
lean_dec(v_x_84_);
lean_inc(v___x_122_);
v_val_131_ = lean_noption_get(v___x_122_);
v___x_132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_132_, 0, v_x_86_);
lean_ctor_set(v___x_132_, 1, v_val_124_);
lean_ctor_set(v___x_132_, 2, v_val_131_);
return v___x_132_;
}
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_array_get_size(v_keyArray_98_);
v___x_116_ = lean_nat_add(v_x_86_, v_one_111_);
lean_dec(v_x_86_);
v___x_117_ = lean_nat_dec_lt(v___x_116_, v___x_115_);
if (v___x_117_ == 0)
{
lean_dec(v___x_116_);
v_x_84_ = v___y_114_;
v_x_85_ = v_n_112_;
v_x_86_ = v_zero_87_;
goto _start;
}
else
{
v_x_84_ = v___y_114_;
v_x_85_ = v_n_112_;
v_x_86_ = v___x_116_;
goto _start;
}
}
v___jp_120_:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v___x_121_; 
lean_inc(v_x_86_);
v___x_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_121_, 0, v_x_86_);
v___y_114_ = v___x_121_;
goto v___jp_113_;
}
else
{
v___y_114_ = v_x_84_;
goto v___jp_113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_m_133_, lean_object* v_query_134_, lean_object* v_x_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_m_133_, v_query_134_, v_x_135_, v_x_136_, v_x_137_);
lean_dec_ref(v_query_134_);
lean_dec_ref(v_m_133_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object* v_m_139_, lean_object* v_query_140_){
_start:
{
lean_object* v_keyArray_141_; lean_object* v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; uint64_t v_fold_146_; uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v___x_149_; size_t v___x_150_; size_t v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_keyArray_141_ = lean_ctor_get(v_m_139_, 1);
v___x_142_ = lean_array_get_size(v_keyArray_141_);
v___x_143_ = l_Lean_ExprStructEq_hash(v_query_140_);
v___x_144_ = 32ULL;
v___x_145_ = lean_uint64_shift_right(v___x_143_, v___x_144_);
v_fold_146_ = lean_uint64_xor(v___x_143_, v___x_145_);
v___x_147_ = 16ULL;
v___x_148_ = lean_uint64_shift_right(v_fold_146_, v___x_147_);
v___x_149_ = lean_uint64_xor(v_fold_146_, v___x_148_);
v___x_150_ = lean_uint64_to_usize(v___x_149_);
v___x_151_ = lean_usize_of_nat(v___x_142_);
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_sub(v___x_151_, v___x_152_);
v___x_154_ = lean_usize_land(v___x_150_, v___x_153_);
v___x_155_ = lean_usize_to_nat(v___x_154_);
v___x_156_ = lean_box(0);
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_m_139_, v_query_140_, v___x_156_, v___x_142_, v___x_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_m_158_, lean_object* v_query_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_158_, v_query_159_);
lean_dec_ref(v_query_159_);
lean_dec_ref(v_m_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(lean_object* v_b_161_, lean_object* v_acc_162_, lean_object* v_i_163_){
_start:
{
lean_object* v___y_165_; lean_object* v_keyArray_173_; lean_object* v_valueArray_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_keyArray_173_ = lean_ctor_get(v_b_161_, 1);
v_valueArray_174_ = lean_ctor_get(v_b_161_, 2);
v___x_175_ = lean_array_get_size(v_keyArray_173_);
v___x_176_ = lean_nat_dec_lt(v_i_163_, v___x_175_);
if (v___x_176_ == 0)
{
lean_dec(v_i_163_);
return v_acc_162_;
}
else
{
lean_object* v___x_177_; uint8_t v_isSome_178_; 
v___x_177_ = lean_array_fget_borrowed(v_keyArray_173_, v_i_163_);
v_isSome_178_ = lean_noption_is_some(v___x_177_);
if (v_isSome_178_ == 0)
{
goto v___jp_169_;
}
else
{
lean_object* v___x_179_; uint8_t v_isSome_180_; 
v___x_179_ = lean_array_fget_borrowed(v_valueArray_174_, v_i_163_);
v_isSome_180_ = lean_noption_is_some(v___x_179_);
if (v_isSome_180_ == 0)
{
goto v___jp_169_;
}
else
{
lean_object* v_val_181_; lean_object* v_val_182_; lean_object* v_i_184_; lean_object* v___x_189_; 
lean_inc(v___x_177_);
v_val_181_ = lean_noption_get(v___x_177_);
lean_inc(v___x_179_);
v_val_182_ = lean_noption_get(v___x_179_);
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_acc_162_, v_val_181_);
switch(lean_obj_tag(v___x_189_))
{
case 0:
{
lean_object* v_index_190_; lean_object* v_size_191_; lean_object* v___x_192_; 
v_index_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_index_190_);
lean_dec_ref_known(v___x_189_, 3);
v_size_191_ = lean_ctor_get(v_acc_162_, 0);
lean_inc(v_size_191_);
v___x_192_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_162_, v_size_191_, v_index_190_, v_val_181_, v_val_182_);
lean_dec(v_index_190_);
v___y_165_ = v___x_192_;
goto v___jp_164_;
}
case 1:
{
lean_object* v_index_193_; 
v_index_193_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_index_193_);
lean_dec_ref_known(v___x_189_, 1);
v_i_184_ = v_index_193_;
goto v___jp_183_;
}
default: 
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_162_, v___x_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_index_196_; 
v_index_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_index_196_);
lean_dec_ref_known(v___x_195_, 1);
v_i_184_ = v_index_196_;
goto v___jp_183_;
}
else
{
lean_dec(v_val_182_);
lean_dec(v_val_181_);
v___y_165_ = v_acc_162_;
goto v___jp_164_;
}
}
}
v___jp_183_:
{
lean_object* v_size_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_size_185_ = lean_ctor_get(v_acc_162_, 0);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_size_185_, v___x_186_);
v___x_188_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_162_, v___x_187_, v_i_184_, v_val_181_, v_val_182_);
lean_dec(v_i_184_);
v___y_165_ = v___x_188_;
goto v___jp_164_;
}
}
}
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_i_163_, v___x_166_);
lean_dec(v_i_163_);
v_acc_162_ = v___y_165_;
v_i_163_ = v___x_167_;
goto _start;
}
v___jp_169_:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_add(v_i_163_, v___x_170_);
lean_dec(v_i_163_);
v_i_163_ = v___x_171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13___redArg___boxed(lean_object* v_b_197_, lean_object* v_acc_198_, lean_object* v_i_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_197_, v_acc_198_, v_i_199_);
lean_dec_ref(v_b_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12___redArg(lean_object* v_init_201_, lean_object* v_b_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_202_, v_init_201_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12___redArg___boxed(lean_object* v_init_205_, lean_object* v_b_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12___redArg(v_init_205_, v_b_206_);
lean_dec_ref(v_b_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___redArg(lean_object* v_m_208_){
_start:
{
lean_object* v_keyArray_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_cellCount_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_target_216_; lean_object* v___x_217_; 
v_keyArray_209_ = lean_ctor_get(v_m_208_, 1);
v___x_210_ = lean_array_get_size(v_keyArray_209_);
v___x_211_ = lean_unsigned_to_nat(2u);
v_cellCount_212_ = lean_nat_mul(v___x_210_, v___x_211_);
v___x_213_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_212_);
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_212_);
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_212_);
v_target_216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_216_, 0, v___x_213_);
lean_ctor_set(v_target_216_, 1, v___x_214_);
lean_ctor_set(v_target_216_, 2, v___x_215_);
v___x_217_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12___redArg(v_target_216_, v_m_208_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_m_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___redArg(v_m_218_);
lean_dec_ref(v_m_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(lean_object* v_a_220_, lean_object* v_e_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___y_227_; lean_object* v___y_230_; lean_object* v_i_231_; lean_object* v___y_247_; lean_object* v_i_248_; lean_object* v___y_254_; lean_object* v___x_263_; 
v___x_224_ = lean_st_ref_take(v_a_220_);
v___x_225_ = lean_box(0);
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v___x_224_, v_e_221_);
switch(lean_obj_tag(v___x_263_))
{
case 0:
{
lean_object* v_index_264_; lean_object* v_size_265_; lean_object* v___x_266_; 
v_index_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_index_264_);
lean_dec_ref_known(v___x_263_, 3);
v_size_265_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_size_265_);
v___x_266_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_224_, v_size_265_, v_index_264_, v_e_221_, v_a_222_);
lean_dec(v_index_264_);
v___y_227_ = v___x_266_;
goto v___jp_226_;
}
case 1:
{
lean_object* v_index_267_; lean_object* v_size_268_; lean_object* v_keyArray_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_index_267_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_index_267_);
lean_dec_ref_known(v___x_263_, 1);
v_size_268_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_size_268_);
v_keyArray_269_ = lean_ctor_get(v___x_224_, 1);
lean_inc_ref(v_keyArray_269_);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_size_268_, v___x_270_);
lean_dec(v_size_268_);
v___x_272_ = lean_array_get_size(v_keyArray_269_);
lean_dec_ref(v_keyArray_269_);
v___x_273_ = lean_nat_dec_lt(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v___x_271_);
lean_dec(v_index_267_);
goto v___jp_236_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_274_ = lean_unsigned_to_nat(4u);
v___x_275_ = lean_nat_mul(v___x_271_, v___x_274_);
v___x_276_ = lean_unsigned_to_nat(3u);
v___x_277_ = lean_nat_mul(v___x_272_, v___x_276_);
v___x_278_ = lean_nat_dec_le(v___x_275_, v___x_277_);
lean_dec(v___x_277_);
lean_dec(v___x_275_);
if (v___x_278_ == 0)
{
lean_dec(v___x_271_);
lean_dec(v_index_267_);
goto v___jp_236_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_224_, v___x_271_, v_index_267_, v_e_221_, v_a_222_);
lean_dec(v_index_267_);
v___y_227_ = v___x_279_;
goto v___jp_226_;
}
}
}
default: 
{
lean_object* v_size_280_; lean_object* v_keyArray_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_size_280_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_size_280_);
v_keyArray_281_ = lean_ctor_get(v___x_224_, 1);
lean_inc_ref(v_keyArray_281_);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_add(v_size_280_, v___x_282_);
lean_dec(v_size_280_);
v___x_284_ = lean_array_get_size(v_keyArray_281_);
lean_dec_ref(v_keyArray_281_);
v___x_285_ = lean_nat_dec_lt(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_dec(v___x_283_);
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___redArg(v___x_224_);
lean_dec(v___x_224_);
v___y_254_ = v___x_286_;
goto v___jp_253_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_287_ = lean_unsigned_to_nat(4u);
v___x_288_ = lean_nat_mul(v___x_283_, v___x_287_);
lean_dec(v___x_283_);
v___x_289_ = lean_unsigned_to_nat(3u);
v___x_290_ = lean_nat_mul(v___x_284_, v___x_289_);
v___x_291_ = lean_nat_dec_le(v___x_288_, v___x_290_);
lean_dec(v___x_290_);
lean_dec(v___x_288_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___redArg(v___x_224_);
lean_dec(v___x_224_);
v___y_254_ = v___x_292_;
goto v___jp_253_;
}
else
{
v___y_254_ = v___x_224_;
goto v___jp_253_;
}
}
}
}
v___jp_226_:
{
lean_object* v___x_228_; 
v___x_228_ = lean_st_ref_put(v_a_220_, v___y_227_);
return v___x_225_;
}
v___jp_229_:
{
lean_object* v_size_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_size_232_ = lean_ctor_get(v___y_230_, 0);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_size_232_, v___x_233_);
v___x_235_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_230_, v___x_234_, v_i_231_, v_e_221_, v_a_222_);
lean_dec(v_i_231_);
v___y_227_ = v___x_235_;
goto v___jp_226_;
}
v___jp_236_:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___redArg(v___x_224_);
lean_dec(v___x_224_);
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v___x_237_, v_e_221_);
switch(lean_obj_tag(v___x_238_))
{
case 0:
{
lean_object* v_index_239_; lean_object* v_size_240_; lean_object* v___x_241_; 
v_index_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_index_239_);
lean_dec_ref_known(v___x_238_, 3);
v_size_240_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_size_240_);
v___x_241_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_237_, v_size_240_, v_index_239_, v_e_221_, v_a_222_);
lean_dec(v_index_239_);
v___y_227_ = v___x_241_;
goto v___jp_226_;
}
case 1:
{
lean_object* v_index_242_; 
v_index_242_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_index_242_);
lean_dec_ref_known(v___x_238_, 1);
v___y_230_ = v___x_237_;
v_i_231_ = v_index_242_;
goto v___jp_229_;
}
default: 
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_237_, v___x_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_index_245_; 
v_index_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_index_245_);
lean_dec_ref_known(v___x_244_, 1);
v___y_230_ = v___x_237_;
v_i_231_ = v_index_245_;
goto v___jp_229_;
}
else
{
lean_dec_ref(v_a_222_);
lean_dec_ref(v_e_221_);
v___y_227_ = v___x_237_;
goto v___jp_226_;
}
}
}
}
v___jp_246_:
{
lean_object* v_size_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_size_249_ = lean_ctor_get(v___y_247_, 0);
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_add(v_size_249_, v___x_250_);
v___x_252_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_247_, v___x_251_, v_i_248_, v_e_221_, v_a_222_);
lean_dec(v_i_248_);
v___y_227_ = v___x_252_;
goto v___jp_226_;
}
v___jp_253_:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v___y_254_, v_e_221_);
switch(lean_obj_tag(v___x_255_))
{
case 0:
{
lean_object* v_index_256_; lean_object* v_size_257_; lean_object* v___x_258_; 
v_index_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_index_256_);
lean_dec_ref_known(v___x_255_, 3);
v_size_257_ = lean_ctor_get(v___y_254_, 0);
lean_inc(v_size_257_);
v___x_258_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_254_, v_size_257_, v_index_256_, v_e_221_, v_a_222_);
lean_dec(v_index_256_);
v___y_227_ = v___x_258_;
goto v___jp_226_;
}
case 1:
{
lean_object* v_index_259_; 
v_index_259_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_index_259_);
lean_dec_ref_known(v___x_255_, 1);
v___y_247_ = v___y_254_;
v_i_248_ = v_index_259_;
goto v___jp_246_;
}
default: 
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_254_, v___x_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_index_262_; 
v_index_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_index_262_);
lean_dec_ref_known(v___x_261_, 1);
v___y_247_ = v___y_254_;
v_i_248_ = v_index_262_;
goto v___jp_246_;
}
else
{
lean_dec_ref(v_a_222_);
lean_dec_ref(v_e_221_);
v___y_227_ = v___y_254_;
goto v___jp_226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed(lean_object* v_a_293_, lean_object* v_e_294_, lean_object* v_a_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(v_a_293_, v_e_294_, v_a_295_);
lean_dec(v_a_293_);
return v_res_297_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_box(0);
v___x_299_ = l_Lean_interruptExceptionId;
v___x_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_305_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_Lean_maxRecDepthErrorMessage;
v___x_312_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_314_ = l_Lean_MessageData_ofFormat(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_316_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_317_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_318_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_ref_318_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(lean_object* v_x_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___y_332_; lean_object* v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; uint8_t v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; uint8_t v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v_fileName_362_; lean_object* v_fileMap_363_; lean_object* v_options_364_; lean_object* v_currRecDepth_365_; lean_object* v_maxRecDepth_366_; lean_object* v_ref_367_; lean_object* v_currNamespace_368_; lean_object* v_openDecls_369_; lean_object* v_initHeartbeats_370_; lean_object* v_maxHeartbeats_371_; lean_object* v_quotContext_372_; lean_object* v_currMacroScope_373_; uint8_t v_diag_374_; lean_object* v_cancelTk_x3f_375_; uint8_t v_suppressElabErrors_376_; lean_object* v_inheritedTraceOptions_377_; 
v_fileName_362_ = lean_ctor_get(v___y_328_, 0);
v_fileMap_363_ = lean_ctor_get(v___y_328_, 1);
v_options_364_ = lean_ctor_get(v___y_328_, 2);
v_currRecDepth_365_ = lean_ctor_get(v___y_328_, 3);
v_maxRecDepth_366_ = lean_ctor_get(v___y_328_, 4);
v_ref_367_ = lean_ctor_get(v___y_328_, 5);
v_currNamespace_368_ = lean_ctor_get(v___y_328_, 6);
v_openDecls_369_ = lean_ctor_get(v___y_328_, 7);
v_initHeartbeats_370_ = lean_ctor_get(v___y_328_, 8);
v_maxHeartbeats_371_ = lean_ctor_get(v___y_328_, 9);
v_quotContext_372_ = lean_ctor_get(v___y_328_, 10);
v_currMacroScope_373_ = lean_ctor_get(v___y_328_, 11);
v_diag_374_ = lean_ctor_get_uint8(v___y_328_, sizeof(void*)*14);
v_cancelTk_x3f_375_ = lean_ctor_get(v___y_328_, 12);
v_suppressElabErrors_376_ = lean_ctor_get_uint8(v___y_328_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_377_ = lean_ctor_get(v___y_328_, 13);
if (lean_obj_tag(v_cancelTk_x3f_375_) == 1)
{
lean_object* v_val_383_; uint8_t v___x_384_; 
v_val_383_ = lean_ctor_get(v_cancelTk_x3f_375_, 0);
v___x_384_ = l_IO_CancelToken_isSet(v_val_383_);
if (v___x_384_ == 0)
{
goto v___jp_378_;
}
else
{
lean_object* v___x_385_; lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec_ref(v_x_326_);
v___x_385_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
goto v___jp_378_;
}
v___jp_331_:
{
if (lean_obj_tag(v___y_332_) == 0)
{
return v___y_332_;
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
v_a_333_ = lean_ctor_get(v___y_332_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___y_332_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___y_332_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___y_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
v___jp_341_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v___y_355_, v___x_358_);
lean_inc_ref(v___y_349_);
lean_inc(v___y_350_);
lean_inc(v___y_343_);
lean_inc(v___y_345_);
lean_inc(v___y_348_);
lean_inc(v___y_352_);
lean_inc(v___y_353_);
lean_inc(v___y_354_);
lean_inc(v___y_342_);
lean_inc_ref(v___y_357_);
lean_inc_ref(v___y_344_);
lean_inc_ref(v___y_356_);
v___x_360_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_360_, 0, v___y_356_);
lean_ctor_set(v___x_360_, 1, v___y_344_);
lean_ctor_set(v___x_360_, 2, v___y_357_);
lean_ctor_set(v___x_360_, 3, v___x_359_);
lean_ctor_set(v___x_360_, 4, v___y_342_);
lean_ctor_set(v___x_360_, 5, v___y_346_);
lean_ctor_set(v___x_360_, 6, v___y_354_);
lean_ctor_set(v___x_360_, 7, v___y_353_);
lean_ctor_set(v___x_360_, 8, v___y_352_);
lean_ctor_set(v___x_360_, 9, v___y_348_);
lean_ctor_set(v___x_360_, 10, v___y_345_);
lean_ctor_set(v___x_360_, 11, v___y_343_);
lean_ctor_set(v___x_360_, 12, v___y_350_);
lean_ctor_set(v___x_360_, 13, v___y_349_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*14, v___y_351_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*14 + 1, v___y_347_);
lean_inc(v___y_329_);
lean_inc(v___y_327_);
v___x_361_ = lean_apply_4(v_x_326_, v___y_327_, v___x_360_, v___y_329_, lean_box(0));
v___y_332_ = v___x_361_;
goto v___jp_331_;
}
v___jp_378_:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_nat_dec_eq(v_maxRecDepth_366_, v___x_379_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_eq(v_currRecDepth_365_, v_maxRecDepth_366_);
if (v___x_381_ == 0)
{
lean_inc(v_ref_367_);
v___y_342_ = v_maxRecDepth_366_;
v___y_343_ = v_currMacroScope_373_;
v___y_344_ = v_fileMap_363_;
v___y_345_ = v_quotContext_372_;
v___y_346_ = v_ref_367_;
v___y_347_ = v_suppressElabErrors_376_;
v___y_348_ = v_maxHeartbeats_371_;
v___y_349_ = v_inheritedTraceOptions_377_;
v___y_350_ = v_cancelTk_x3f_375_;
v___y_351_ = v_diag_374_;
v___y_352_ = v_initHeartbeats_370_;
v___y_353_ = v_openDecls_369_;
v___y_354_ = v_currNamespace_368_;
v___y_355_ = v_currRecDepth_365_;
v___y_356_ = v_fileName_362_;
v___y_357_ = v_options_364_;
goto v___jp_341_;
}
else
{
lean_object* v___x_382_; 
lean_dec_ref(v_x_326_);
lean_inc(v_ref_367_);
v___x_382_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_367_);
v___y_332_ = v___x_382_;
goto v___jp_331_;
}
}
else
{
lean_inc(v_ref_367_);
v___y_342_ = v_maxRecDepth_366_;
v___y_343_ = v_currMacroScope_373_;
v___y_344_ = v_fileMap_363_;
v___y_345_ = v_quotContext_372_;
v___y_346_ = v_ref_367_;
v___y_347_ = v_suppressElabErrors_376_;
v___y_348_ = v_maxHeartbeats_371_;
v___y_349_ = v_inheritedTraceOptions_377_;
v___y_350_ = v_cancelTk_x3f_375_;
v___y_351_ = v_diag_374_;
v___y_352_ = v_initHeartbeats_370_;
v___y_353_ = v_openDecls_369_;
v___y_354_ = v_currNamespace_368_;
v___y_355_ = v_currRecDepth_365_;
v___y_356_ = v_fileName_362_;
v___y_357_ = v_options_364_;
goto v___jp_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_400_, lean_object* v_x_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_apply_1(v_x_401_, lean_box(0));
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_407_, lean_object* v_x_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_407_, v_x_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_m_413_, lean_object* v_query_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_413_, v_query_414_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_index_416_; lean_object* v_key_417_; lean_object* v_value_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_index_416_ = lean_ctor_get(v___x_415_, 0);
v_key_417_ = lean_ctor_get(v___x_415_, 1);
v_value_418_ = lean_ctor_get(v___x_415_, 2);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_415_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_value_418_);
lean_inc(v_key_417_);
lean_inc(v_index_416_);
lean_dec(v___x_415_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_index_416_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_key_417_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_value_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v___x_426_; 
lean_dec(v___x_415_);
v___x_426_ = lean_box(1);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_m_427_, lean_object* v_query_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_m_427_, v_query_428_);
lean_dec_ref(v_query_428_);
lean_dec_ref(v_m_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_m_430_, v_a_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_value_433_; lean_object* v___x_434_; 
v_value_433_ = lean_ctor_get(v___x_432_, 2);
lean_inc(v_value_433_);
lean_dec_ref_known(v___x_432_, 3);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_value_433_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; 
v___x_435_ = lean_box(0);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_436_, v_a_437_);
lean_dec_ref(v_a_437_);
lean_dec_ref(v_m_436_);
return v_res_438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_440_; lean_object* v_dummy_441_; 
v___x_440_ = lean_box(0);
v_dummy_441_ = l_Lean_Expr_sort___override(v___x_440_);
return v_dummy_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_442_, lean_object* v_post_443_, size_t v_sz_444_, size_t v_i_445_, lean_object* v_bs_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = lean_usize_dec_lt(v_i_445_, v_sz_444_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_442_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_bs_446_);
return v___x_452_;
}
else
{
lean_object* v_v_453_; lean_object* v___x_454_; 
v_v_453_ = lean_array_uget_borrowed(v_bs_446_, v_i_445_);
lean_inc(v_v_453_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_442_);
v___x_454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_442_, v_post_443_, v_v_453_, v___y_447_, v___y_448_, v___y_449_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_456_; lean_object* v_bs_x27_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v___x_456_ = lean_unsigned_to_nat(0u);
v_bs_x27_457_ = lean_array_uset(v_bs_446_, v_i_445_, v___x_456_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_i_445_, v___x_458_);
v___x_460_ = lean_array_uset(v_bs_x27_457_, v_i_445_, v_a_455_);
v_i_445_ = v___x_459_;
v_bs_446_ = v___x_460_;
goto _start;
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref(v_bs_446_);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_442_);
v_a_462_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_454_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_454_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_470_, lean_object* v_post_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
if (lean_obj_tag(v_x_472_) == 5)
{
lean_object* v_fn_479_; lean_object* v_arg_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_fn_479_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_fn_479_);
v_arg_480_ = lean_ctor_get(v_x_472_, 1);
lean_inc_ref(v_arg_480_);
lean_dec_ref_known(v_x_472_, 2);
v___x_481_ = lean_array_set(v_x_473_, v_x_474_, v_arg_480_);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_sub(v_x_474_, v___x_482_);
lean_dec(v_x_474_);
v_x_472_ = v_fn_479_;
v_x_473_ = v___x_481_;
v_x_474_ = v___x_483_;
goto _start;
}
else
{
lean_object* v___x_485_; 
lean_dec(v_x_474_);
lean_inc_ref(v_post_471_);
lean_inc_ref(v_pre_470_);
v___x_485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_470_, v_post_471_, v_x_472_, v___y_475_, v___y_476_, v___y_477_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; size_t v_sz_487_; size_t v___x_488_; lean_object* v___x_489_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v_sz_487_ = lean_array_size(v_x_473_);
v___x_488_ = ((size_t)0ULL);
lean_inc_ref(v_post_471_);
lean_inc_ref(v_pre_470_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_470_, v_post_471_, v_sz_487_, v___x_488_, v_x_473_, v___y_475_, v___y_476_, v___y_477_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v___x_491_ = l_Lean_mkAppN(v_a_486_, v_a_490_);
lean_dec(v_a_490_);
v___x_492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_470_, v_post_471_, v___x_491_, v___y_475_, v___y_476_, v___y_477_);
return v___x_492_;
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_a_486_);
lean_dec_ref(v_post_471_);
lean_dec_ref(v_pre_470_);
v_a_493_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_489_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_489_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_dec_ref(v_x_473_);
lean_dec_ref(v_post_471_);
lean_dec_ref(v_pre_470_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_501_, lean_object* v_pre_502_, lean_object* v_e_503_, lean_object* v_post_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; uint8_t v___y_515_; lean_object* v___y_516_; uint8_t v___y_517_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; uint8_t v___y_531_; uint8_t v___y_532_; lean_object* v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; uint8_t v___y_545_; lean_object* v___x_552_; 
v___x_552_ = l_Lean_Core_checkSystem(v___x_501_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; 
lean_dec_ref_known(v___x_552_, 1);
lean_inc_ref(v_pre_502_);
lean_inc(v___y_507_);
lean_inc_ref(v___y_506_);
lean_inc_ref(v_e_503_);
v___x_553_ = lean_apply_4(v_pre_502_, v_e_503_, v___y_506_, v___y_507_, lean_box(0));
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_643_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_643_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_643_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_643_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___y_559_; 
switch(lean_obj_tag(v_a_554_))
{
case 0:
{
lean_object* v_e_633_; lean_object* v___x_635_; 
lean_dec_ref(v_post_504_);
lean_dec_ref(v_e_503_);
lean_dec_ref(v_pre_502_);
v_e_633_ = lean_ctor_get(v_a_554_, 0);
lean_inc_ref(v_e_633_);
lean_dec_ref_known(v_a_554_, 1);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_e_633_);
v___x_635_ = v___x_556_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_e_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
case 1:
{
lean_object* v_e_637_; lean_object* v___x_638_; 
lean_del_object(v___x_556_);
lean_dec_ref(v_e_503_);
v_e_637_ = lean_ctor_get(v_a_554_, 0);
lean_inc_ref(v_e_637_);
lean_dec_ref_known(v_a_554_, 1);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_638_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_e_637_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v_a_639_, v___y_505_, v___y_506_, v___y_507_);
return v___x_640_;
}
else
{
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_638_;
}
}
default: 
{
lean_object* v_e_x3f_641_; 
lean_del_object(v___x_556_);
v_e_x3f_641_ = lean_ctor_get(v_a_554_, 0);
lean_inc(v_e_x3f_641_);
lean_dec_ref_known(v_a_554_, 1);
if (lean_obj_tag(v_e_x3f_641_) == 0)
{
v___y_559_ = v_e_503_;
goto v___jp_558_;
}
else
{
lean_object* v_val_642_; 
lean_dec_ref(v_e_503_);
v_val_642_ = lean_ctor_get(v_e_x3f_641_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v_e_x3f_641_, 1);
v___y_559_ = v_val_642_;
goto v___jp_558_;
}
}
}
v___jp_558_:
{
switch(lean_obj_tag(v___y_559_))
{
case 7:
{
lean_object* v_binderName_560_; lean_object* v_binderType_561_; lean_object* v_body_562_; uint8_t v_binderInfo_563_; lean_object* v___x_564_; 
v_binderName_560_ = lean_ctor_get(v___y_559_, 0);
lean_inc(v_binderName_560_);
v_binderType_561_ = lean_ctor_get(v___y_559_, 1);
v_body_562_ = lean_ctor_get(v___y_559_, 2);
v_binderInfo_563_ = lean_ctor_get_uint8(v___y_559_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_561_);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_564_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_binderType_561_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
lean_inc_ref(v_body_562_);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_566_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_body_562_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; size_t v___x_568_; size_t v___x_569_; uint8_t v___x_570_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v___x_568_ = lean_ptr_addr(v_binderType_561_);
v___x_569_ = lean_ptr_addr(v_a_565_);
v___x_570_ = lean_usize_dec_eq(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
v___y_540_ = v_a_565_;
v___y_541_ = v_binderName_560_;
v___y_542_ = v_binderInfo_563_;
v___y_543_ = v_a_567_;
v___y_544_ = v___y_559_;
v___y_545_ = v___x_570_;
goto v___jp_539_;
}
else
{
size_t v___x_571_; size_t v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_ptr_addr(v_body_562_);
v___x_572_ = lean_ptr_addr(v_a_567_);
v___x_573_ = lean_usize_dec_eq(v___x_571_, v___x_572_);
v___y_540_ = v_a_565_;
v___y_541_ = v_binderName_560_;
v___y_542_ = v_binderInfo_563_;
v___y_543_ = v_a_567_;
v___y_544_ = v___y_559_;
v___y_545_ = v___x_573_;
goto v___jp_539_;
}
}
else
{
lean_dec(v_a_565_);
lean_dec(v_binderName_560_);
lean_dec_ref_known(v___y_559_, 3);
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_566_;
}
}
else
{
lean_dec(v_binderName_560_);
lean_dec_ref_known(v___y_559_, 3);
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_564_;
}
}
case 6:
{
lean_object* v_binderName_574_; lean_object* v_binderType_575_; lean_object* v_body_576_; uint8_t v_binderInfo_577_; lean_object* v___x_578_; 
v_binderName_574_ = lean_ctor_get(v___y_559_, 0);
lean_inc(v_binderName_574_);
v_binderType_575_ = lean_ctor_get(v___y_559_, 1);
v_body_576_ = lean_ctor_get(v___y_559_, 2);
v_binderInfo_577_ = lean_ctor_get_uint8(v___y_559_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_575_);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_578_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_binderType_575_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
lean_inc_ref(v_body_576_);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_580_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_body_576_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; size_t v___x_582_; size_t v___x_583_; uint8_t v___x_584_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = lean_ptr_addr(v_binderType_575_);
v___x_583_ = lean_ptr_addr(v_a_579_);
v___x_584_ = lean_usize_dec_eq(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
v___y_527_ = v_a_581_;
v___y_528_ = v___y_559_;
v___y_529_ = v_binderName_574_;
v___y_530_ = v_a_579_;
v___y_531_ = v_binderInfo_577_;
v___y_532_ = v___x_584_;
goto v___jp_526_;
}
else
{
size_t v___x_585_; size_t v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_ptr_addr(v_body_576_);
v___x_586_ = lean_ptr_addr(v_a_581_);
v___x_587_ = lean_usize_dec_eq(v___x_585_, v___x_586_);
v___y_527_ = v_a_581_;
v___y_528_ = v___y_559_;
v___y_529_ = v_binderName_574_;
v___y_530_ = v_a_579_;
v___y_531_ = v_binderInfo_577_;
v___y_532_ = v___x_587_;
goto v___jp_526_;
}
}
else
{
lean_dec(v_a_579_);
lean_dec_ref_known(v___y_559_, 3);
lean_dec(v_binderName_574_);
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_580_;
}
}
else
{
lean_dec(v_binderName_574_);
lean_dec_ref_known(v___y_559_, 3);
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_578_;
}
}
case 8:
{
lean_object* v_declName_588_; lean_object* v_type_589_; lean_object* v_value_590_; lean_object* v_body_591_; uint8_t v_nondep_592_; lean_object* v___x_593_; 
v_declName_588_ = lean_ctor_get(v___y_559_, 0);
lean_inc(v_declName_588_);
v_type_589_ = lean_ctor_get(v___y_559_, 1);
v_value_590_ = lean_ctor_get(v___y_559_, 2);
v_body_591_ = lean_ctor_get(v___y_559_, 3);
lean_inc_ref(v_body_591_);
v_nondep_592_ = lean_ctor_get_uint8(v___y_559_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_589_);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_593_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_type_589_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
lean_inc_ref(v_value_590_);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_595_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_value_590_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
lean_inc_ref(v_body_591_);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_597_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_body_591_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; size_t v___x_599_; size_t v___x_600_; uint8_t v___x_601_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = lean_ptr_addr(v_type_589_);
v___x_600_ = lean_ptr_addr(v_a_594_);
v___x_601_ = lean_usize_dec_eq(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
v___y_510_ = v_a_596_;
v___y_511_ = v_body_591_;
v___y_512_ = v_a_598_;
v___y_513_ = v_a_594_;
v___y_514_ = v_declName_588_;
v___y_515_ = v_nondep_592_;
v___y_516_ = v___y_559_;
v___y_517_ = v___x_601_;
goto v___jp_509_;
}
else
{
size_t v___x_602_; size_t v___x_603_; uint8_t v___x_604_; 
v___x_602_ = lean_ptr_addr(v_value_590_);
v___x_603_ = lean_ptr_addr(v_a_596_);
v___x_604_ = lean_usize_dec_eq(v___x_602_, v___x_603_);
v___y_510_ = v_a_596_;
v___y_511_ = v_body_591_;
v___y_512_ = v_a_598_;
v___y_513_ = v_a_594_;
v___y_514_ = v_declName_588_;
v___y_515_ = v_nondep_592_;
v___y_516_ = v___y_559_;
v___y_517_ = v___x_604_;
goto v___jp_509_;
}
}
else
{
lean_dec(v_a_596_);
lean_dec(v_a_594_);
lean_dec_ref(v_body_591_);
lean_dec_ref_known(v___y_559_, 4);
lean_dec(v_declName_588_);
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_597_;
}
}
else
{
lean_dec(v_a_594_);
lean_dec_ref(v_body_591_);
lean_dec_ref_known(v___y_559_, 4);
lean_dec(v_declName_588_);
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_595_;
}
}
else
{
lean_dec_ref(v_body_591_);
lean_dec(v_declName_588_);
lean_dec_ref_known(v___y_559_, 4);
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_593_;
}
}
case 5:
{
lean_object* v_dummy_605_; lean_object* v_nargs_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_dummy_605_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_606_ = l_Lean_Expr_getAppNumArgs(v___y_559_);
lean_inc(v_nargs_606_);
v___x_607_ = lean_mk_array(v_nargs_606_, v_dummy_605_);
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_sub(v_nargs_606_, v___x_608_);
lean_dec(v_nargs_606_);
v___x_610_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_502_, v_post_504_, v___y_559_, v___x_607_, v___x_609_, v___y_505_, v___y_506_, v___y_507_);
return v___x_610_;
}
case 10:
{
lean_object* v_data_611_; lean_object* v_expr_612_; lean_object* v___x_613_; 
v_data_611_ = lean_ctor_get(v___y_559_, 0);
v_expr_612_ = lean_ctor_get(v___y_559_, 1);
lean_inc_ref(v_expr_612_);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_613_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_expr_612_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; size_t v___x_615_; size_t v___x_616_; uint8_t v___x_617_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v___x_615_ = lean_ptr_addr(v_expr_612_);
v___x_616_ = lean_ptr_addr(v_a_614_);
v___x_617_ = lean_usize_dec_eq(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_inc(v_data_611_);
lean_dec_ref_known(v___y_559_, 2);
v___x_618_ = l_Lean_Expr_mdata___override(v_data_611_, v_a_614_);
v___x_619_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___x_618_, v___y_505_, v___y_506_, v___y_507_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; 
lean_dec(v_a_614_);
v___x_620_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___y_559_, v___y_505_, v___y_506_, v___y_507_);
return v___x_620_;
}
}
else
{
lean_dec_ref_known(v___y_559_, 2);
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_613_;
}
}
case 11:
{
lean_object* v_typeName_621_; lean_object* v_idx_622_; lean_object* v_struct_623_; lean_object* v___x_624_; 
v_typeName_621_ = lean_ctor_get(v___y_559_, 0);
v_idx_622_ = lean_ctor_get(v___y_559_, 1);
v_struct_623_ = lean_ctor_get(v___y_559_, 2);
lean_inc_ref(v_struct_623_);
lean_inc_ref(v_post_504_);
lean_inc_ref(v_pre_502_);
v___x_624_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_502_, v_post_504_, v_struct_623_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; size_t v___x_626_; size_t v___x_627_; uint8_t v___x_628_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = lean_ptr_addr(v_struct_623_);
v___x_627_ = lean_ptr_addr(v_a_625_);
v___x_628_ = lean_usize_dec_eq(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_inc(v_idx_622_);
lean_inc(v_typeName_621_);
lean_dec_ref_known(v___y_559_, 3);
v___x_629_ = l_Lean_Expr_proj___override(v_typeName_621_, v_idx_622_, v_a_625_);
v___x_630_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___x_629_, v___y_505_, v___y_506_, v___y_507_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; 
lean_dec(v_a_625_);
v___x_631_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___y_559_, v___y_505_, v___y_506_, v___y_507_);
return v___x_631_;
}
}
else
{
lean_dec_ref_known(v___y_559_, 3);
lean_dec_ref(v_post_504_);
lean_dec_ref(v_pre_502_);
return v___x_624_;
}
}
default: 
{
lean_object* v___x_632_; 
v___x_632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___y_559_, v___y_505_, v___y_506_, v___y_507_);
return v___x_632_;
}
}
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v_post_504_);
lean_dec_ref(v_e_503_);
lean_dec_ref(v_pre_502_);
v_a_644_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_553_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_553_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v_post_504_);
lean_dec_ref(v_e_503_);
lean_dec_ref(v_pre_502_);
v_a_652_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_552_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_552_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
v___jp_509_:
{
if (v___y_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec_ref(v___y_516_);
lean_dec_ref(v___y_511_);
v___x_518_ = l_Lean_Expr_letE___override(v___y_514_, v___y_513_, v___y_510_, v___y_512_, v___y_515_);
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___x_518_, v___y_505_, v___y_506_, v___y_507_);
return v___x_519_;
}
else
{
size_t v___x_520_; size_t v___x_521_; uint8_t v___x_522_; 
v___x_520_ = lean_ptr_addr(v___y_511_);
lean_dec_ref(v___y_511_);
v___x_521_ = lean_ptr_addr(v___y_512_);
v___x_522_ = lean_usize_dec_eq(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec_ref(v___y_516_);
v___x_523_ = l_Lean_Expr_letE___override(v___y_514_, v___y_513_, v___y_510_, v___y_512_, v___y_515_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___x_523_, v___y_505_, v___y_506_, v___y_507_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; 
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v___y_510_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___y_516_, v___y_505_, v___y_506_, v___y_507_);
return v___x_525_;
}
}
}
v___jp_526_:
{
if (v___y_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec_ref(v___y_528_);
v___x_533_ = l_Lean_Expr_lam___override(v___y_529_, v___y_530_, v___y_527_, v___y_531_);
v___x_534_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___x_533_, v___y_505_, v___y_506_, v___y_507_);
return v___x_534_;
}
else
{
uint8_t v___x_535_; 
v___x_535_ = l_Lean_instBEqBinderInfo_beq(v___y_531_, v___y_531_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v___y_528_);
v___x_536_ = l_Lean_Expr_lam___override(v___y_529_, v___y_530_, v___y_527_, v___y_531_);
v___x_537_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___x_536_, v___y_505_, v___y_506_, v___y_507_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; 
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_527_);
v___x_538_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___y_528_, v___y_505_, v___y_506_, v___y_507_);
return v___x_538_;
}
}
}
v___jp_539_:
{
if (v___y_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec_ref(v___y_544_);
v___x_546_ = l_Lean_Expr_forallE___override(v___y_541_, v___y_540_, v___y_543_, v___y_542_);
v___x_547_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___x_546_, v___y_505_, v___y_506_, v___y_507_);
return v___x_547_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = l_Lean_instBEqBinderInfo_beq(v___y_542_, v___y_542_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec_ref(v___y_544_);
v___x_549_ = l_Lean_Expr_forallE___override(v___y_541_, v___y_540_, v___y_543_, v___y_542_);
v___x_550_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___x_549_, v___y_505_, v___y_506_, v___y_507_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
lean_dec_ref(v___y_543_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
v___x_551_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_502_, v_post_504_, v___y_544_, v___y_505_, v___y_506_, v___y_507_);
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_660_, lean_object* v_pre_661_, lean_object* v_e_662_, lean_object* v_post_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_660_, v_pre_661_, v_e_662_, v_post_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_669_, lean_object* v_post_670_, lean_object* v_e_671_, lean_object* v_a_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_inc(v_a_672_);
v___x_676_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_676_, 0, lean_box(0));
lean_closure_set(v___x_676_, 1, lean_box(0));
lean_closure_set(v___x_676_, 2, v_a_672_);
v___x_677_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_676_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_709_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_709_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_709_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_709_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; 
v___x_682_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_678_, v_e_671_);
lean_dec(v_a_678_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_683_; lean_object* v___f_684_; lean_object* v___x_685_; 
lean_del_object(v___x_680_);
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_671_);
v___f_684_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_684_, 0, v___x_683_);
lean_closure_set(v___f_684_, 1, v_pre_669_);
lean_closure_set(v___f_684_, 2, v_e_671_);
lean_closure_set(v___f_684_, 3, v_post_670_);
v___x_685_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_684_, v_a_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___f_687_; lean_object* v___x_688_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_n(v_a_686_, 2);
lean_dec_ref_known(v___x_685_, 1);
lean_inc(v_a_672_);
v___f_687_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_687_, 0, v_a_672_);
lean_closure_set(v___f_687_, 1, v_e_671_);
lean_closure_set(v___f_687_, 2, v_a_686_);
v___x_688_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_687_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v___x_688_, 0);
lean_dec(v_unused_696_);
v___x_690_ = v___x_688_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_dec(v___x_688_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v_a_686_);
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_686_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_a_686_);
v_a_697_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_688_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_688_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_dec_ref(v_e_671_);
return v___x_685_;
}
}
else
{
lean_object* v_val_705_; lean_object* v___x_707_; 
lean_dec_ref(v_e_671_);
lean_dec_ref(v_post_670_);
lean_dec_ref(v_pre_669_);
v_val_705_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v___x_682_, 1);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v_val_705_);
v___x_707_ = v___x_680_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_val_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v_e_671_);
lean_dec_ref(v_post_670_);
lean_dec_ref(v_pre_669_);
v_a_710_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_677_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_677_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_718_, lean_object* v_post_719_, lean_object* v_e_720_, lean_object* v_a_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
lean_inc_ref(v_post_719_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc_ref(v_e_720_);
v___x_725_ = lean_apply_4(v_post_719_, v_e_720_, v___y_722_, v___y_723_, lean_box(0));
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_744_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_744_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_744_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_744_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
switch(lean_obj_tag(v_a_726_))
{
case 0:
{
lean_object* v_e_730_; lean_object* v___x_732_; 
lean_dec_ref(v_e_720_);
lean_dec_ref(v_post_719_);
lean_dec_ref(v_pre_718_);
v_e_730_ = lean_ctor_get(v_a_726_, 0);
lean_inc_ref(v_e_730_);
lean_dec_ref_known(v_a_726_, 1);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_e_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_e_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
case 1:
{
lean_object* v_e_734_; lean_object* v___x_735_; 
lean_del_object(v___x_728_);
lean_dec_ref(v_e_720_);
v_e_734_ = lean_ctor_get(v_a_726_, 0);
lean_inc_ref(v_e_734_);
lean_dec_ref_known(v_a_726_, 1);
v___x_735_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_718_, v_post_719_, v_e_734_, v_a_721_, v___y_722_, v___y_723_);
return v___x_735_;
}
default: 
{
lean_object* v_e_x3f_736_; 
lean_dec_ref(v_post_719_);
lean_dec_ref(v_pre_718_);
v_e_x3f_736_ = lean_ctor_get(v_a_726_, 0);
lean_inc(v_e_x3f_736_);
lean_dec_ref_known(v_a_726_, 1);
if (lean_obj_tag(v_e_x3f_736_) == 0)
{
lean_object* v___x_738_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_e_720_);
v___x_738_ = v___x_728_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_e_720_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
else
{
lean_object* v_val_740_; lean_object* v___x_742_; 
lean_dec_ref(v_e_720_);
v_val_740_ = lean_ctor_get(v_e_x3f_736_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v_e_x3f_736_, 1);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v_val_740_);
v___x_742_ = v___x_728_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_val_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_e_720_);
lean_dec_ref(v_post_719_);
lean_dec_ref(v_pre_718_);
v_a_745_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_725_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_725_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_753_, lean_object* v_post_754_, lean_object* v_e_755_, lean_object* v_a_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_753_, v_post_754_, v_e_755_, v_a_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v_a_756_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_761_, lean_object* v_post_762_, lean_object* v_sz_763_, lean_object* v_i_764_, lean_object* v_bs_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
size_t v_sz_boxed_770_; size_t v_i_boxed_771_; lean_object* v_res_772_; 
v_sz_boxed_770_ = lean_unbox_usize(v_sz_763_);
lean_dec(v_sz_763_);
v_i_boxed_771_ = lean_unbox_usize(v_i_764_);
lean_dec(v_i_764_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_761_, v_post_762_, v_sz_boxed_770_, v_i_boxed_771_, v_bs_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_773_, lean_object* v_post_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_773_, v_post_774_, v_x_775_, v_x_776_, v_x_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_783_, lean_object* v_post_784_, lean_object* v_e_785_, lean_object* v_a_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_783_, v_post_784_, v_e_785_, v_a_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v_a_786_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_791_, lean_object* v_x_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_apply_1(v_x_792_, lean_box(0));
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_798_, lean_object* v_x_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_798_, v_x_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
return v_res_803_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v_cellCount_804_; lean_object* v___x_805_; 
v_cellCount_804_ = lean_unsigned_to_nat(16u);
v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v_cellCount_806_; lean_object* v___x_807_; 
v_cellCount_806_ = lean_unsigned_to_nat(16u);
v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_806_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_808_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_809_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
lean_ctor_set(v___x_811_, 2, v___x_808_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__3(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_813_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_813_, 0, lean_box(0));
lean_closure_set(v___x_813_, 1, lean_box(0));
lean_closure_set(v___x_813_, 2, v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_814_, lean_object* v_pre_815_, lean_object* v_post_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_a_822_; lean_object* v___x_823_; 
v___x_820_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__3, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__3_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__3);
v___x_821_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_820_, v___y_817_, v___y_818_);
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref(v___x_821_);
v___x_823_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_815_, v_post_816_, v_input_814_, v_a_822_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_825_, 0, lean_box(0));
lean_closure_set(v___x_825_, 1, lean_box(0));
lean_closure_set(v___x_825_, 2, v_a_822_);
v___x_826_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_825_, v___y_817_, v___y_818_);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v___x_826_, 0);
lean_dec(v_unused_834_);
v___x_828_ = v___x_826_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_dec(v___x_826_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_a_824_);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_824_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
lean_dec(v_a_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_835_, lean_object* v_pre_836_, lean_object* v_post_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_835_, v_pre_836_, v_post_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___x_850_; 
v___f_848_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_849_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_850_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_844_, v___f_848_, v___f_849_, v_a_845_, v_a_846_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_elimOptParam(v_type_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_856_, lean_object* v_m_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_857_, v_a_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_860_, lean_object* v_m_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_860_, v_m_861_, v_a_862_);
lean_dec_ref(v_a_862_);
lean_dec_ref(v_m_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_864_, lean_object* v_ref_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_865_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_870_, lean_object* v_ref_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_870_, v_ref_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_886_, lean_object* v_x_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_887_, v___y_888_, v___y_889_, v___y_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_893_, lean_object* v_x_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_893_, v_x_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_900_, lean_object* v_m_901_, lean_object* v_query_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_901_, v_query_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b2_904_, lean_object* v_m_905_, lean_object* v_query_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(v_00_u03b2_904_, v_m_905_, v_query_906_);
lean_dec_ref(v_query_906_);
lean_dec_ref(v_m_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7(lean_object* v_00_u03b2_908_, lean_object* v_m_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___redArg(v_m_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b2_911_, lean_object* v_m_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7(v_00_u03b2_911_, v_m_912_);
lean_dec_ref(v_m_912_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_914_, lean_object* v_m_915_, lean_object* v_query_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_m_915_, v_query_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_918_, lean_object* v_m_919_, lean_object* v_query_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_918_, v_m_919_, v_query_920_);
lean_dec_ref(v_query_920_);
lean_dec_ref(v_m_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_922_, lean_object* v_m_923_, lean_object* v_query_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_m_923_, v_query_924_, v_x_925_, v_x_926_, v_x_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_930_, lean_object* v_m_931_, lean_object* v_query_932_, lean_object* v_x_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_930_, v_m_931_, v_query_932_, v_x_933_, v_x_934_, v_x_935_, v_x_936_);
lean_dec_ref(v_query_932_);
lean_dec_ref(v_m_931_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12(lean_object* v_00_u03b2_938_, lean_object* v_init_939_, lean_object* v_b_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12___redArg(v_init_939_, v_b_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12___boxed(lean_object* v_00_u03b2_942_, lean_object* v_init_943_, lean_object* v_b_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12(v_00_u03b2_942_, v_init_943_, v_b_944_);
lean_dec_ref(v_b_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_946_, lean_object* v_b_947_, lean_object* v_acc_948_, lean_object* v_i_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_947_, v_acc_948_, v_i_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13___boxed(lean_object* v_00_u03b2_951_, lean_object* v_b_952_, lean_object* v_acc_953_, lean_object* v_i_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__7_spec__12_spec__13(v_00_u03b2_951_, v_b_952_, v_acc_953_, v_i_954_);
lean_dec_ref(v_b_952_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_956_, lean_object* v_as_957_, size_t v_sz_958_, size_t v_i_959_, lean_object* v_b_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_a_967_; uint8_t v___x_971_; 
v___x_971_ = lean_usize_dec_lt(v_i_959_, v_sz_958_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; 
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v_b_960_);
return v___x_972_;
}
else
{
lean_object* v_snd_973_; lean_object* v_fst_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1052_; 
v_snd_973_ = lean_ctor_get(v_b_960_, 1);
v_fst_974_ = lean_ctor_get(v_b_960_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_b_960_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_976_ = v_b_960_;
v_isShared_977_ = v_isSharedCheck_1052_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_snd_973_);
lean_inc(v_fst_974_);
lean_dec(v_b_960_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1052_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_array_978_; lean_object* v_start_979_; lean_object* v_stop_980_; uint8_t v___x_981_; 
v_array_978_ = lean_ctor_get(v_snd_973_, 0);
v_start_979_ = lean_ctor_get(v_snd_973_, 1);
v_stop_980_ = lean_ctor_get(v_snd_973_, 2);
v___x_981_ = lean_nat_dec_lt(v_start_979_, v_stop_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_983_; 
if (v_isShared_977_ == 0)
{
v___x_983_ = v___x_976_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_fst_974_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_snd_973_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
else
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1048_; 
lean_inc(v_stop_980_);
lean_inc(v_start_979_);
lean_inc_ref(v_array_978_);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_snd_973_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; lean_object* v_unused_1050_; lean_object* v_unused_1051_; 
v_unused_1049_ = lean_ctor_get(v_snd_973_, 2);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_snd_973_, 1);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v_snd_973_, 0);
lean_dec(v_unused_1051_);
v___x_987_ = v_snd_973_;
v_isShared_988_ = v_isSharedCheck_1048_;
goto v_resetjp_986_;
}
else
{
lean_dec(v_snd_973_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1048_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_array_uget_borrowed(v_as_957_, v_i_959_);
lean_inc(v___y_964_);
lean_inc_ref(v___y_963_);
lean_inc(v___y_962_);
lean_inc_ref(v___y_961_);
lean_inc(v_a_989_);
v___x_990_ = lean_infer_type(v_a_989_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_array_fget(v_array_978_, v_start_979_);
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_nat_add(v_start_979_, v___x_993_);
lean_dec(v_start_979_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v___x_994_);
v___x_996_ = v___x_987_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_array_978_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_stop_980_);
v___x_996_ = v_reuseFailAlloc_1039_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
if (v_skipIfPropOrEq_956_ == 0)
{
lean_object* v___x_997_; 
lean_dec(v_a_991_);
lean_inc(v_a_989_);
v___x_997_ = l_Lean_Meta_mkEqHEq(v_a_989_, v___x_992_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = lean_array_push(v_fst_974_, v_a_998_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_996_);
lean_ctor_set(v___x_976_, 0, v___x_999_);
v___x_1001_ = v___x_976_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
v_a_967_ = v___x_1001_;
goto v___jp_966_;
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v___x_996_);
lean_del_object(v___x_976_);
lean_dec(v_fst_974_);
v_a_1003_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_997_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_997_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Meta_isProp(v_a_991_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; uint8_t v___x_1017_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1017_ = lean_unbox(v_a_1012_);
lean_dec(v_a_1012_);
if (v___x_1017_ == 0)
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_expr_eqv(v_a_989_, v___x_992_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
lean_del_object(v___x_976_);
lean_inc(v_a_989_);
v___x_1019_ = l_Lean_Meta_mkEqHEq(v_a_989_, v___x_992_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = lean_array_push(v_fst_974_, v_a_1020_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_996_);
v_a_967_ = v___x_1022_;
goto v___jp_966_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v___x_996_);
lean_dec(v_fst_974_);
v_a_1023_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1019_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1019_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_dec(v___x_992_);
goto v___jp_1013_;
}
}
else
{
lean_dec(v___x_992_);
goto v___jp_1013_;
}
v___jp_1013_:
{
lean_object* v___x_1015_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_996_);
v___x_1015_ = v___x_976_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_fst_974_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_996_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
v_a_967_ = v___x_1015_;
goto v___jp_966_;
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v___x_996_);
lean_dec(v___x_992_);
lean_del_object(v___x_976_);
lean_dec(v_fst_974_);
v_a_1031_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1011_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1011_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_del_object(v___x_987_);
lean_dec(v_stop_980_);
lean_dec(v_start_979_);
lean_dec_ref(v_array_978_);
lean_del_object(v___x_976_);
lean_dec(v_fst_974_);
v_a_1040_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_990_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_990_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
}
}
v___jp_966_:
{
size_t v___x_968_; size_t v___x_969_; 
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_add(v_i_959_, v___x_968_);
v_i_959_ = v___x_969_;
v_b_960_ = v_a_967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_1053_, lean_object* v_as_1054_, lean_object* v_sz_1055_, lean_object* v_i_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_1063_; size_t v_sz_boxed_1064_; size_t v_i_boxed_1065_; lean_object* v_res_1066_; 
v_skipIfPropOrEq_boxed_1063_ = lean_unbox(v_skipIfPropOrEq_1053_);
v_sz_boxed_1064_ = lean_unbox_usize(v_sz_1055_);
lean_dec(v_sz_1055_);
v_i_boxed_1065_ = lean_unbox_usize(v_i_1056_);
lean_dec(v_i_1056_);
v_res_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_1063_, v_as_1054_, v_sz_boxed_1064_, v_i_boxed_1065_, v_b_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec_ref(v_as_1054_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_1069_, lean_object* v_args2_1070_, uint8_t v_skipIfPropOrEq_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v_eqs_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; size_t v_sz_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v___x_1077_ = lean_unsigned_to_nat(0u);
v_eqs_1078_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1079_ = lean_array_get_size(v_args2_1070_);
v___x_1080_ = l_Array_toSubarray___redArg(v_args2_1070_, v___x_1077_, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_eqs_1078_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v_sz_1082_ = lean_array_size(v_args1_1069_);
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_1071_, v_args1_1069_, v_sz_1082_, v___x_1083_, v___x_1081_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_fst_1089_; lean_object* v___x_1091_; 
v_fst_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_fst_1089_);
lean_dec(v_a_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_fst_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_fst_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
v_a_1094_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1084_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1084_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_1102_, lean_object* v_args2_1103_, lean_object* v_skipIfPropOrEq_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_1110_; lean_object* v_res_1111_; 
v_skipIfPropOrEq_boxed_1110_ = lean_unbox(v_skipIfPropOrEq_1104_);
v_res_1111_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1102_, v_args2_1103_, v_skipIfPropOrEq_boxed_1110_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec_ref(v_args1_1102_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
lean_inc(v___y_1115_);
lean_inc_ref(v___y_1114_);
v___x_1119_ = lean_apply_6(v_k_1112_, v_b_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, lean_box(0));
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_1120_, v_b_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1128_, uint8_t v_bi_1129_, lean_object* v_type_1130_, lean_object* v_k_1131_, uint8_t v_kind_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___f_1138_; lean_object* v___x_1139_; 
v___f_1138_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1138_, 0, v_k_1131_);
v___x_1139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1128_, v_bi_1129_, v_type_1130_, v___f_1138_, v_kind_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v_a_1148_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1139_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1139_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1156_, lean_object* v_bi_1157_, lean_object* v_type_1158_, lean_object* v_k_1159_, lean_object* v_kind_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_bi_boxed_1166_; uint8_t v_kind_boxed_1167_; lean_object* v_res_1168_; 
v_bi_boxed_1166_ = lean_unbox(v_bi_1157_);
v_kind_boxed_1167_ = lean_unbox(v_kind_1160_);
v_res_1168_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1156_, v_bi_boxed_1166_, v_type_1158_, v_k_1159_, v_kind_boxed_1167_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1169_, lean_object* v_name_1170_, uint8_t v_bi_1171_, lean_object* v_type_1172_, lean_object* v_k_1173_, uint8_t v_kind_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1170_, v_bi_1171_, v_type_1172_, v_k_1173_, v_kind_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_name_1182_, lean_object* v_bi_1183_, lean_object* v_type_1184_, lean_object* v_k_1185_, lean_object* v_kind_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_bi_boxed_1192_; uint8_t v_kind_boxed_1193_; lean_object* v_res_1194_; 
v_bi_boxed_1192_ = lean_unbox(v_bi_1183_);
v_kind_boxed_1193_ = lean_unbox(v_kind_1186_);
v_res_1194_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1181_, v_name_1182_, v_bi_boxed_1192_, v_type_1184_, v_k_1185_, v_kind_boxed_1193_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_env_1202_; lean_object* v___x_1203_; lean_object* v_mctx_1204_; lean_object* v_lctx_1205_; lean_object* v_options_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1201_ = lean_st_ref_get(v___y_1199_);
v_env_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_env_1202_);
lean_dec(v___x_1201_);
v___x_1203_ = lean_st_ref_get(v___y_1197_);
v_mctx_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc_ref(v_mctx_1204_);
lean_dec(v___x_1203_);
v_lctx_1205_ = lean_ctor_get(v___y_1196_, 2);
v_options_1206_ = lean_ctor_get(v___y_1198_, 2);
lean_inc_ref(v_options_1206_);
lean_inc_ref(v_lctx_1205_);
v___x_1207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1207_, 0, v_env_1202_);
lean_ctor_set(v___x_1207_, 1, v_mctx_1204_);
lean_ctor_set(v___x_1207_, 2, v_lctx_1205_);
lean_ctor_set(v___x_1207_, 3, v_options_1206_);
v___x_1208_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v_msgData_1195_);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_ref_1223_; lean_object* v___x_1224_; lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1233_; 
v_ref_1223_ = lean_ctor_get(v___y_1220_, 5);
v___x_1224_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
lean_inc(v_ref_1223_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_ref_1223_);
lean_ctor_set(v___x_1229_, 1, v_a_1225_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 1);
lean_ctor_set(v___x_1227_, 0, v___x_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1241_, lean_object* v_body_1242_, lean_object* v_args2_1243_, lean_object* v_args2New_1244_, lean_object* v_ctorVal_1245_, lean_object* v_useEq_1246_, lean_object* v_args1_1247_, lean_object* v_resultType_1248_, lean_object* v_k_1249_, lean_object* v_arg2_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v_useEq_boxed_1256_; lean_object* v_res_1257_; 
v_useEq_boxed_1256_ = lean_unbox(v_useEq_1246_);
v_res_1257_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1241_, v_body_1242_, v_args2_1243_, v_args2New_1244_, v_ctorVal_1245_, v_useEq_boxed_1256_, v_args1_1247_, v_resultType_1248_, v_k_1249_, v_arg2_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v_body_1242_);
lean_dec(v_i_1241_);
return v_res_1257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1264_, uint8_t v_useEq_1265_, lean_object* v_args1_1266_, lean_object* v_resultType_1267_, lean_object* v_k_1268_, lean_object* v_i_1269_, lean_object* v_type_1270_, lean_object* v_args2_1271_, lean_object* v_args2New_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = lean_array_get_size(v_args1_1266_);
v___x_1279_ = lean_nat_dec_lt(v_i_1269_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec_ref(v_type_1270_);
lean_dec(v_i_1269_);
lean_dec_ref(v_resultType_1267_);
lean_dec_ref(v_args1_1266_);
lean_dec_ref(v_ctorVal_1264_);
lean_inc(v_a_1276_);
lean_inc_ref(v_a_1275_);
lean_inc(v_a_1274_);
lean_inc_ref(v_a_1273_);
v___x_1280_ = lean_apply_7(v_k_1268_, v_args2_1271_, v_args2New_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, lean_box(0));
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; 
lean_inc(v_a_1276_);
lean_inc_ref(v_a_1275_);
lean_inc(v_a_1274_);
lean_inc_ref(v_a_1273_);
v___x_1281_ = lean_whnf(v_type_1270_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
if (lean_obj_tag(v_a_1282_) == 7)
{
lean_object* v_binderName_1283_; lean_object* v_binderType_1284_; lean_object* v_body_1285_; lean_object* v_lctx_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_binderName_1283_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_binderName_1283_);
v_binderType_1284_ = lean_ctor_get(v_a_1282_, 1);
lean_inc_ref(v_binderType_1284_);
v_body_1285_ = lean_ctor_get(v_a_1282_, 2);
lean_inc_ref(v_body_1285_);
lean_dec_ref_known(v_a_1282_, 3);
v_lctx_1286_ = lean_ctor_get(v_a_1273_, 2);
v___x_1287_ = lean_array_fget_borrowed(v_args1_1266_, v_i_1269_);
lean_inc(v___x_1287_);
lean_inc_ref(v_lctx_1286_);
v___x_1288_ = l_Lean_Meta_occursOrInType(v_lctx_1286_, v___x_1287_, v_resultType_1267_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___f_1290_; uint8_t v___y_1292_; 
v___x_1289_ = lean_box(v_useEq_1265_);
v___f_1290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1290_, 0, v_i_1269_);
lean_closure_set(v___f_1290_, 1, v_body_1285_);
lean_closure_set(v___f_1290_, 2, v_args2_1271_);
lean_closure_set(v___f_1290_, 3, v_args2New_1272_);
lean_closure_set(v___f_1290_, 4, v_ctorVal_1264_);
lean_closure_set(v___f_1290_, 5, v___x_1289_);
lean_closure_set(v___f_1290_, 6, v_args1_1266_);
lean_closure_set(v___f_1290_, 7, v_resultType_1267_);
lean_closure_set(v___f_1290_, 8, v_k_1268_);
if (v_useEq_1265_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = 1;
v___y_1292_ = v___x_1295_;
goto v___jp_1291_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = 0;
v___y_1292_ = v___x_1296_;
goto v___jp_1291_;
}
v___jp_1291_:
{
uint8_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = 0;
v___x_1294_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1283_, v___y_1292_, v_binderType_1284_, v___f_1290_, v___x_1293_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
return v___x_1294_;
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v_binderType_1284_);
lean_dec(v_binderName_1283_);
v___x_1297_ = lean_unsigned_to_nat(1u);
v___x_1298_ = lean_nat_add(v_i_1269_, v___x_1297_);
lean_dec(v_i_1269_);
v___x_1299_ = lean_expr_instantiate1(v_body_1285_, v___x_1287_);
lean_dec_ref(v_body_1285_);
lean_inc(v___x_1287_);
v___x_1300_ = lean_array_push(v_args2_1271_, v___x_1287_);
v_i_1269_ = v___x_1298_;
v_type_1270_ = v___x_1299_;
v_args2_1271_ = v___x_1300_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1302_; lean_object* v_name_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_dec(v_a_1282_);
lean_dec_ref(v_args2New_1272_);
lean_dec_ref(v_args2_1271_);
lean_dec(v_i_1269_);
lean_dec_ref(v_k_1268_);
lean_dec_ref(v_resultType_1267_);
lean_dec_ref(v_args1_1266_);
v_toConstantVal_1302_ = lean_ctor_get(v_ctorVal_1264_, 0);
lean_inc_ref(v_toConstantVal_1302_);
lean_dec_ref(v_ctorVal_1264_);
v_name_1303_ = lean_ctor_get(v_toConstantVal_1302_, 0);
lean_inc(v_name_1303_);
lean_dec_ref(v_toConstantVal_1302_);
v___x_1304_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1305_ = l_Lean_MessageData_ofName(v_name_1303_);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1308_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
return v___x_1309_;
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v_args2New_1272_);
lean_dec_ref(v_args2_1271_);
lean_dec(v_i_1269_);
lean_dec_ref(v_k_1268_);
lean_dec_ref(v_resultType_1267_);
lean_dec_ref(v_args1_1266_);
lean_dec_ref(v_ctorVal_1264_);
v_a_1310_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1281_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1281_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1318_, lean_object* v_body_1319_, lean_object* v_args2_1320_, lean_object* v_args2New_1321_, lean_object* v_ctorVal_1322_, uint8_t v_useEq_1323_, lean_object* v_args1_1324_, lean_object* v_resultType_1325_, lean_object* v_k_1326_, lean_object* v_arg2_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = lean_nat_add(v_i_1318_, v___x_1333_);
v___x_1335_ = lean_expr_instantiate1(v_body_1319_, v_arg2_1327_);
lean_inc_ref(v_arg2_1327_);
v___x_1336_ = lean_array_push(v_args2_1320_, v_arg2_1327_);
v___x_1337_ = lean_array_push(v_args2New_1321_, v_arg2_1327_);
v___x_1338_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1322_, v_useEq_1323_, v_args1_1324_, v_resultType_1325_, v_k_1326_, v___x_1334_, v___x_1335_, v___x_1336_, v___x_1337_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1339_, lean_object* v_useEq_1340_, lean_object* v_args1_1341_, lean_object* v_resultType_1342_, lean_object* v_k_1343_, lean_object* v_i_1344_, lean_object* v_type_1345_, lean_object* v_args2_1346_, lean_object* v_args2New_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
uint8_t v_useEq_boxed_1353_; lean_object* v_res_1354_; 
v_useEq_boxed_1353_ = lean_unbox(v_useEq_1340_);
v_res_1354_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1339_, v_useEq_boxed_1353_, v_args1_1341_, v_resultType_1342_, v_k_1343_, v_i_1344_, v_type_1345_, v_args2_1346_, v_args2New_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1355_, lean_object* v_msg_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_msg_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1363_, v_msg_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1371_, lean_object* v_h__1_1372_, lean_object* v_h__2_1373_){
_start:
{
if (lean_obj_tag(v_____x_1371_) == 7)
{
lean_object* v_binderName_1374_; lean_object* v_binderType_1375_; lean_object* v_body_1376_; uint8_t v_binderInfo_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec(v_h__2_1373_);
v_binderName_1374_ = lean_ctor_get(v_____x_1371_, 0);
lean_inc(v_binderName_1374_);
v_binderType_1375_ = lean_ctor_get(v_____x_1371_, 1);
lean_inc_ref(v_binderType_1375_);
v_body_1376_ = lean_ctor_get(v_____x_1371_, 2);
lean_inc_ref(v_body_1376_);
v_binderInfo_1377_ = lean_ctor_get_uint8(v_____x_1371_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1371_, 3);
v___x_1378_ = lean_box(v_binderInfo_1377_);
v___x_1379_ = lean_apply_4(v_h__1_1372_, v_binderName_1374_, v_binderType_1375_, v_body_1376_, v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v___x_1380_; 
lean_dec(v_h__1_1372_);
v___x_1380_ = lean_apply_2(v_h__2_1373_, v_____x_1371_, lean_box(0));
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1381_, lean_object* v_____x_1382_, lean_object* v_h__1_1383_, lean_object* v_h__2_1384_){
_start:
{
if (lean_obj_tag(v_____x_1382_) == 7)
{
lean_object* v_binderName_1385_; lean_object* v_binderType_1386_; lean_object* v_body_1387_; uint8_t v_binderInfo_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v_h__2_1384_);
v_binderName_1385_ = lean_ctor_get(v_____x_1382_, 0);
lean_inc(v_binderName_1385_);
v_binderType_1386_ = lean_ctor_get(v_____x_1382_, 1);
lean_inc_ref(v_binderType_1386_);
v_body_1387_ = lean_ctor_get(v_____x_1382_, 2);
lean_inc_ref(v_body_1387_);
v_binderInfo_1388_ = lean_ctor_get_uint8(v_____x_1382_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1382_, 3);
v___x_1389_ = lean_box(v_binderInfo_1388_);
v___x_1390_ = lean_apply_4(v_h__1_1383_, v_binderName_1385_, v_binderType_1386_, v_body_1387_, v___x_1389_);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; 
lean_dec(v_h__1_1383_);
v___x_1391_ = lean_apply_2(v_h__2_1384_, v_____x_1382_, lean_box(0));
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1392_, lean_object* v_b_1393_, lean_object* v_c_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
v___x_1400_ = lean_apply_7(v_k_1392_, v_b_1393_, v_c_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, lean_box(0));
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1401_, lean_object* v_b_1402_, lean_object* v_c_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1401_, v_b_1402_, v_c_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1410_, lean_object* v_k_1411_, uint8_t v_cleanupAnnotations_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v___f_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___f_1418_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1418_, 0, v_k_1411_);
v___x_1419_ = 0;
v___x_1420_ = lean_box(0);
v___x_1421_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1419_, v___x_1420_, v_type_1410_, v___f_1418_, v_cleanupAnnotations_1412_, v___x_1419_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
v_a_1430_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1421_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1421_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1438_, lean_object* v_k_1439_, lean_object* v_cleanupAnnotations_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1446_; lean_object* v_res_1447_; 
v_cleanupAnnotations_boxed_1446_ = lean_unbox(v_cleanupAnnotations_1440_);
v_res_1447_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1438_, v_k_1439_, v_cleanupAnnotations_boxed_1446_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1448_, lean_object* v_type_1449_, lean_object* v_k_1450_, uint8_t v_cleanupAnnotations_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1449_, v_k_1450_, v_cleanupAnnotations_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1458_, lean_object* v_type_1459_, lean_object* v_k_1460_, lean_object* v_cleanupAnnotations_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1467_; lean_object* v_res_1468_; 
v_cleanupAnnotations_boxed_1467_ = lean_unbox(v_cleanupAnnotations_1461_);
v_res_1468_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1458_, v_type_1459_, v_k_1460_, v_cleanupAnnotations_boxed_1467_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1469_, lean_object* v_maxFVars_x3f_1470_, lean_object* v_k_1471_, uint8_t v_cleanupAnnotations_1472_, uint8_t v_whnfType_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___f_1479_; lean_object* v___x_1480_; 
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1479_, 0, v_k_1471_);
v___x_1480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1469_, v_maxFVars_x3f_1470_, v___f_1479_, v_cleanupAnnotations_1472_, v_whnfType_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_a_1489_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1480_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1480_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1497_, lean_object* v_maxFVars_x3f_1498_, lean_object* v_k_1499_, lean_object* v_cleanupAnnotations_1500_, lean_object* v_whnfType_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1507_; uint8_t v_whnfType_boxed_1508_; lean_object* v_res_1509_; 
v_cleanupAnnotations_boxed_1507_ = lean_unbox(v_cleanupAnnotations_1500_);
v_whnfType_boxed_1508_ = lean_unbox(v_whnfType_1501_);
v_res_1509_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1497_, v_maxFVars_x3f_1498_, v_k_1499_, v_cleanupAnnotations_boxed_1507_, v_whnfType_boxed_1508_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1510_, lean_object* v_type_1511_, lean_object* v_maxFVars_x3f_1512_, lean_object* v_k_1513_, uint8_t v_cleanupAnnotations_1514_, uint8_t v_whnfType_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1511_, v_maxFVars_x3f_1512_, v_k_1513_, v_cleanupAnnotations_1514_, v_whnfType_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_type_1523_, lean_object* v_maxFVars_x3f_1524_, lean_object* v_k_1525_, lean_object* v_cleanupAnnotations_1526_, lean_object* v_whnfType_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1533_; uint8_t v_whnfType_boxed_1534_; lean_object* v_res_1535_; 
v_cleanupAnnotations_boxed_1533_ = lean_unbox(v_cleanupAnnotations_1526_);
v_whnfType_boxed_1534_ = lean_unbox(v_whnfType_1527_);
v_res_1535_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1522_, v_type_1523_, v_maxFVars_x3f_1524_, v_k_1525_, v_cleanupAnnotations_boxed_1533_, v_whnfType_boxed_1534_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1536_, lean_object* v_us_1537_, lean_object* v_params_1538_, lean_object* v_args1_1539_, uint8_t v_useEq_1540_, lean_object* v_args2_1541_, lean_object* v_args2New_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1548_ = l_Lean_mkConst(v_name_1536_, v_us_1537_);
v___x_1549_ = l_Lean_mkAppN(v___x_1548_, v_params_1538_);
lean_inc_ref(v___x_1549_);
v___x_1550_ = l_Lean_mkAppN(v___x_1549_, v_args1_1539_);
v___x_1551_ = l_Lean_mkAppN(v___x_1549_, v_args2_1541_);
v___x_1552_ = l_Lean_Meta_mkEq(v___x_1550_, v___x_1551_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; uint8_t v___x_1554_; lean_object* v_result_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___x_1601_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = 1;
v___x_1601_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1539_, v_args2_1541_, v___x_1554_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1633_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1633_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1633_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1602_);
if (lean_obj_tag(v___x_1606_) == 1)
{
lean_del_object(v___x_1604_);
if (v_useEq_1540_ == 0)
{
lean_object* v_val_1607_; lean_object* v___x_1608_; 
v_val_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_val_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1608_ = l_Lean_mkArrow(v_a_1553_, v_val_1607_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v_result_1556_ = v_a_1609_;
v___y_1557_ = v___y_1543_;
v___y_1558_ = v___y_1544_;
v___y_1559_ = v___y_1545_;
v___y_1560_ = v___y_1546_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_a_1610_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1608_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1608_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v_val_1618_; lean_object* v___x_1619_; 
v_val_1618_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_val_1618_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1619_ = l_Lean_Meta_mkEq(v_a_1553_, v_val_1618_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v_result_1556_ = v_a_1620_;
v___y_1557_ = v___y_1543_;
v___y_1558_ = v___y_1544_;
v___y_1559_ = v___y_1545_;
v___y_1560_ = v___y_1546_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
v_a_1621_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1619_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1619_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_dec(v___x_1606_);
lean_dec(v_a_1553_);
v___x_1629_ = lean_box(0);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1629_);
v___x_1631_ = v___x_1604_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec(v_a_1553_);
v_a_1634_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1601_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1601_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
v___jp_1555_:
{
uint8_t v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = 0;
v___x_1562_ = 1;
v___x_1563_ = l_Lean_Meta_mkForallFVars(v_args2New_1542_, v_result_1556_, v___x_1561_, v___x_1554_, v___x_1554_, v___x_1562_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = l_Lean_Meta_mkForallFVars(v_args1_1539_, v_a_1564_, v___x_1561_, v___x_1554_, v___x_1554_, v___x_1562_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = l_Lean_Meta_mkForallFVars(v_params_1538_, v_a_1566_, v___x_1561_, v___x_1554_, v___x_1554_, v___x_1562_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1576_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_a_1568_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1572_);
v___x_1574_ = v___x_1570_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_a_1577_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1567_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1567_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1585_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1565_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1565_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1563_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1563_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v_args2_1541_);
v_a_1642_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1552_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1552_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1650_, lean_object* v_us_1651_, lean_object* v_params_1652_, lean_object* v_args1_1653_, lean_object* v_useEq_1654_, lean_object* v_args2_1655_, lean_object* v_args2New_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v_useEq_boxed_1662_; lean_object* v_res_1663_; 
v_useEq_boxed_1662_ = lean_unbox(v_useEq_1654_);
v_res_1663_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1650_, v_us_1651_, v_params_1652_, v_args1_1653_, v_useEq_boxed_1662_, v_args2_1655_, v_args2New_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec_ref(v_args2New_1656_);
lean_dec_ref(v_args1_1653_);
lean_dec_ref(v_params_1652_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1664_, size_t v_i_1665_, lean_object* v_bs_1666_){
_start:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_usize_dec_lt(v_i_1665_, v_sz_1664_);
if (v___x_1667_ == 0)
{
return v_bs_1666_;
}
else
{
lean_object* v_v_1668_; lean_object* v___x_1669_; lean_object* v_bs_x27_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; size_t v___x_1675_; size_t v___x_1676_; lean_object* v___x_1677_; 
v_v_1668_ = lean_array_uget(v_bs_1666_, v_i_1665_);
v___x_1669_ = lean_unsigned_to_nat(0u);
v_bs_x27_1670_ = lean_array_uset(v_bs_1666_, v_i_1665_, v___x_1669_);
v___x_1671_ = l_Lean_Expr_fvarId_x21(v_v_1668_);
lean_dec(v_v_1668_);
v___x_1672_ = 1;
v___x_1673_ = lean_box(v___x_1672_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1671_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = ((size_t)1ULL);
v___x_1676_ = lean_usize_add(v_i_1665_, v___x_1675_);
v___x_1677_ = lean_array_uset(v_bs_x27_1670_, v_i_1665_, v___x_1674_);
v_i_1665_ = v___x_1676_;
v_bs_1666_ = v___x_1677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1679_, lean_object* v_i_1680_, lean_object* v_bs_1681_){
_start:
{
size_t v_sz_boxed_1682_; size_t v_i_boxed_1683_; lean_object* v_res_1684_; 
v_sz_boxed_1682_ = lean_unbox_usize(v_sz_1679_);
lean_dec(v_sz_1679_);
v_i_boxed_1683_ = lean_unbox_usize(v_i_1680_);
lean_dec(v_i_1680_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1682_, v_i_boxed_1683_, v_bs_1681_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1685_, lean_object* v_k_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1685_, v_k_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v_a_1701_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1692_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1692_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1709_, lean_object* v_k_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1709_, v_k_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v_bs_1709_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1717_, lean_object* v_k_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
size_t v_sz_1724_; size_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_sz_1724_ = lean_array_size(v_bs_1717_);
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1724_, v___x_1725_, v_bs_1717_);
v___x_1727_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1726_, v_k_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec_ref(v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1728_, lean_object* v_k_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1728_, v_k_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1736_, lean_object* v_us_1737_, lean_object* v_params_1738_, uint8_t v_useEq_1739_, lean_object* v_ctorVal_1740_, lean_object* v_type_1741_, lean_object* v_args1_1742_, lean_object* v_resultType_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; lean_object* v___f_1750_; 
v___x_1749_ = lean_box(v_useEq_1739_);
lean_inc_ref(v_args1_1742_);
lean_inc_ref(v_params_1738_);
v___f_1750_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1750_, 0, v_name_1736_);
lean_closure_set(v___f_1750_, 1, v_us_1737_);
lean_closure_set(v___f_1750_, 2, v_params_1738_);
lean_closure_set(v___f_1750_, 3, v_args1_1742_);
lean_closure_set(v___f_1750_, 4, v___x_1749_);
if (v_useEq_1739_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1751_ = l_Array_append___redArg(v_params_1738_, v_args1_1742_);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1754_ = lean_box(v_useEq_1739_);
v___x_1755_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1755_, 0, v_ctorVal_1740_);
lean_closure_set(v___x_1755_, 1, v___x_1754_);
lean_closure_set(v___x_1755_, 2, v_args1_1742_);
lean_closure_set(v___x_1755_, 3, v_resultType_1743_);
lean_closure_set(v___x_1755_, 4, v___f_1750_);
lean_closure_set(v___x_1755_, 5, v___x_1752_);
lean_closure_set(v___x_1755_, 6, v_type_1741_);
lean_closure_set(v___x_1755_, 7, v___x_1753_);
lean_closure_set(v___x_1755_, 8, v___x_1753_);
v___x_1756_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1751_, v___x_1755_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec_ref(v_params_1738_);
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1759_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1740_, v_useEq_1739_, v_args1_1742_, v_resultType_1743_, v___f_1750_, v___x_1757_, v_type_1741_, v___x_1758_, v___x_1758_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1760_, lean_object* v_us_1761_, lean_object* v_params_1762_, lean_object* v_useEq_1763_, lean_object* v_ctorVal_1764_, lean_object* v_type_1765_, lean_object* v_args1_1766_, lean_object* v_resultType_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v_useEq_boxed_1773_; lean_object* v_res_1774_; 
v_useEq_boxed_1773_ = lean_unbox(v_useEq_1763_);
v_res_1774_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1760_, v_us_1761_, v_params_1762_, v_useEq_boxed_1773_, v_ctorVal_1764_, v_type_1765_, v_args1_1766_, v_resultType_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1775_, lean_object* v_us_1776_, uint8_t v_useEq_1777_, lean_object* v_ctorVal_1778_, lean_object* v_params_1779_, lean_object* v_type_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; lean_object* v___f_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; 
v___x_1786_ = lean_box(v_useEq_1777_);
lean_inc_ref(v_type_1780_);
v___f_1787_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1787_, 0, v_name_1775_);
lean_closure_set(v___f_1787_, 1, v_us_1776_);
lean_closure_set(v___f_1787_, 2, v_params_1779_);
lean_closure_set(v___f_1787_, 3, v___x_1786_);
lean_closure_set(v___f_1787_, 4, v_ctorVal_1778_);
lean_closure_set(v___f_1787_, 5, v_type_1780_);
v___x_1788_ = 0;
v___x_1789_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1780_, v___f_1787_, v___x_1788_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1790_, lean_object* v_us_1791_, lean_object* v_useEq_1792_, lean_object* v_ctorVal_1793_, lean_object* v_params_1794_, lean_object* v_type_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v_useEq_boxed_1801_; lean_object* v_res_1802_; 
v_useEq_boxed_1801_ = lean_unbox(v_useEq_1792_);
v_res_1802_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1790_, v_us_1791_, v_useEq_boxed_1801_, v_ctorVal_1793_, v_params_1794_, v_type_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
if (lean_obj_tag(v_a_1803_) == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = l_List_reverse___redArg(v_a_1804_);
return v___x_1805_;
}
else
{
lean_object* v_head_1806_; lean_object* v_tail_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1816_; 
v_head_1806_ = lean_ctor_get(v_a_1803_, 0);
v_tail_1807_ = lean_ctor_get(v_a_1803_, 1);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_a_1803_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1809_ = v_a_1803_;
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_tail_1807_);
lean_inc(v_head_1806_);
lean_dec(v_a_1803_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = l_Lean_mkLevelParam(v_head_1806_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v_a_1804_);
lean_ctor_set(v___x_1809_, 0, v___x_1811_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_a_1804_);
v___x_1813_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
v_a_1803_ = v_tail_1807_;
v_a_1804_ = v___x_1813_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1817_, uint8_t v_useEq_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_toConstantVal_1824_; lean_object* v_numParams_1825_; lean_object* v_name_1826_; lean_object* v_levelParams_1827_; lean_object* v_type_1828_; lean_object* v___x_1829_; 
v_toConstantVal_1824_ = lean_ctor_get(v_ctorVal_1817_, 0);
v_numParams_1825_ = lean_ctor_get(v_ctorVal_1817_, 3);
lean_inc(v_numParams_1825_);
v_name_1826_ = lean_ctor_get(v_toConstantVal_1824_, 0);
lean_inc(v_name_1826_);
v_levelParams_1827_ = lean_ctor_get(v_toConstantVal_1824_, 1);
v_type_1828_ = lean_ctor_get(v_toConstantVal_1824_, 2);
lean_inc_ref(v_type_1828_);
v___x_1829_ = l_Lean_Meta_elimOptParam(v_type_1828_, v_a_1821_, v_a_1822_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1831_; lean_object* v_us_1832_; lean_object* v___x_1833_; lean_object* v___f_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1831_ = lean_box(0);
lean_inc(v_levelParams_1827_);
v_us_1832_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1827_, v___x_1831_);
v___x_1833_ = lean_box(v_useEq_1818_);
v___f_1834_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1834_, 0, v_name_1826_);
lean_closure_set(v___f_1834_, 1, v_us_1832_);
lean_closure_set(v___f_1834_, 2, v___x_1833_);
lean_closure_set(v___f_1834_, 3, v_ctorVal_1817_);
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_numParams_1825_);
v___x_1836_ = 0;
v___x_1837_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1830_, v___x_1835_, v___f_1834_, v___x_1836_, v___x_1836_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
return v___x_1837_;
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_name_1826_);
lean_dec(v_numParams_1825_);
lean_dec_ref(v_ctorVal_1817_);
v_a_1838_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1829_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1829_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1846_, lean_object* v_useEq_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
uint8_t v_useEq_boxed_1853_; lean_object* v_res_1854_; 
v_useEq_boxed_1853_ = lean_unbox(v_useEq_1847_);
v_res_1854_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1846_, v_useEq_boxed_1853_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1855_, lean_object* v_bs_1856_, lean_object* v_k_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1856_, v_k_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1864_, lean_object* v_bs_1865_, lean_object* v_k_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1864_, v_bs_1865_, v_k_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec_ref(v_bs_1865_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1873_, lean_object* v_bs_1874_, lean_object* v_k_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1874_, v_k_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1882_, lean_object* v_bs_1883_, lean_object* v_k_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1882_, v_bs_1883_, v_k_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
uint8_t v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = 0;
v___x_1898_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1891_, v___x_1897_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
return v_res_1905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1908_ = l_Lean_stringToMessageData(v___x_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1911_ = l_Lean_stringToMessageData(v___x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1913_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1914_ = l_Lean_MessageData_ofName(v_ctorName_1912_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1918_, lean_object* v_mvarId_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1925_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1918_);
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_mvarId_1919_);
v___x_1927_ = l_Lean_indentD(v___x_1926_);
v___x_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1925_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1928_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1930_, lean_object* v_mvarId_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1930_, v_mvarId_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1938_, lean_object* v_ctorName_1939_, lean_object* v_mvarId_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1939_, v_mvarId_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1947_, lean_object* v_ctorName_1948_, lean_object* v_mvarId_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1947_, v_ctorName_1948_, v_mvarId_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1956_, lean_object* v_as_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
if (lean_obj_tag(v_as_1957_) == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec(v_ctorName_1956_);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
else
{
lean_object* v_head_1965_; lean_object* v_tail_1966_; lean_object* v___x_1967_; 
v_head_1965_ = lean_ctor_get(v_as_1957_, 0);
lean_inc_n(v_head_1965_, 2);
v_tail_1966_ = lean_ctor_get(v_as_1957_, 1);
lean_inc(v_tail_1966_);
lean_dec_ref_known(v_as_1957_, 2);
v___x_1967_ = l_Lean_MVarId_assumptionCore(v_head_1965_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; uint8_t v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = lean_unbox(v_a_1968_);
lean_dec(v_a_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec(v_tail_1966_);
v___x_1970_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1956_, v_head_1965_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
return v___x_1970_;
}
else
{
lean_dec(v_head_1965_);
v_as_1957_ = v_tail_1966_;
goto _start;
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_tail_1966_);
lean_dec(v_head_1965_);
lean_dec(v_ctorName_1956_);
v_a_1972_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1967_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1967_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1980_, lean_object* v_as_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1980_, v_as_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1988_, lean_object* v_ctorName_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_MVarId_splitAndCore(v_mvarId_1988_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1989_, v_a_1996_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
return v___x_1997_;
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_dec(v_ctorName_1989_);
v_a_1998_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1995_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1995_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_2006_, lean_object* v_ctorName_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2006_, v_ctorName_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___f_2021_; lean_object* v___x_1015__overap_2022_; lean_object* v___x_2023_; 
v___f_2021_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_1015__overap_2022_ = lean_panic_fn_borrowed(v___f_2021_, v_msg_2015_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v___y_2017_);
lean_inc_ref(v___y_2016_);
v___x_2023_ = lean_apply_5(v___x_1015__overap_2022_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, lean_box(0));
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2030_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2031_; double v___x_2032_; 
v___x_2031_ = lean_unsigned_to_nat(0u);
v___x_2032_ = lean_float_of_nat(v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_2036_, lean_object* v_msg_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_ref_2043_; lean_object* v___x_2044_; lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2089_; 
v_ref_2043_ = lean_ctor_get(v___y_2040_, 5);
v___x_2044_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2089_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2089_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v_traceState_2050_; lean_object* v_env_2051_; lean_object* v_nextMacroScope_2052_; lean_object* v_ngen_2053_; lean_object* v_auxDeclNGen_2054_; lean_object* v_cache_2055_; lean_object* v_messages_2056_; lean_object* v_infoState_2057_; lean_object* v_snapshotTasks_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2088_; 
v___x_2049_ = lean_st_ref_take(v___y_2041_);
v_traceState_2050_ = lean_ctor_get(v___x_2049_, 4);
v_env_2051_ = lean_ctor_get(v___x_2049_, 0);
v_nextMacroScope_2052_ = lean_ctor_get(v___x_2049_, 1);
v_ngen_2053_ = lean_ctor_get(v___x_2049_, 2);
v_auxDeclNGen_2054_ = lean_ctor_get(v___x_2049_, 3);
v_cache_2055_ = lean_ctor_get(v___x_2049_, 5);
v_messages_2056_ = lean_ctor_get(v___x_2049_, 6);
v_infoState_2057_ = lean_ctor_get(v___x_2049_, 7);
v_snapshotTasks_2058_ = lean_ctor_get(v___x_2049_, 8);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2060_ = v___x_2049_;
v_isShared_2061_ = v_isSharedCheck_2088_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_snapshotTasks_2058_);
lean_inc(v_infoState_2057_);
lean_inc(v_messages_2056_);
lean_inc(v_cache_2055_);
lean_inc(v_traceState_2050_);
lean_inc(v_auxDeclNGen_2054_);
lean_inc(v_ngen_2053_);
lean_inc(v_nextMacroScope_2052_);
lean_inc(v_env_2051_);
lean_dec(v___x_2049_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2088_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
uint64_t v_tid_2062_; lean_object* v_traces_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2087_; 
v_tid_2062_ = lean_ctor_get_uint64(v_traceState_2050_, sizeof(void*)*1);
v_traces_2063_ = lean_ctor_get(v_traceState_2050_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_traceState_2050_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2065_ = v_traceState_2050_;
v_isShared_2066_ = v_isSharedCheck_2087_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_traces_2063_);
lean_dec(v_traceState_2050_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2087_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; double v___x_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2067_ = lean_box(0);
v___x_2068_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_2069_ = 0;
v___x_2070_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2071_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2071_, 0, v_cls_2036_);
lean_ctor_set(v___x_2071_, 1, v___x_2067_);
lean_ctor_set(v___x_2071_, 2, v___x_2070_);
lean_ctor_set_float(v___x_2071_, sizeof(void*)*3, v___x_2068_);
lean_ctor_set_float(v___x_2071_, sizeof(void*)*3 + 8, v___x_2068_);
lean_ctor_set_uint8(v___x_2071_, sizeof(void*)*3 + 16, v___x_2069_);
v___x_2072_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_2073_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v_a_2045_);
lean_ctor_set(v___x_2073_, 2, v___x_2072_);
lean_inc(v_ref_2043_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_ref_2043_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_PersistentArray_push___redArg(v_traces_2063_, v___x_2074_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2075_);
v___x_2077_ = v___x_2065_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2075_);
lean_ctor_set_uint64(v_reuseFailAlloc_2086_, sizeof(void*)*1, v_tid_2062_);
v___x_2077_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2079_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v___x_2077_);
v___x_2079_ = v___x_2060_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_env_2051_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_nextMacroScope_2052_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_ngen_2053_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_auxDeclNGen_2054_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2085_, 5, v_cache_2055_);
lean_ctor_set(v_reuseFailAlloc_2085_, 6, v_messages_2056_);
lean_ctor_set(v_reuseFailAlloc_2085_, 7, v_infoState_2057_);
lean_ctor_set(v_reuseFailAlloc_2085_, 8, v_snapshotTasks_2058_);
v___x_2079_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2080_ = lean_st_ref_put(v___y_2041_, v___x_2079_);
v___x_2081_ = lean_box(0);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2081_);
v___x_2083_ = v___x_2047_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_2090_, lean_object* v_msg_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2090_, v_msg_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v_res_2097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2101_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_2102_ = lean_unsigned_to_nat(30u);
v___x_2103_ = lean_unsigned_to_nat(96u);
v___x_2104_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_2105_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_2106_ = l_mkPanicMessageWithDecl(v___x_2105_, v___x_2104_, v___x_2103_, v___x_2102_, v___x_2101_);
return v___x_2106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_cls_2115_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_2117_ = l_Lean_Name_append(v___x_2116_, v_cls_2115_);
return v___x_2117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_2123_ = l_Lean_stringToMessageData(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2126_ = l_Lean_stringToMessageData(v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2127_, lean_object* v_mvarId_2128_, lean_object* v_h_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v_options_2155_; uint8_t v_hasTrace_2156_; 
v_options_2155_ = lean_ctor_get(v_a_2132_, 2);
v_hasTrace_2156_ = lean_ctor_get_uint8(v_options_2155_, sizeof(void*)*1);
if (v_hasTrace_2156_ == 0)
{
v___y_2136_ = v_a_2130_;
v___y_2137_ = v_a_2131_;
v___y_2138_ = v_a_2132_;
v___y_2139_ = v_a_2133_;
goto v___jp_2135_;
}
else
{
lean_object* v_inheritedTraceOptions_2157_; lean_object* v_cls_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v_inheritedTraceOptions_2157_ = lean_ctor_get(v_a_2132_, 13);
v_cls_2158_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2159_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2160_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2157_, v_options_2155_, v___x_2159_);
if (v___x_2160_ == 0)
{
v___y_2136_ = v_a_2130_;
v___y_2137_ = v_a_2131_;
v___y_2138_ = v_a_2132_;
v___y_2139_ = v_a_2133_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2161_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2127_);
v___x_2162_ = l_Lean_MessageData_ofName(v_ctorName_2127_);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
lean_inc(v_h_2129_);
v___x_2166_ = l_Lean_mkFVar(v_h_2129_);
v___x_2167_ = l_Lean_MessageData_ofExpr(v___x_2166_);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2165_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
lean_inc(v_mvarId_2128_);
v___x_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_mvarId_2128_);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2158_, v___x_2172_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_dec_ref_known(v___x_2173_, 1);
v___y_2136_ = v_a_2130_;
v___y_2137_ = v_a_2131_;
v___y_2138_ = v_a_2132_;
v___y_2139_ = v_a_2133_;
goto v___jp_2135_;
}
else
{
lean_dec(v_h_2129_);
lean_dec(v_mvarId_2128_);
lean_dec(v_ctorName_2127_);
return v___x_2173_;
}
}
}
v___jp_2135_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_box(0);
v___x_2141_ = l_Lean_Meta_injection(v_mvarId_2128_, v_h_2129_, v___x_2140_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
if (lean_obj_tag(v_a_2142_) == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec(v_ctorName_2127_);
v___x_2143_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2144_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2143_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
return v___x_2144_;
}
else
{
lean_object* v_mvarId_2145_; lean_object* v___x_2146_; 
v_mvarId_2145_ = lean_ctor_get(v_a_2142_, 0);
lean_inc(v_mvarId_2145_);
lean_dec_ref_known(v_a_2142_, 3);
v___x_2146_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2145_, v_ctorName_2127_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
return v___x_2146_;
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec(v_ctorName_2127_);
v_a_2147_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2141_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2141_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2174_, lean_object* v_mvarId_2175_, lean_object* v_h_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2174_, v_mvarId_2175_, v_h_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2183_, lean_object* v_k_2184_, uint8_t v_cleanupAnnotations_2185_, uint8_t v_whnfType_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___f_2192_; lean_object* v___x_2193_; 
v___f_2192_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2192_, 0, v_k_2184_);
v___x_2193_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2183_, v___f_2192_, v_cleanupAnnotations_2185_, v_whnfType_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_a_2202_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2193_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2193_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2210_, lean_object* v_k_2211_, lean_object* v_cleanupAnnotations_2212_, lean_object* v_whnfType_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2219_; uint8_t v_whnfType_boxed_2220_; lean_object* v_res_2221_; 
v_cleanupAnnotations_boxed_2219_ = lean_unbox(v_cleanupAnnotations_2212_);
v_whnfType_boxed_2220_ = lean_unbox(v_whnfType_2213_);
v_res_2221_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2210_, v_k_2211_, v_cleanupAnnotations_boxed_2219_, v_whnfType_boxed_2220_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2222_, lean_object* v_type_2223_, lean_object* v_k_2224_, uint8_t v_cleanupAnnotations_2225_, uint8_t v_whnfType_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2223_, v_k_2224_, v_cleanupAnnotations_2225_, v_whnfType_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2233_, lean_object* v_type_2234_, lean_object* v_k_2235_, lean_object* v_cleanupAnnotations_2236_, lean_object* v_whnfType_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2243_; uint8_t v_whnfType_boxed_2244_; lean_object* v_res_2245_; 
v_cleanupAnnotations_boxed_2243_ = lean_unbox(v_cleanupAnnotations_2236_);
v_whnfType_boxed_2244_ = lean_unbox(v_whnfType_2237_);
v_res_2245_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2233_, v_type_2234_, v_k_2235_, v_cleanupAnnotations_boxed_2243_, v_whnfType_boxed_2244_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2246_, lean_object* v_ctorName_2247_, lean_object* v_xs_2248_, lean_object* v_type_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_box(0);
v___x_2256_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2249_, v___x_2255_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2258_ = l_Lean_Expr_mvarId_x21(v_a_2257_);
v___x_2259_ = lean_array_get_size(v_xs_2248_);
v___x_2260_ = lean_unsigned_to_nat(1u);
v___x_2261_ = lean_nat_sub(v___x_2259_, v___x_2260_);
v___x_2262_ = lean_array_get_borrowed(v___x_2246_, v_xs_2248_, v___x_2261_);
lean_dec(v___x_2261_);
v___x_2263_ = l_Lean_Expr_fvarId_x21(v___x_2262_);
v___x_2264_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2247_, v___x_2258_, v___x_2263_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2264_) == 0)
{
uint8_t v___x_2265_; uint8_t v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; 
lean_dec_ref_known(v___x_2264_, 1);
v___x_2265_ = 0;
v___x_2266_ = 1;
v___x_2267_ = 1;
v___x_2268_ = l_Lean_Meta_mkLambdaFVars(v_xs_2248_, v_a_2257_, v___x_2265_, v___x_2266_, v___x_2265_, v___x_2266_, v___x_2267_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2268_;
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_a_2257_);
v_a_2269_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2264_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2264_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_dec(v_ctorName_2247_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2277_, lean_object* v_ctorName_2278_, lean_object* v_xs_2279_, lean_object* v_type_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2277_, v_ctorName_2278_, v_xs_2279_, v_type_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec_ref(v_xs_2279_);
lean_dec_ref(v___x_2277_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2287_, lean_object* v_targetType_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2294_; lean_object* v___f_2295_; uint8_t v___x_2296_; lean_object* v___x_2297_; 
v___x_2294_ = l_Lean_instInhabitedExpr;
v___f_2295_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2295_, 0, v___x_2294_);
lean_closure_set(v___f_2295_, 1, v_ctorName_2287_);
v___x_2296_ = 0;
v___x_2297_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2288_, v___f_2295_, v___x_2296_, v___x_2296_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2298_, lean_object* v_targetType_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2298_, v_targetType_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2309_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2311_ = l_Lean_Name_append(v_ctorName_2309_, v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v___x_2315_; 
v___x_2315_ = l_Lean_Expr_hasMVar(v_e_2312_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_e_2312_);
return v___x_2316_;
}
else
{
lean_object* v___x_2317_; lean_object* v_mctx_2318_; lean_object* v___x_2319_; lean_object* v_fst_2320_; lean_object* v_snd_2321_; lean_object* v___x_2322_; lean_object* v_cache_2323_; lean_object* v_zetaDeltaFVarIds_2324_; lean_object* v_postponed_2325_; lean_object* v_diag_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2335_; 
v___x_2317_ = lean_st_ref_get(v___y_2313_);
v_mctx_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc_ref(v_mctx_2318_);
lean_dec(v___x_2317_);
v___x_2319_ = l_Lean_instantiateMVarsCore(v_mctx_2318_, v_e_2312_);
v_fst_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_fst_2320_);
v_snd_2321_ = lean_ctor_get(v___x_2319_, 1);
lean_inc(v_snd_2321_);
lean_dec_ref(v___x_2319_);
v___x_2322_ = lean_st_ref_take(v___y_2313_);
v_cache_2323_ = lean_ctor_get(v___x_2322_, 1);
v_zetaDeltaFVarIds_2324_ = lean_ctor_get(v___x_2322_, 2);
v_postponed_2325_ = lean_ctor_get(v___x_2322_, 3);
v_diag_2326_ = lean_ctor_get(v___x_2322_, 4);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v___x_2322_, 0);
lean_dec(v_unused_2336_);
v___x_2328_ = v___x_2322_;
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_diag_2326_);
lean_inc(v_postponed_2325_);
lean_inc(v_zetaDeltaFVarIds_2324_);
lean_inc(v_cache_2323_);
lean_dec(v___x_2322_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v_snd_2321_);
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_snd_2321_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_cache_2323_);
lean_ctor_set(v_reuseFailAlloc_2334_, 2, v_zetaDeltaFVarIds_2324_);
lean_ctor_set(v_reuseFailAlloc_2334_, 3, v_postponed_2325_);
lean_ctor_set(v_reuseFailAlloc_2334_, 4, v_diag_2326_);
v___x_2331_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_st_ref_put(v___y_2313_, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_fst_2320_);
return v___x_2333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2337_, v___y_2338_);
lean_dec(v___y_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2341_, v___y_2343_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
return v_res_2354_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_unsigned_to_nat(32u);
v___x_2356_ = lean_mk_empty_array_with_capacity(v___x_2355_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2358_ = ((size_t)5ULL);
v___x_2359_ = lean_unsigned_to_nat(0u);
v___x_2360_ = lean_unsigned_to_nat(32u);
v___x_2361_ = lean_mk_empty_array_with_capacity(v___x_2360_);
v___x_2362_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2363_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___x_2361_);
lean_ctor_set(v___x_2363_, 2, v___x_2359_);
lean_ctor_set(v___x_2363_, 3, v___x_2359_);
lean_ctor_set_usize(v___x_2363_, 4, v___x_2358_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v_traceState_2367_; lean_object* v_traces_2368_; lean_object* v___x_2369_; lean_object* v_traceState_2370_; lean_object* v_env_2371_; lean_object* v_nextMacroScope_2372_; lean_object* v_ngen_2373_; lean_object* v_auxDeclNGen_2374_; lean_object* v_cache_2375_; lean_object* v_messages_2376_; lean_object* v_infoState_2377_; lean_object* v_snapshotTasks_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2397_; 
v___x_2366_ = lean_st_ref_get(v___y_2364_);
v_traceState_2367_ = lean_ctor_get(v___x_2366_, 4);
lean_inc_ref(v_traceState_2367_);
lean_dec(v___x_2366_);
v_traces_2368_ = lean_ctor_get(v_traceState_2367_, 0);
lean_inc_ref(v_traces_2368_);
lean_dec_ref(v_traceState_2367_);
v___x_2369_ = lean_st_ref_take(v___y_2364_);
v_traceState_2370_ = lean_ctor_get(v___x_2369_, 4);
v_env_2371_ = lean_ctor_get(v___x_2369_, 0);
v_nextMacroScope_2372_ = lean_ctor_get(v___x_2369_, 1);
v_ngen_2373_ = lean_ctor_get(v___x_2369_, 2);
v_auxDeclNGen_2374_ = lean_ctor_get(v___x_2369_, 3);
v_cache_2375_ = lean_ctor_get(v___x_2369_, 5);
v_messages_2376_ = lean_ctor_get(v___x_2369_, 6);
v_infoState_2377_ = lean_ctor_get(v___x_2369_, 7);
v_snapshotTasks_2378_ = lean_ctor_get(v___x_2369_, 8);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2380_ = v___x_2369_;
v_isShared_2381_ = v_isSharedCheck_2397_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_snapshotTasks_2378_);
lean_inc(v_infoState_2377_);
lean_inc(v_messages_2376_);
lean_inc(v_cache_2375_);
lean_inc(v_traceState_2370_);
lean_inc(v_auxDeclNGen_2374_);
lean_inc(v_ngen_2373_);
lean_inc(v_nextMacroScope_2372_);
lean_inc(v_env_2371_);
lean_dec(v___x_2369_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2397_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
uint64_t v_tid_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2395_; 
v_tid_2382_ = lean_ctor_get_uint64(v_traceState_2370_, sizeof(void*)*1);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_traceState_2370_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; 
v_unused_2396_ = lean_ctor_get(v_traceState_2370_, 0);
lean_dec(v_unused_2396_);
v___x_2384_ = v_traceState_2370_;
v_isShared_2385_ = v_isSharedCheck_2395_;
goto v_resetjp_2383_;
}
else
{
lean_dec(v_traceState_2370_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2395_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2386_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2386_);
lean_ctor_set_uint64(v_reuseFailAlloc_2394_, sizeof(void*)*1, v_tid_2382_);
v___x_2388_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 4, v___x_2388_);
v___x_2390_ = v___x_2380_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_env_2371_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_nextMacroScope_2372_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_ngen_2373_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v_auxDeclNGen_2374_);
lean_ctor_set(v_reuseFailAlloc_2393_, 4, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2393_, 5, v_cache_2375_);
lean_ctor_set(v_reuseFailAlloc_2393_, 6, v_messages_2376_);
lean_ctor_set(v_reuseFailAlloc_2393_, 7, v_infoState_2377_);
lean_ctor_set(v_reuseFailAlloc_2393_, 8, v_snapshotTasks_2378_);
v___x_2390_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = lean_st_ref_put(v___y_2364_, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v_traces_2368_);
return v___x_2392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2398_);
lean_dec(v___y_2398_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2413_, lean_object* v_opt_2414_){
_start:
{
lean_object* v_name_2415_; lean_object* v_defValue_2416_; lean_object* v_map_2417_; lean_object* v___x_2418_; 
v_name_2415_ = lean_ctor_get(v_opt_2414_, 0);
v_defValue_2416_ = lean_ctor_get(v_opt_2414_, 1);
v_map_2417_ = lean_ctor_get(v_opts_2413_, 0);
v___x_2418_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2417_, v_name_2415_);
if (lean_obj_tag(v___x_2418_) == 0)
{
uint8_t v___x_2419_; 
v___x_2419_ = lean_unbox(v_defValue_2416_);
return v___x_2419_;
}
else
{
lean_object* v_val_2420_; 
v_val_2420_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_val_2420_);
lean_dec_ref_known(v___x_2418_, 1);
if (lean_obj_tag(v_val_2420_) == 1)
{
uint8_t v_v_2421_; 
v_v_2421_ = lean_ctor_get_uint8(v_val_2420_, 0);
lean_dec_ref_known(v_val_2420_, 0);
return v_v_2421_;
}
else
{
uint8_t v___x_2422_; 
lean_dec(v_val_2420_);
v___x_2422_ = lean_unbox(v_defValue_2416_);
return v___x_2422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2423_, lean_object* v_opt_2424_){
_start:
{
uint8_t v_res_2425_; lean_object* v_r_2426_; 
v_res_2425_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2423_, v_opt_2424_);
lean_dec_ref(v_opt_2424_);
lean_dec_ref(v_opts_2423_);
v_r_2426_ = lean_box(v_res_2425_);
return v_r_2426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2429_ = l_Lean_stringToMessageData(v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2430_, lean_object* v_x_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2437_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2438_ = l_Lean_MessageData_ofName(v_name_2430_);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2443_, lean_object* v_x_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2443_, v_x_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec_ref(v_x_2444_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2451_, lean_object* v_val_2452_, lean_object* v_name_2453_, lean_object* v_levelParams_2454_, uint8_t v___x_2455_, lean_object* v_____r_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___x_2462_; 
lean_inc_ref(v_val_2452_);
v___x_2462_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2451_, v_val_2452_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; lean_object* v_a_2465_; lean_object* v___x_2466_; lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2479_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2452_, v___y_2458_);
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2463_, v___y_2458_);
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2479_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2479_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_inc(v_name_2453_);
v___x_2471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2471_, 0, v_name_2453_);
lean_ctor_set(v___x_2471_, 1, v_levelParams_2454_);
lean_ctor_set(v___x_2471_, 2, v_a_2465_);
v___x_2472_ = lean_box(0);
v___x_2473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_name_2453_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2471_);
lean_ctor_set(v___x_2474_, 1, v_a_2467_);
lean_ctor_set(v___x_2474_, 2, v___x_2473_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set_tag(v___x_2469_, 2);
lean_ctor_set(v___x_2469_, 0, v___x_2474_);
v___x_2476_ = v___x_2469_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_addDecl(v___x_2476_, v___x_2455_, v___y_2459_, v___y_2460_);
return v___x_2477_;
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_levelParams_2454_);
lean_dec(v_name_2453_);
lean_dec_ref(v_val_2452_);
v_a_2480_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2462_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2462_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2488_, lean_object* v_val_2489_, lean_object* v_name_2490_, lean_object* v_levelParams_2491_, lean_object* v___x_2492_, lean_object* v_____r_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v___x_12904__boxed_2499_; lean_object* v_res_2500_; 
v___x_12904__boxed_2499_ = lean_unbox(v___x_2492_);
v_res_2500_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2488_, v_val_2489_, v_name_2490_, v_levelParams_2491_, v___x_12904__boxed_2499_, v_____r_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2501_, lean_object* v_val_2502_, lean_object* v_name_2503_, lean_object* v_levelParams_2504_, lean_object* v_____r_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; 
lean_inc_ref(v_val_2502_);
v___x_2511_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2501_, v_val_2502_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2513_; lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2529_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v___x_2513_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2502_, v___y_2507_);
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2513_);
v___x_2515_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2512_, v___y_2507_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2529_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2529_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
lean_inc(v_name_2503_);
v___x_2520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2520_, 0, v_name_2503_);
lean_ctor_set(v___x_2520_, 1, v_levelParams_2504_);
lean_ctor_set(v___x_2520_, 2, v_a_2514_);
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2522_, 0, v_name_2503_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2520_);
lean_ctor_set(v___x_2523_, 1, v_a_2516_);
lean_ctor_set(v___x_2523_, 2, v___x_2522_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 2);
lean_ctor_set(v___x_2518_, 0, v___x_2523_);
v___x_2525_ = v___x_2518_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
uint8_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = 0;
v___x_2527_ = l_Lean_addDecl(v___x_2525_, v___x_2526_, v___y_2508_, v___y_2509_);
return v___x_2527_;
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec(v_levelParams_2504_);
lean_dec(v_name_2503_);
lean_dec_ref(v_val_2502_);
v_a_2530_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2511_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2511_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2538_, lean_object* v_val_2539_, lean_object* v_name_2540_, lean_object* v_levelParams_2541_, lean_object* v_____r_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2538_, v_val_2539_, v_name_2540_, v_levelParams_2541_, v_____r_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t v_sz_2549_, size_t v_i_2550_, lean_object* v_bs_2551_){
_start:
{
uint8_t v___x_2552_; 
v___x_2552_ = lean_usize_dec_lt(v_i_2550_, v_sz_2549_);
if (v___x_2552_ == 0)
{
return v_bs_2551_;
}
else
{
lean_object* v_v_2553_; lean_object* v_msg_2554_; lean_object* v___x_2555_; lean_object* v_bs_x27_2556_; size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v_v_2553_ = lean_array_uget_borrowed(v_bs_2551_, v_i_2550_);
v_msg_2554_ = lean_ctor_get(v_v_2553_, 1);
lean_inc_ref(v_msg_2554_);
v___x_2555_ = lean_unsigned_to_nat(0u);
v_bs_x27_2556_ = lean_array_uset(v_bs_2551_, v_i_2550_, v___x_2555_);
v___x_2557_ = ((size_t)1ULL);
v___x_2558_ = lean_usize_add(v_i_2550_, v___x_2557_);
v___x_2559_ = lean_array_uset(v_bs_x27_2556_, v_i_2550_, v_msg_2554_);
v_i_2550_ = v___x_2558_;
v_bs_2551_ = v___x_2559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2561_, lean_object* v_i_2562_, lean_object* v_bs_2563_){
_start:
{
size_t v_sz_boxed_2564_; size_t v_i_boxed_2565_; lean_object* v_res_2566_; 
v_sz_boxed_2564_ = lean_unbox_usize(v_sz_2561_);
lean_dec(v_sz_2561_);
v_i_boxed_2565_ = lean_unbox_usize(v_i_2562_);
lean_dec(v_i_2562_);
v_res_2566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_boxed_2564_, v_i_boxed_2565_, v_bs_2563_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_oldTraces_2567_, lean_object* v_data_2568_, lean_object* v_ref_2569_, lean_object* v_msg_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_fileName_2576_; lean_object* v_fileMap_2577_; lean_object* v_options_2578_; lean_object* v_currRecDepth_2579_; lean_object* v_maxRecDepth_2580_; lean_object* v_ref_2581_; lean_object* v_currNamespace_2582_; lean_object* v_openDecls_2583_; lean_object* v_initHeartbeats_2584_; lean_object* v_maxHeartbeats_2585_; lean_object* v_quotContext_2586_; lean_object* v_currMacroScope_2587_; uint8_t v_diag_2588_; lean_object* v_cancelTk_x3f_2589_; uint8_t v_suppressElabErrors_2590_; lean_object* v_inheritedTraceOptions_2591_; lean_object* v___x_2592_; lean_object* v_traceState_2593_; lean_object* v_traces_2594_; lean_object* v_ref_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; size_t v_sz_2598_; size_t v___x_2599_; lean_object* v___x_2600_; lean_object* v_msg_2601_; lean_object* v___x_2602_; lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2640_; 
v_fileName_2576_ = lean_ctor_get(v___y_2573_, 0);
v_fileMap_2577_ = lean_ctor_get(v___y_2573_, 1);
v_options_2578_ = lean_ctor_get(v___y_2573_, 2);
v_currRecDepth_2579_ = lean_ctor_get(v___y_2573_, 3);
v_maxRecDepth_2580_ = lean_ctor_get(v___y_2573_, 4);
v_ref_2581_ = lean_ctor_get(v___y_2573_, 5);
v_currNamespace_2582_ = lean_ctor_get(v___y_2573_, 6);
v_openDecls_2583_ = lean_ctor_get(v___y_2573_, 7);
v_initHeartbeats_2584_ = lean_ctor_get(v___y_2573_, 8);
v_maxHeartbeats_2585_ = lean_ctor_get(v___y_2573_, 9);
v_quotContext_2586_ = lean_ctor_get(v___y_2573_, 10);
v_currMacroScope_2587_ = lean_ctor_get(v___y_2573_, 11);
v_diag_2588_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*14);
v_cancelTk_x3f_2589_ = lean_ctor_get(v___y_2573_, 12);
v_suppressElabErrors_2590_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2591_ = lean_ctor_get(v___y_2573_, 13);
v___x_2592_ = lean_st_ref_get(v___y_2574_);
v_traceState_2593_ = lean_ctor_get(v___x_2592_, 4);
lean_inc_ref(v_traceState_2593_);
lean_dec(v___x_2592_);
v_traces_2594_ = lean_ctor_get(v_traceState_2593_, 0);
lean_inc_ref(v_traces_2594_);
lean_dec_ref(v_traceState_2593_);
v_ref_2595_ = l_Lean_replaceRef(v_ref_2569_, v_ref_2581_);
lean_inc_ref(v_inheritedTraceOptions_2591_);
lean_inc(v_cancelTk_x3f_2589_);
lean_inc(v_currMacroScope_2587_);
lean_inc(v_quotContext_2586_);
lean_inc(v_maxHeartbeats_2585_);
lean_inc(v_initHeartbeats_2584_);
lean_inc(v_openDecls_2583_);
lean_inc(v_currNamespace_2582_);
lean_inc(v_maxRecDepth_2580_);
lean_inc(v_currRecDepth_2579_);
lean_inc_ref(v_options_2578_);
lean_inc_ref(v_fileMap_2577_);
lean_inc_ref(v_fileName_2576_);
v___x_2596_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2596_, 0, v_fileName_2576_);
lean_ctor_set(v___x_2596_, 1, v_fileMap_2577_);
lean_ctor_set(v___x_2596_, 2, v_options_2578_);
lean_ctor_set(v___x_2596_, 3, v_currRecDepth_2579_);
lean_ctor_set(v___x_2596_, 4, v_maxRecDepth_2580_);
lean_ctor_set(v___x_2596_, 5, v_ref_2595_);
lean_ctor_set(v___x_2596_, 6, v_currNamespace_2582_);
lean_ctor_set(v___x_2596_, 7, v_openDecls_2583_);
lean_ctor_set(v___x_2596_, 8, v_initHeartbeats_2584_);
lean_ctor_set(v___x_2596_, 9, v_maxHeartbeats_2585_);
lean_ctor_set(v___x_2596_, 10, v_quotContext_2586_);
lean_ctor_set(v___x_2596_, 11, v_currMacroScope_2587_);
lean_ctor_set(v___x_2596_, 12, v_cancelTk_x3f_2589_);
lean_ctor_set(v___x_2596_, 13, v_inheritedTraceOptions_2591_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*14, v_diag_2588_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*14 + 1, v_suppressElabErrors_2590_);
v___x_2597_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2594_);
lean_dec_ref(v_traces_2594_);
v_sz_2598_ = lean_array_size(v___x_2597_);
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_2598_, v___x_2599_, v___x_2597_);
v_msg_2601_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2601_, 0, v_data_2568_);
lean_ctor_set(v_msg_2601_, 1, v_msg_2570_);
lean_ctor_set(v_msg_2601_, 2, v___x_2600_);
v___x_2602_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2601_, v___y_2571_, v___y_2572_, v___x_2596_, v___y_2574_);
lean_dec_ref_known(v___x_2596_, 14);
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2640_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2640_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v_traceState_2608_; lean_object* v_env_2609_; lean_object* v_nextMacroScope_2610_; lean_object* v_ngen_2611_; lean_object* v_auxDeclNGen_2612_; lean_object* v_cache_2613_; lean_object* v_messages_2614_; lean_object* v_infoState_2615_; lean_object* v_snapshotTasks_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2639_; 
v___x_2607_ = lean_st_ref_take(v___y_2574_);
v_traceState_2608_ = lean_ctor_get(v___x_2607_, 4);
v_env_2609_ = lean_ctor_get(v___x_2607_, 0);
v_nextMacroScope_2610_ = lean_ctor_get(v___x_2607_, 1);
v_ngen_2611_ = lean_ctor_get(v___x_2607_, 2);
v_auxDeclNGen_2612_ = lean_ctor_get(v___x_2607_, 3);
v_cache_2613_ = lean_ctor_get(v___x_2607_, 5);
v_messages_2614_ = lean_ctor_get(v___x_2607_, 6);
v_infoState_2615_ = lean_ctor_get(v___x_2607_, 7);
v_snapshotTasks_2616_ = lean_ctor_get(v___x_2607_, 8);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2618_ = v___x_2607_;
v_isShared_2619_ = v_isSharedCheck_2639_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_snapshotTasks_2616_);
lean_inc(v_infoState_2615_);
lean_inc(v_messages_2614_);
lean_inc(v_cache_2613_);
lean_inc(v_traceState_2608_);
lean_inc(v_auxDeclNGen_2612_);
lean_inc(v_ngen_2611_);
lean_inc(v_nextMacroScope_2610_);
lean_inc(v_env_2609_);
lean_dec(v___x_2607_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2639_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
uint64_t v_tid_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2637_; 
v_tid_2620_ = lean_ctor_get_uint64(v_traceState_2608_, sizeof(void*)*1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_traceState_2608_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v_traceState_2608_, 0);
lean_dec(v_unused_2638_);
v___x_2622_ = v_traceState_2608_;
v_isShared_2623_ = v_isSharedCheck_2637_;
goto v_resetjp_2621_;
}
else
{
lean_dec(v_traceState_2608_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2637_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v_ref_2569_);
lean_ctor_set(v___x_2624_, 1, v_a_2603_);
v___x_2625_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2567_, v___x_2624_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2625_);
v___x_2627_ = v___x_2622_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2625_);
lean_ctor_set_uint64(v_reuseFailAlloc_2636_, sizeof(void*)*1, v_tid_2620_);
v___x_2627_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2629_; 
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 4, v___x_2627_);
v___x_2629_ = v___x_2618_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_env_2609_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_nextMacroScope_2610_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v_ngen_2611_);
lean_ctor_set(v_reuseFailAlloc_2635_, 3, v_auxDeclNGen_2612_);
lean_ctor_set(v_reuseFailAlloc_2635_, 4, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2635_, 5, v_cache_2613_);
lean_ctor_set(v_reuseFailAlloc_2635_, 6, v_messages_2614_);
lean_ctor_set(v_reuseFailAlloc_2635_, 7, v_infoState_2615_);
lean_ctor_set(v_reuseFailAlloc_2635_, 8, v_snapshotTasks_2616_);
v___x_2629_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2630_ = lean_st_ref_put(v___y_2574_, v___x_2629_);
v___x_2631_ = lean_box(0);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2631_);
v___x_2633_ = v___x_2605_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_oldTraces_2641_, lean_object* v_data_2642_, lean_object* v_ref_2643_, lean_object* v_msg_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2641_, v_data_2642_, v_ref_2643_, v_msg_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2651_, lean_object* v_opt_2652_){
_start:
{
lean_object* v_name_2653_; lean_object* v_defValue_2654_; lean_object* v_map_2655_; lean_object* v___x_2656_; 
v_name_2653_ = lean_ctor_get(v_opt_2652_, 0);
v_defValue_2654_ = lean_ctor_get(v_opt_2652_, 1);
v_map_2655_ = lean_ctor_get(v_opts_2651_, 0);
v___x_2656_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2655_, v_name_2653_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_inc(v_defValue_2654_);
return v_defValue_2654_;
}
else
{
lean_object* v_val_2657_; 
v_val_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_val_2657_);
lean_dec_ref_known(v___x_2656_, 1);
if (lean_obj_tag(v_val_2657_) == 3)
{
lean_object* v_v_2658_; 
v_v_2658_ = lean_ctor_get(v_val_2657_, 0);
lean_inc(v_v_2658_);
lean_dec_ref_known(v_val_2657_, 1);
return v_v_2658_;
}
else
{
lean_dec(v_val_2657_);
lean_inc(v_defValue_2654_);
return v_defValue_2654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2659_, lean_object* v_opt_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2659_, v_opt_2660_);
lean_dec_ref(v_opt_2660_);
lean_dec_ref(v_opts_2659_);
return v_res_2661_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_e_2662_){
_start:
{
if (lean_obj_tag(v_e_2662_) == 0)
{
uint8_t v___x_2663_; 
v___x_2663_ = 2;
return v___x_2663_;
}
else
{
uint8_t v___x_2664_; 
v___x_2664_ = 0;
return v___x_2664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_e_2665_){
_start:
{
uint8_t v_res_2666_; lean_object* v_r_2667_; 
v_res_2666_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_e_2665_);
lean_dec_ref(v_e_2665_);
v_r_2667_ = lean_box(v_res_2666_);
return v_r_2667_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object* v_x_2668_){
_start:
{
if (lean_obj_tag(v_x_2668_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_a_2670_ = lean_ctor_get(v_x_2668_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_x_2668_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v_x_2668_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v_x_2668_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 1);
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_a_2678_ = lean_ctor_get(v_x_2668_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_x_2668_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v_x_2668_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v_x_2668_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 0);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object* v_x_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2686_);
return v_res_2688_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2691_ = l_Lean_stringToMessageData(v___x_2690_);
return v___x_2691_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2692_; double v___x_2693_; 
v___x_2692_ = lean_unsigned_to_nat(1000u);
v___x_2693_ = lean_float_of_nat(v___x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2694_, uint8_t v_collapsed_2695_, lean_object* v_tag_2696_, lean_object* v_opts_2697_, uint8_t v_clsEnabled_2698_, lean_object* v_oldTraces_2699_, lean_object* v_msg_2700_, lean_object* v_resStartStop_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_fst_2707_; lean_object* v_snd_2708_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v_data_2712_; lean_object* v_fst_2715_; lean_object* v_snd_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___y_2720_; lean_object* v_a_2721_; uint8_t v___y_2736_; double v___y_2767_; 
v_fst_2707_ = lean_ctor_get(v_resStartStop_2701_, 0);
lean_inc(v_fst_2707_);
v_snd_2708_ = lean_ctor_get(v_resStartStop_2701_, 1);
lean_inc(v_snd_2708_);
lean_dec_ref(v_resStartStop_2701_);
v_fst_2715_ = lean_ctor_get(v_snd_2708_, 0);
lean_inc(v_fst_2715_);
v_snd_2716_ = lean_ctor_get(v_snd_2708_, 1);
lean_inc(v_snd_2716_);
lean_dec(v_snd_2708_);
v___x_2717_ = l_Lean_trace_profiler;
v___x_2718_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2697_, v___x_2717_);
if (v___x_2718_ == 0)
{
v___y_2736_ = v___x_2718_;
goto v___jp_2735_;
}
else
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2773_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2697_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; double v___x_2776_; double v___x_2777_; double v___x_2778_; 
v___x_2774_ = l_Lean_trace_profiler_threshold;
v___x_2775_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2697_, v___x_2774_);
v___x_2776_ = lean_float_of_nat(v___x_2775_);
v___x_2777_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2);
v___x_2778_ = lean_float_div(v___x_2776_, v___x_2777_);
v___y_2767_ = v___x_2778_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; double v___x_2781_; 
v___x_2779_ = l_Lean_trace_profiler_threshold;
v___x_2780_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2697_, v___x_2779_);
v___x_2781_ = lean_float_of_nat(v___x_2780_);
v___y_2767_ = v___x_2781_;
goto v___jp_2766_;
}
}
v___jp_2709_:
{
lean_object* v___x_2713_; 
lean_inc(v___y_2710_);
v___x_2713_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2699_, v_data_2712_, v___y_2710_, v___y_2711_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v___x_2714_; 
lean_dec_ref_known(v___x_2713_, 1);
v___x_2714_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2707_);
return v___x_2714_;
}
else
{
lean_dec(v_fst_2707_);
return v___x_2713_;
}
}
v___jp_2719_:
{
uint8_t v_result_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; double v___x_2725_; lean_object* v_data_2726_; 
v_result_2722_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_fst_2707_);
v___x_2723_ = lean_box(v_result_2722_);
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
v___x_2725_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2696_);
lean_inc_ref(v___x_2724_);
lean_inc(v_cls_2694_);
v_data_2726_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2726_, 0, v_cls_2694_);
lean_ctor_set(v_data_2726_, 1, v___x_2724_);
lean_ctor_set(v_data_2726_, 2, v_tag_2696_);
lean_ctor_set_float(v_data_2726_, sizeof(void*)*3, v___x_2725_);
lean_ctor_set_float(v_data_2726_, sizeof(void*)*3 + 8, v___x_2725_);
lean_ctor_set_uint8(v_data_2726_, sizeof(void*)*3 + 16, v_collapsed_2695_);
if (v___x_2718_ == 0)
{
lean_dec_ref_known(v___x_2724_, 1);
lean_dec(v_snd_2716_);
lean_dec(v_fst_2715_);
lean_dec_ref(v_tag_2696_);
lean_dec(v_cls_2694_);
v___y_2710_ = v___y_2720_;
v___y_2711_ = v_a_2721_;
v_data_2712_ = v_data_2726_;
goto v___jp_2709_;
}
else
{
lean_object* v_data_2727_; double v___x_2728_; double v___x_2729_; 
lean_dec_ref_known(v_data_2726_, 3);
v_data_2727_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2727_, 0, v_cls_2694_);
lean_ctor_set(v_data_2727_, 1, v___x_2724_);
lean_ctor_set(v_data_2727_, 2, v_tag_2696_);
v___x_2728_ = lean_unbox_float(v_fst_2715_);
lean_dec(v_fst_2715_);
lean_ctor_set_float(v_data_2727_, sizeof(void*)*3, v___x_2728_);
v___x_2729_ = lean_unbox_float(v_snd_2716_);
lean_dec(v_snd_2716_);
lean_ctor_set_float(v_data_2727_, sizeof(void*)*3 + 8, v___x_2729_);
lean_ctor_set_uint8(v_data_2727_, sizeof(void*)*3 + 16, v_collapsed_2695_);
v___y_2710_ = v___y_2720_;
v___y_2711_ = v_a_2721_;
v_data_2712_ = v_data_2727_;
goto v___jp_2709_;
}
}
v___jp_2730_:
{
lean_object* v_ref_2731_; lean_object* v___x_2732_; 
v_ref_2731_ = lean_ctor_get(v___y_2704_, 5);
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v_fst_2707_);
v___x_2732_ = lean_apply_6(v_msg_2700_, v_fst_2707_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, lean_box(0));
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___y_2720_ = v_ref_2731_;
v_a_2721_ = v_a_2733_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2734_; 
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
v___y_2720_ = v_ref_2731_;
v_a_2721_ = v___x_2734_;
goto v___jp_2719_;
}
}
v___jp_2735_:
{
if (v_clsEnabled_2698_ == 0)
{
if (v___y_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v_traceState_2738_; lean_object* v_env_2739_; lean_object* v_nextMacroScope_2740_; lean_object* v_ngen_2741_; lean_object* v_auxDeclNGen_2742_; lean_object* v_cache_2743_; lean_object* v_messages_2744_; lean_object* v_infoState_2745_; lean_object* v_snapshotTasks_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v_snd_2716_);
lean_dec(v_fst_2715_);
lean_dec_ref(v_msg_2700_);
lean_dec_ref(v_tag_2696_);
lean_dec(v_cls_2694_);
v___x_2737_ = lean_st_ref_take(v___y_2705_);
v_traceState_2738_ = lean_ctor_get(v___x_2737_, 4);
v_env_2739_ = lean_ctor_get(v___x_2737_, 0);
v_nextMacroScope_2740_ = lean_ctor_get(v___x_2737_, 1);
v_ngen_2741_ = lean_ctor_get(v___x_2737_, 2);
v_auxDeclNGen_2742_ = lean_ctor_get(v___x_2737_, 3);
v_cache_2743_ = lean_ctor_get(v___x_2737_, 5);
v_messages_2744_ = lean_ctor_get(v___x_2737_, 6);
v_infoState_2745_ = lean_ctor_get(v___x_2737_, 7);
v_snapshotTasks_2746_ = lean_ctor_get(v___x_2737_, 8);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2748_ = v___x_2737_;
v_isShared_2749_ = v_isSharedCheck_2765_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_snapshotTasks_2746_);
lean_inc(v_infoState_2745_);
lean_inc(v_messages_2744_);
lean_inc(v_cache_2743_);
lean_inc(v_traceState_2738_);
lean_inc(v_auxDeclNGen_2742_);
lean_inc(v_ngen_2741_);
lean_inc(v_nextMacroScope_2740_);
lean_inc(v_env_2739_);
lean_dec(v___x_2737_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2765_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
uint64_t v_tid_2750_; lean_object* v_traces_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2764_; 
v_tid_2750_ = lean_ctor_get_uint64(v_traceState_2738_, sizeof(void*)*1);
v_traces_2751_ = lean_ctor_get(v_traceState_2738_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_traceState_2738_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2753_ = v_traceState_2738_;
v_isShared_2754_ = v_isSharedCheck_2764_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_traces_2751_);
lean_dec(v_traceState_2738_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2764_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2755_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2699_, v_traces_2751_);
lean_dec_ref(v_traces_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2755_);
v___x_2757_ = v___x_2753_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2755_);
lean_ctor_set_uint64(v_reuseFailAlloc_2763_, sizeof(void*)*1, v_tid_2750_);
v___x_2757_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2759_; 
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 4, v___x_2757_);
v___x_2759_ = v___x_2748_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_env_2739_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_nextMacroScope_2740_);
lean_ctor_set(v_reuseFailAlloc_2762_, 2, v_ngen_2741_);
lean_ctor_set(v_reuseFailAlloc_2762_, 3, v_auxDeclNGen_2742_);
lean_ctor_set(v_reuseFailAlloc_2762_, 4, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2762_, 5, v_cache_2743_);
lean_ctor_set(v_reuseFailAlloc_2762_, 6, v_messages_2744_);
lean_ctor_set(v_reuseFailAlloc_2762_, 7, v_infoState_2745_);
lean_ctor_set(v_reuseFailAlloc_2762_, 8, v_snapshotTasks_2746_);
v___x_2759_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_st_ref_put(v___y_2705_, v___x_2759_);
v___x_2761_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2707_);
return v___x_2761_;
}
}
}
}
}
else
{
goto v___jp_2730_;
}
}
else
{
goto v___jp_2730_;
}
}
v___jp_2766_:
{
double v___x_2768_; double v___x_2769_; double v___x_2770_; uint8_t v___x_2771_; 
v___x_2768_ = lean_unbox_float(v_snd_2716_);
v___x_2769_ = lean_unbox_float(v_fst_2715_);
v___x_2770_ = lean_float_sub(v___x_2768_, v___x_2769_);
v___x_2771_ = lean_float_decLt(v___y_2767_, v___x_2770_);
v___y_2736_ = v___x_2771_;
goto v___jp_2735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2782_, lean_object* v_collapsed_2783_, lean_object* v_tag_2784_, lean_object* v_opts_2785_, lean_object* v_clsEnabled_2786_, lean_object* v_oldTraces_2787_, lean_object* v_msg_2788_, lean_object* v_resStartStop_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
uint8_t v_collapsed_boxed_2795_; uint8_t v_clsEnabled_boxed_2796_; lean_object* v_res_2797_; 
v_collapsed_boxed_2795_ = lean_unbox(v_collapsed_2783_);
v_clsEnabled_boxed_2796_ = lean_unbox(v_clsEnabled_2786_);
v_res_2797_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2782_, v_collapsed_boxed_2795_, v_tag_2784_, v_opts_2785_, v_clsEnabled_boxed_2796_, v_oldTraces_2787_, v_msg_2788_, v_resStartStop_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec_ref(v_opts_2785_);
return v_res_2797_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2798_; double v___x_2799_; 
v___x_2798_ = lean_unsigned_to_nat(1000000000u);
v___x_2799_ = lean_float_of_nat(v___x_2798_);
return v___x_2799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2802_ = l_Lean_stringToMessageData(v___x_2801_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_toConstantVal_2809_; lean_object* v_options_2810_; lean_object* v_name_2811_; lean_object* v_levelParams_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_3023_; 
v_toConstantVal_2809_ = lean_ctor_get(v_ctorVal_2803_, 0);
lean_inc_ref(v_toConstantVal_2809_);
v_options_2810_ = lean_ctor_get(v_a_2806_, 2);
v_name_2811_ = lean_ctor_get(v_toConstantVal_2809_, 0);
v_levelParams_2812_ = lean_ctor_get(v_toConstantVal_2809_, 1);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_toConstantVal_2809_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; 
v_unused_3024_ = lean_ctor_get(v_toConstantVal_2809_, 2);
lean_dec(v_unused_3024_);
v___x_2814_ = v_toConstantVal_2809_;
v_isShared_2815_ = v_isSharedCheck_3023_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_levelParams_2812_);
lean_inc(v_name_2811_);
lean_dec(v_toConstantVal_2809_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_3023_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_inheritedTraceOptions_2816_; uint8_t v_hasTrace_2817_; lean_object* v_name_2818_; 
v_inheritedTraceOptions_2816_ = lean_ctor_get(v_a_2806_, 13);
v_hasTrace_2817_ = lean_ctor_get_uint8(v_options_2810_, sizeof(void*)*1);
lean_inc(v_name_2811_);
v_name_2818_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2811_);
if (v_hasTrace_2817_ == 0)
{
lean_object* v___x_2819_; 
v___x_2819_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2857_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2857_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2857_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
if (lean_obj_tag(v_a_2820_) == 1)
{
lean_object* v_val_2824_; lean_object* v___x_2825_; 
lean_del_object(v___x_2822_);
v_val_2824_ = lean_ctor_get(v_a_2820_, 0);
lean_inc_n(v_val_2824_, 2);
lean_dec_ref_known(v_a_2820_, 1);
v___x_2825_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2811_, v_val_2824_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2844_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2824_, v_a_2805_);
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref(v___x_2827_);
v___x_2829_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2826_, v_a_2805_);
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2844_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2844_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
lean_inc(v_name_2818_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 2, v_a_2828_);
lean_ctor_set(v___x_2814_, 0, v_name_2818_);
v___x_2835_ = v___x_2814_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_name_2818_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_levelParams_2812_);
lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_a_2828_);
v___x_2835_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2837_, 0, v_name_2818_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2835_);
lean_ctor_set(v___x_2838_, 1, v_a_2830_);
lean_ctor_set(v___x_2838_, 2, v___x_2837_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set_tag(v___x_2832_, 2);
lean_ctor_set(v___x_2832_, 0, v___x_2838_);
v___x_2840_ = v___x_2832_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_addDecl(v___x_2840_, v_hasTrace_2817_, v_a_2806_, v_a_2807_);
return v___x_2841_;
}
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v_val_2824_);
lean_dec(v_name_2818_);
lean_del_object(v___x_2814_);
lean_dec(v_levelParams_2812_);
v_a_2845_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2825_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2825_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
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
lean_object* v___x_2853_; lean_object* v___x_2855_; 
lean_dec(v_a_2820_);
lean_dec(v_name_2818_);
lean_del_object(v___x_2814_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v___x_2853_ = lean_box(0);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v___x_2853_);
v___x_2855_ = v___x_2822_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_name_2818_);
lean_del_object(v___x_2814_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v_a_2858_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2819_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2819_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
else
{
lean_object* v___f_2866_; lean_object* v_cls_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v_a_2874_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v_a_2886_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v_a_2891_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v_a_2902_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v_a_2917_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v_a_2922_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; 
lean_inc(v_name_2818_);
v___f_2866_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2866_, 0, v_name_2818_);
v_cls_2867_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2868_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2869_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2870_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2816_, v_options_2810_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = l_Lean_trace_profiler;
v___x_2966_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2810_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
lean_dec_ref(v___f_2866_);
v___x_2967_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3014_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_3014_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3014_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
if (lean_obj_tag(v_a_2968_) == 1)
{
lean_object* v_val_2972_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; 
lean_del_object(v___x_2970_);
v_val_2972_ = lean_ctor_get(v_a_2968_, 0);
lean_inc(v_val_2972_);
lean_dec_ref_known(v_a_2968_, 1);
if (v___x_2870_ == 0)
{
v___y_2974_ = v_a_2804_;
v___y_2975_ = v_a_2805_;
v___y_2976_ = v_a_2806_;
v___y_2977_ = v_a_2807_;
goto v___jp_2973_;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3006_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2972_);
v___x_3007_ = l_Lean_MessageData_ofExpr(v_val_2972_);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2867_, v___x_3008_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_dec_ref_known(v___x_3009_, 1);
v___y_2974_ = v_a_2804_;
v___y_2975_ = v_a_2805_;
v___y_2976_ = v_a_2806_;
v___y_2977_ = v_a_2807_;
goto v___jp_2973_;
}
else
{
lean_dec(v_val_2972_);
lean_dec(v_name_2818_);
lean_del_object(v___x_2814_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
return v___x_3009_;
}
}
v___jp_2973_:
{
lean_object* v___x_2978_; 
lean_inc(v_val_2972_);
v___x_2978_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2811_, v_val_2972_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2997_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2972_, v___y_2975_);
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2979_, v___y_2975_);
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_2997_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2997_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
lean_inc(v_name_2818_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 2, v_a_2981_);
lean_ctor_set(v___x_2814_, 0, v_name_2818_);
v___x_2988_ = v___x_2814_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_name_2818_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_levelParams_2812_);
lean_ctor_set(v_reuseFailAlloc_2996_, 2, v_a_2981_);
v___x_2988_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2989_ = lean_box(0);
v___x_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2990_, 0, v_name_2818_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2988_);
lean_ctor_set(v___x_2991_, 1, v_a_2983_);
lean_ctor_set(v___x_2991_, 2, v___x_2990_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set_tag(v___x_2985_, 2);
lean_ctor_set(v___x_2985_, 0, v___x_2991_);
v___x_2993_ = v___x_2985_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_addDecl(v___x_2993_, v___x_2966_, v___y_2976_, v___y_2977_);
return v___x_2994_;
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v_val_2972_);
lean_dec(v_name_2818_);
lean_del_object(v___x_2814_);
lean_dec(v_levelParams_2812_);
v_a_2998_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2978_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2978_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
lean_dec(v_a_2968_);
lean_dec(v_name_2818_);
lean_del_object(v___x_2814_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v___x_3010_ = lean_box(0);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_3010_);
v___x_3012_ = v___x_2970_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v_name_2818_);
lean_del_object(v___x_2814_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v_a_3015_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2967_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2967_);
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
else
{
lean_del_object(v___x_2814_);
goto v___jp_2930_;
}
}
else
{
lean_del_object(v___x_2814_);
goto v___jp_2930_;
}
v___jp_2871_:
{
lean_object* v___x_2875_; double v___x_2876_; double v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2875_ = lean_io_get_num_heartbeats();
v___x_2876_ = lean_float_of_nat(v___y_2872_);
v___x_2877_ = lean_float_of_nat(v___x_2875_);
v___x_2878_ = lean_box_float(v___x_2876_);
v___x_2879_ = lean_box_float(v___x_2877_);
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2878_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v_a_2874_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2867_, v_hasTrace_2817_, v___x_2868_, v_options_2810_, v___x_2870_, v___y_2873_, v___f_2866_, v___x_2881_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
return v___x_2882_;
}
v___jp_2883_:
{
lean_object* v___x_2887_; 
v___x_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2887_, 0, v_a_2886_);
v___y_2872_ = v___y_2884_;
v___y_2873_ = v___y_2885_;
v_a_2874_ = v___x_2887_;
goto v___jp_2871_;
}
v___jp_2888_:
{
lean_object* v___x_2892_; 
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_a_2891_);
v___y_2872_ = v___y_2889_;
v___y_2873_ = v___y_2890_;
v_a_2874_ = v___x_2892_;
goto v___jp_2871_;
}
v___jp_2893_:
{
if (lean_obj_tag(v___y_2896_) == 0)
{
lean_object* v_a_2897_; 
v_a_2897_ = lean_ctor_get(v___y_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___y_2896_, 1);
v___y_2889_ = v___y_2894_;
v___y_2890_ = v___y_2895_;
v_a_2891_ = v_a_2897_;
goto v___jp_2888_;
}
else
{
lean_object* v_a_2898_; 
v_a_2898_ = lean_ctor_get(v___y_2896_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___y_2896_, 1);
v___y_2884_ = v___y_2894_;
v___y_2885_ = v___y_2895_;
v_a_2886_ = v_a_2898_;
goto v___jp_2883_;
}
}
v___jp_2899_:
{
lean_object* v___x_2903_; double v___x_2904_; double v___x_2905_; double v___x_2906_; double v___x_2907_; double v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2903_ = lean_io_mono_nanos_now();
v___x_2904_ = lean_float_of_nat(v___y_2900_);
v___x_2905_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2906_ = lean_float_div(v___x_2904_, v___x_2905_);
v___x_2907_ = lean_float_of_nat(v___x_2903_);
v___x_2908_ = lean_float_div(v___x_2907_, v___x_2905_);
v___x_2909_ = lean_box_float(v___x_2906_);
v___x_2910_ = lean_box_float(v___x_2908_);
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2902_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2867_, v_hasTrace_2817_, v___x_2868_, v_options_2810_, v___x_2870_, v___y_2901_, v___f_2866_, v___x_2912_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
return v___x_2913_;
}
v___jp_2914_:
{
lean_object* v___x_2918_; 
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v_a_2917_);
v___y_2900_ = v___y_2915_;
v___y_2901_ = v___y_2916_;
v_a_2902_ = v___x_2918_;
goto v___jp_2899_;
}
v___jp_2919_:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_a_2922_);
v___y_2900_ = v___y_2920_;
v___y_2901_ = v___y_2921_;
v_a_2902_ = v___x_2923_;
goto v___jp_2899_;
}
v___jp_2924_:
{
if (lean_obj_tag(v___y_2927_) == 0)
{
lean_object* v_a_2928_; 
v_a_2928_ = lean_ctor_get(v___y_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___y_2927_, 1);
v___y_2915_ = v___y_2925_;
v___y_2916_ = v___y_2926_;
v_a_2917_ = v_a_2928_;
goto v___jp_2914_;
}
else
{
lean_object* v_a_2929_; 
v_a_2929_ = lean_ctor_get(v___y_2927_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___y_2927_, 1);
v___y_2920_ = v___y_2925_;
v___y_2921_ = v___y_2926_;
v_a_2922_ = v_a_2929_;
goto v___jp_2919_;
}
}
v___jp_2930_:
{
lean_object* v___x_2931_; lean_object* v_a_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v___x_2931_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2807_);
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
v___x_2933_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2934_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2810_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_io_mono_nanos_now();
v___x_2936_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
if (lean_obj_tag(v_a_2937_) == 1)
{
if (v___x_2870_ == 0)
{
lean_object* v_val_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_val_2938_ = lean_ctor_get(v_a_2937_, 0);
lean_inc(v_val_2938_);
lean_dec_ref_known(v_a_2937_, 1);
v___x_2939_ = lean_box(0);
v___x_2940_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2811_, v_val_2938_, v_name_2818_, v_levelParams_2812_, v___x_2934_, v___x_2939_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
v___y_2925_ = v___x_2935_;
v___y_2926_ = v_a_2932_;
v___y_2927_ = v___x_2940_;
goto v___jp_2924_;
}
else
{
lean_object* v_val_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_val_2941_ = lean_ctor_get(v_a_2937_, 0);
lean_inc_n(v_val_2941_, 2);
lean_dec_ref_known(v_a_2937_, 1);
v___x_2942_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2943_ = l_Lean_MessageData_ofExpr(v_val_2941_);
v___x_2944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2867_, v___x_2944_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2811_, v_val_2941_, v_name_2818_, v_levelParams_2812_, v___x_2934_, v_a_2946_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
v___y_2925_ = v___x_2935_;
v___y_2926_ = v_a_2932_;
v___y_2927_ = v___x_2947_;
goto v___jp_2924_;
}
else
{
lean_dec(v_val_2941_);
lean_dec(v_name_2818_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v___y_2925_ = v___x_2935_;
v___y_2926_ = v_a_2932_;
v___y_2927_ = v___x_2945_;
goto v___jp_2924_;
}
}
}
else
{
lean_object* v___x_2948_; 
lean_dec(v_a_2937_);
lean_dec(v_name_2818_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v___x_2948_ = lean_box(0);
v___y_2915_ = v___x_2935_;
v___y_2916_ = v_a_2932_;
v_a_2917_ = v___x_2948_;
goto v___jp_2914_;
}
}
else
{
lean_object* v_a_2949_; 
lean_dec(v_name_2818_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v_a_2949_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2936_, 1);
v___y_2920_ = v___x_2935_;
v___y_2921_ = v_a_2932_;
v_a_2922_ = v_a_2949_;
goto v___jp_2919_;
}
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_io_get_num_heartbeats();
v___x_2951_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
if (lean_obj_tag(v_a_2952_) == 1)
{
if (v___x_2870_ == 0)
{
lean_object* v_val_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_val_2953_ = lean_ctor_get(v_a_2952_, 0);
lean_inc(v_val_2953_);
lean_dec_ref_known(v_a_2952_, 1);
v___x_2954_ = lean_box(0);
v___x_2955_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2811_, v_val_2953_, v_name_2818_, v_levelParams_2812_, v___x_2954_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
v___y_2894_ = v___x_2950_;
v___y_2895_ = v_a_2932_;
v___y_2896_ = v___x_2955_;
goto v___jp_2893_;
}
else
{
lean_object* v_val_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_val_2956_ = lean_ctor_get(v_a_2952_, 0);
lean_inc_n(v_val_2956_, 2);
lean_dec_ref_known(v_a_2952_, 1);
v___x_2957_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2958_ = l_Lean_MessageData_ofExpr(v_val_2956_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2867_, v___x_2959_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2811_, v_val_2956_, v_name_2818_, v_levelParams_2812_, v_a_2961_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
v___y_2894_ = v___x_2950_;
v___y_2895_ = v_a_2932_;
v___y_2896_ = v___x_2962_;
goto v___jp_2893_;
}
else
{
lean_dec(v_val_2956_);
lean_dec(v_name_2818_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v___y_2894_ = v___x_2950_;
v___y_2895_ = v_a_2932_;
v___y_2896_ = v___x_2960_;
goto v___jp_2893_;
}
}
}
else
{
lean_object* v___x_2963_; 
lean_dec(v_a_2952_);
lean_dec(v_name_2818_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v___x_2963_ = lean_box(0);
v___y_2889_ = v___x_2950_;
v___y_2890_ = v_a_2932_;
v_a_2891_ = v___x_2963_;
goto v___jp_2888_;
}
}
else
{
lean_object* v_a_2964_; 
lean_dec(v_name_2818_);
lean_dec(v_levelParams_2812_);
lean_dec(v_name_2811_);
v_a_2964_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2951_, 1);
v___y_2884_ = v___x_2950_;
v___y_2885_ = v_a_2932_;
v_a_2886_ = v_a_2964_;
goto v___jp_2883_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_00_u03b1_3032_, lean_object* v_x_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_3033_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_x_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_00_u03b1_3040_, v_x_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_3051_){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_3053_ = l_Lean_Name_append(v_ctorName_3051_, v___x_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
uint8_t v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = 1;
v___x_3061_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_3054_, v___x_3060_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_3069_, lean_object* v_t_3070_, lean_object* v_acc_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_3070_, v_a_3072_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3098_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3098_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3098_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = l_Lean_Expr_cleanupAnnotations(v_a_3075_);
v___x_3085_ = l_Lean_Expr_isApp(v___x_3084_);
if (v___x_3085_ == 0)
{
lean_dec_ref(v___x_3084_);
goto v___jp_3079_;
}
else
{
lean_object* v_arg_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; 
v_arg_3086_ = lean_ctor_get(v___x_3084_, 1);
lean_inc_ref(v_arg_3086_);
v___x_3087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3084_);
v___x_3088_ = l_Lean_Expr_isApp(v___x_3087_);
if (v___x_3088_ == 0)
{
lean_dec_ref(v___x_3087_);
lean_dec_ref(v_arg_3086_);
goto v___jp_3079_;
}
else
{
lean_object* v_arg_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v_arg_3089_ = lean_ctor_get(v___x_3087_, 1);
lean_inc_ref(v_arg_3089_);
v___x_3090_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3087_);
v___x_3091_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3092_ = l_Lean_Expr_isConstOf(v___x_3090_, v___x_3091_);
lean_dec_ref(v___x_3090_);
if (v___x_3092_ == 0)
{
lean_dec_ref(v_arg_3089_);
lean_dec_ref(v_arg_3086_);
goto v___jp_3079_;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_del_object(v___x_3077_);
v___x_3093_ = lean_unsigned_to_nat(0u);
v___x_3094_ = l_Lean_mkProj(v___x_3091_, v___x_3093_, v_e_3069_);
lean_inc_ref(v___x_3094_);
v___x_3095_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_3094_, v_arg_3089_, v_acc_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v_e_3069_ = v___x_3094_;
v_t_3070_ = v_arg_3086_;
v_acc_3071_ = v_a_3096_;
goto _start;
}
else
{
lean_dec_ref(v___x_3094_);
lean_dec_ref(v_arg_3086_);
return v___x_3095_;
}
}
}
}
v___jp_3079_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = lean_array_push(v_acc_3071_, v_e_3069_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v___x_3080_);
v___x_3082_ = v___x_3077_;
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
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v_acc_3071_);
lean_dec_ref(v_e_3069_);
v_a_3099_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3074_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3074_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_3107_, lean_object* v_t_3108_, lean_object* v_acc_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3107_, v_t_3108_, v_acc_3109_, v_a_3110_);
lean_dec(v_a_3110_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_3113_, lean_object* v_t_3114_, lean_object* v_acc_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3113_, v_t_3114_, v_acc_3115_, v_a_3117_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3122_, lean_object* v_t_3123_, lean_object* v_acc_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3122_, v_t_3123_, v_acc_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___x_3137_; 
lean_inc(v_a_3135_);
lean_inc_ref(v_a_3134_);
lean_inc(v_a_3133_);
lean_inc_ref(v_a_3132_);
lean_inc_ref(v_e_3131_);
v___x_3137_ = lean_infer_type(v_e_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3139_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3140_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3131_, v_a_3138_, v___x_3139_, v_a_3133_);
return v___x_3140_;
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v_e_3131_);
v_a_3141_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3137_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3137_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3156_, lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_){
_start:
{
lean_object* v_ks_3160_; lean_object* v_vs_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3185_; 
v_ks_3160_ = lean_ctor_get(v_x_3156_, 0);
v_vs_3161_ = lean_ctor_get(v_x_3156_, 1);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_x_3156_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3163_ = v_x_3156_;
v_isShared_3164_ = v_isSharedCheck_3185_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_vs_3161_);
lean_inc(v_ks_3160_);
lean_dec(v_x_3156_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3185_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; uint8_t v___x_3166_; 
v___x_3165_ = lean_array_get_size(v_ks_3160_);
v___x_3166_ = lean_nat_dec_lt(v_x_3157_, v___x_3165_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
lean_dec(v_x_3157_);
v___x_3167_ = lean_array_push(v_ks_3160_, v_x_3158_);
v___x_3168_ = lean_array_push(v_vs_3161_, v_x_3159_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3168_);
lean_ctor_set(v___x_3163_, 0, v___x_3167_);
v___x_3170_ = v___x_3163_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
else
{
lean_object* v_k_x27_3172_; uint8_t v___x_3173_; 
v_k_x27_3172_ = lean_array_fget_borrowed(v_ks_3160_, v_x_3157_);
v___x_3173_ = l_Lean_instBEqMVarId_beq(v_x_3158_, v_k_x27_3172_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3175_; 
if (v_isShared_3164_ == 0)
{
v___x_3175_ = v___x_3163_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_ks_3160_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_vs_3161_);
v___x_3175_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_unsigned_to_nat(1u);
v___x_3177_ = lean_nat_add(v_x_3157_, v___x_3176_);
lean_dec(v_x_3157_);
v_x_3156_ = v___x_3175_;
v_x_3157_ = v___x_3177_;
goto _start;
}
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3183_; 
v___x_3180_ = lean_array_fset(v_ks_3160_, v_x_3157_, v_x_3158_);
v___x_3181_ = lean_array_fset(v_vs_3161_, v_x_3157_, v_x_3159_);
lean_dec(v_x_3157_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3181_);
lean_ctor_set(v___x_3163_, 0, v___x_3180_);
v___x_3183_ = v___x_3163_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3186_, lean_object* v_k_3187_, lean_object* v_v_3188_){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_unsigned_to_nat(0u);
v___x_3190_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3186_, v___x_3189_, v_k_3187_, v_v_3188_);
return v___x_3190_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3192_, size_t v_x_3193_, size_t v_x_3194_, lean_object* v_x_3195_, lean_object* v_x_3196_){
_start:
{
if (lean_obj_tag(v_x_3192_) == 0)
{
lean_object* v_es_3197_; size_t v___x_3198_; size_t v___x_3199_; lean_object* v_j_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v_es_3197_ = lean_ctor_get(v_x_3192_, 0);
v___x_3198_ = ((size_t)31ULL);
v___x_3199_ = lean_usize_land(v_x_3193_, v___x_3198_);
v_j_3200_ = lean_usize_to_nat(v___x_3199_);
v___x_3201_ = lean_array_get_size(v_es_3197_);
v___x_3202_ = lean_nat_dec_lt(v_j_3200_, v___x_3201_);
if (v___x_3202_ == 0)
{
lean_dec(v_j_3200_);
lean_dec(v_x_3196_);
lean_dec(v_x_3195_);
return v_x_3192_;
}
else
{
lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3241_; 
lean_inc_ref(v_es_3197_);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_x_3192_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v_x_3192_, 0);
lean_dec(v_unused_3242_);
v___x_3204_ = v_x_3192_;
v_isShared_3205_ = v_isSharedCheck_3241_;
goto v_resetjp_3203_;
}
else
{
lean_dec(v_x_3192_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3241_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v_v_3206_; lean_object* v___x_3207_; lean_object* v_xs_x27_3208_; lean_object* v___y_3210_; 
v_v_3206_ = lean_array_fget(v_es_3197_, v_j_3200_);
v___x_3207_ = lean_box(0);
v_xs_x27_3208_ = lean_array_fset(v_es_3197_, v_j_3200_, v___x_3207_);
switch(lean_obj_tag(v_v_3206_))
{
case 0:
{
lean_object* v_key_3215_; lean_object* v_val_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3226_; 
v_key_3215_ = lean_ctor_get(v_v_3206_, 0);
v_val_3216_ = lean_ctor_get(v_v_3206_, 1);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_v_3206_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3218_ = v_v_3206_;
v_isShared_3219_ = v_isSharedCheck_3226_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_val_3216_);
lean_inc(v_key_3215_);
lean_dec(v_v_3206_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3226_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
uint8_t v___x_3220_; 
v___x_3220_ = l_Lean_instBEqMVarId_beq(v_x_3195_, v_key_3215_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_del_object(v___x_3218_);
v___x_3221_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3215_, v_val_3216_, v_x_3195_, v_x_3196_);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
v___y_3210_ = v___x_3222_;
goto v___jp_3209_;
}
else
{
lean_object* v___x_3224_; 
lean_dec(v_val_3216_);
lean_dec(v_key_3215_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 1, v_x_3196_);
lean_ctor_set(v___x_3218_, 0, v_x_3195_);
v___x_3224_ = v___x_3218_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_x_3195_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_x_3196_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
v___y_3210_ = v___x_3224_;
goto v___jp_3209_;
}
}
}
}
case 1:
{
lean_object* v_node_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3239_; 
v_node_3227_ = lean_ctor_get(v_v_3206_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_v_3206_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3229_ = v_v_3206_;
v_isShared_3230_ = v_isSharedCheck_3239_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_node_3227_);
lean_dec(v_v_3206_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3239_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
size_t v___x_3231_; size_t v___x_3232_; size_t v___x_3233_; size_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3231_ = ((size_t)5ULL);
v___x_3232_ = lean_usize_shift_right(v_x_3193_, v___x_3231_);
v___x_3233_ = ((size_t)1ULL);
v___x_3234_ = lean_usize_add(v_x_3194_, v___x_3233_);
v___x_3235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3227_, v___x_3232_, v___x_3234_, v_x_3195_, v_x_3196_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3235_);
v___x_3237_ = v___x_3229_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
v___y_3210_ = v___x_3237_;
goto v___jp_3209_;
}
}
}
default: 
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v_x_3195_);
lean_ctor_set(v___x_3240_, 1, v_x_3196_);
v___y_3210_ = v___x_3240_;
goto v___jp_3209_;
}
}
v___jp_3209_:
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3211_ = lean_array_fset(v_xs_x27_3208_, v_j_3200_, v___y_3210_);
lean_dec(v_j_3200_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3211_);
v___x_3213_ = v___x_3204_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
else
{
lean_object* v_ks_3243_; lean_object* v_vs_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3264_; 
v_ks_3243_ = lean_ctor_get(v_x_3192_, 0);
v_vs_3244_ = lean_ctor_get(v_x_3192_, 1);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_x_3192_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3246_ = v_x_3192_;
v_isShared_3247_ = v_isSharedCheck_3264_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_vs_3244_);
lean_inc(v_ks_3243_);
lean_dec(v_x_3192_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3264_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_ks_3243_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_vs_3244_);
v___x_3249_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v_newNode_3250_; uint8_t v___y_3252_; size_t v___x_3258_; uint8_t v___x_3259_; 
v_newNode_3250_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3249_, v_x_3195_, v_x_3196_);
v___x_3258_ = ((size_t)7ULL);
v___x_3259_ = lean_usize_dec_le(v___x_3258_, v_x_3194_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v___x_3260_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3250_);
v___x_3261_ = lean_unsigned_to_nat(4u);
v___x_3262_ = lean_nat_dec_lt(v___x_3260_, v___x_3261_);
lean_dec(v___x_3260_);
v___y_3252_ = v___x_3262_;
goto v___jp_3251_;
}
else
{
v___y_3252_ = v___x_3259_;
goto v___jp_3251_;
}
v___jp_3251_:
{
if (v___y_3252_ == 0)
{
lean_object* v_ks_3253_; lean_object* v_vs_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_ks_3253_ = lean_ctor_get(v_newNode_3250_, 0);
lean_inc_ref(v_ks_3253_);
v_vs_3254_ = lean_ctor_get(v_newNode_3250_, 1);
lean_inc_ref(v_vs_3254_);
lean_dec_ref(v_newNode_3250_);
v___x_3255_ = lean_unsigned_to_nat(0u);
v___x_3256_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3194_, v_ks_3253_, v_vs_3254_, v___x_3255_, v___x_3256_);
lean_dec_ref(v_vs_3254_);
lean_dec_ref(v_ks_3253_);
return v___x_3257_;
}
else
{
return v_newNode_3250_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3265_, lean_object* v_keys_3266_, lean_object* v_vals_3267_, lean_object* v_i_3268_, lean_object* v_entries_3269_){
_start:
{
lean_object* v___x_3270_; uint8_t v___x_3271_; 
v___x_3270_ = lean_array_get_size(v_keys_3266_);
v___x_3271_ = lean_nat_dec_lt(v_i_3268_, v___x_3270_);
if (v___x_3271_ == 0)
{
lean_dec(v_i_3268_);
return v_entries_3269_;
}
else
{
lean_object* v_k_3272_; lean_object* v_v_3273_; uint64_t v___x_3274_; size_t v_h_3275_; size_t v___x_3276_; lean_object* v___x_3277_; size_t v___x_3278_; size_t v___x_3279_; size_t v___x_3280_; size_t v_h_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_k_3272_ = lean_array_fget_borrowed(v_keys_3266_, v_i_3268_);
v_v_3273_ = lean_array_fget_borrowed(v_vals_3267_, v_i_3268_);
v___x_3274_ = l_Lean_instHashableMVarId_hash(v_k_3272_);
v_h_3275_ = lean_uint64_to_usize(v___x_3274_);
v___x_3276_ = ((size_t)5ULL);
v___x_3277_ = lean_unsigned_to_nat(1u);
v___x_3278_ = ((size_t)1ULL);
v___x_3279_ = lean_usize_sub(v_depth_3265_, v___x_3278_);
v___x_3280_ = lean_usize_mul(v___x_3276_, v___x_3279_);
v_h_3281_ = lean_usize_shift_right(v_h_3275_, v___x_3280_);
v___x_3282_ = lean_nat_add(v_i_3268_, v___x_3277_);
lean_dec(v_i_3268_);
lean_inc(v_v_3273_);
lean_inc(v_k_3272_);
v___x_3283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3269_, v_h_3281_, v_depth_3265_, v_k_3272_, v_v_3273_);
v_i_3268_ = v___x_3282_;
v_entries_3269_ = v___x_3283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3285_, lean_object* v_keys_3286_, lean_object* v_vals_3287_, lean_object* v_i_3288_, lean_object* v_entries_3289_){
_start:
{
size_t v_depth_boxed_3290_; lean_object* v_res_3291_; 
v_depth_boxed_3290_ = lean_unbox_usize(v_depth_3285_);
lean_dec(v_depth_3285_);
v_res_3291_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3290_, v_keys_3286_, v_vals_3287_, v_i_3288_, v_entries_3289_);
lean_dec_ref(v_vals_3287_);
lean_dec_ref(v_keys_3286_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3292_, lean_object* v_x_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_, lean_object* v_x_3296_){
_start:
{
size_t v_x_5649__boxed_3297_; size_t v_x_5650__boxed_3298_; lean_object* v_res_3299_; 
v_x_5649__boxed_3297_ = lean_unbox_usize(v_x_3293_);
lean_dec(v_x_3293_);
v_x_5650__boxed_3298_ = lean_unbox_usize(v_x_3294_);
lean_dec(v_x_3294_);
v_res_3299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3292_, v_x_5649__boxed_3297_, v_x_5650__boxed_3298_, v_x_3295_, v_x_3296_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3300_, lean_object* v_x_3301_, lean_object* v_x_3302_){
_start:
{
uint64_t v___x_3303_; size_t v___x_3304_; size_t v___x_3305_; lean_object* v___x_3306_; 
v___x_3303_ = l_Lean_instHashableMVarId_hash(v_x_3301_);
v___x_3304_ = lean_uint64_to_usize(v___x_3303_);
v___x_3305_ = ((size_t)1ULL);
v___x_3306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3300_, v___x_3304_, v___x_3305_, v_x_3301_, v_x_3302_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3307_, lean_object* v_val_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; lean_object* v_mctx_3312_; lean_object* v_cache_3313_; lean_object* v_zetaDeltaFVarIds_3314_; lean_object* v_postponed_3315_; lean_object* v_diag_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3345_; 
v___x_3311_ = lean_st_ref_take(v___y_3309_);
v_mctx_3312_ = lean_ctor_get(v___x_3311_, 0);
v_cache_3313_ = lean_ctor_get(v___x_3311_, 1);
v_zetaDeltaFVarIds_3314_ = lean_ctor_get(v___x_3311_, 2);
v_postponed_3315_ = lean_ctor_get(v___x_3311_, 3);
v_diag_3316_ = lean_ctor_get(v___x_3311_, 4);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3318_ = v___x_3311_;
v_isShared_3319_ = v_isSharedCheck_3345_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_diag_3316_);
lean_inc(v_postponed_3315_);
lean_inc(v_zetaDeltaFVarIds_3314_);
lean_inc(v_cache_3313_);
lean_inc(v_mctx_3312_);
lean_dec(v___x_3311_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3345_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v_depth_3320_; lean_object* v_levelAssignDepth_3321_; lean_object* v_lmvarCounter_3322_; lean_object* v_mvarCounter_3323_; lean_object* v_lDecls_3324_; lean_object* v_decls_3325_; lean_object* v_userNames_3326_; lean_object* v_lAssignment_3327_; lean_object* v_eAssignment_3328_; lean_object* v_dAssignment_3329_; lean_object* v_instanceTypedMVars_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3344_; 
v_depth_3320_ = lean_ctor_get(v_mctx_3312_, 0);
v_levelAssignDepth_3321_ = lean_ctor_get(v_mctx_3312_, 1);
v_lmvarCounter_3322_ = lean_ctor_get(v_mctx_3312_, 2);
v_mvarCounter_3323_ = lean_ctor_get(v_mctx_3312_, 3);
v_lDecls_3324_ = lean_ctor_get(v_mctx_3312_, 4);
v_decls_3325_ = lean_ctor_get(v_mctx_3312_, 5);
v_userNames_3326_ = lean_ctor_get(v_mctx_3312_, 6);
v_lAssignment_3327_ = lean_ctor_get(v_mctx_3312_, 7);
v_eAssignment_3328_ = lean_ctor_get(v_mctx_3312_, 8);
v_dAssignment_3329_ = lean_ctor_get(v_mctx_3312_, 9);
v_instanceTypedMVars_3330_ = lean_ctor_get(v_mctx_3312_, 10);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_mctx_3312_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3332_ = v_mctx_3312_;
v_isShared_3333_ = v_isSharedCheck_3344_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_instanceTypedMVars_3330_);
lean_inc(v_dAssignment_3329_);
lean_inc(v_eAssignment_3328_);
lean_inc(v_lAssignment_3327_);
lean_inc(v_userNames_3326_);
lean_inc(v_decls_3325_);
lean_inc(v_lDecls_3324_);
lean_inc(v_mvarCounter_3323_);
lean_inc(v_lmvarCounter_3322_);
lean_inc(v_levelAssignDepth_3321_);
lean_inc(v_depth_3320_);
lean_dec(v_mctx_3312_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3344_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3334_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3328_, v_mvarId_3307_, v_val_3308_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 8, v___x_3334_);
v___x_3336_ = v___x_3332_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_depth_3320_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_levelAssignDepth_3321_);
lean_ctor_set(v_reuseFailAlloc_3343_, 2, v_lmvarCounter_3322_);
lean_ctor_set(v_reuseFailAlloc_3343_, 3, v_mvarCounter_3323_);
lean_ctor_set(v_reuseFailAlloc_3343_, 4, v_lDecls_3324_);
lean_ctor_set(v_reuseFailAlloc_3343_, 5, v_decls_3325_);
lean_ctor_set(v_reuseFailAlloc_3343_, 6, v_userNames_3326_);
lean_ctor_set(v_reuseFailAlloc_3343_, 7, v_lAssignment_3327_);
lean_ctor_set(v_reuseFailAlloc_3343_, 8, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3343_, 9, v_dAssignment_3329_);
lean_ctor_set(v_reuseFailAlloc_3343_, 10, v_instanceTypedMVars_3330_);
v___x_3336_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; 
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3336_);
v___x_3338_ = v___x_3318_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_cache_3313_);
lean_ctor_set(v_reuseFailAlloc_3342_, 2, v_zetaDeltaFVarIds_3314_);
lean_ctor_set(v_reuseFailAlloc_3342_, 3, v_postponed_3315_);
lean_ctor_set(v_reuseFailAlloc_3342_, 4, v_diag_3316_);
v___x_3338_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = lean_st_ref_put(v___y_3309_, v___x_3338_);
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3346_, lean_object* v_val_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3346_, v_val_3347_, v___y_3348_);
lean_dec(v___y_3348_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3351_, lean_object* v_a_3352_, lean_object* v_x_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = lean_box(0);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
lean_inc(v___y_3355_);
lean_inc_ref(v___y_3354_);
v___x_3360_ = lean_apply_7(v___f_3351_, v___x_3359_, v_a_3352_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, lean_box(0));
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3361_, lean_object* v_a_3362_, lean_object* v_x_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3361_, v_a_3362_, v_x_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
return v_res_3369_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0));
v___x_3372_ = l_Lean_stringToMessageData(v___x_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3373_, lean_object* v_a_3374_, lean_object* v_x_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1);
v___x_3382_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3381_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3382_, 1);
lean_inc(v___y_3379_);
lean_inc_ref(v___y_3378_);
lean_inc(v___y_3377_);
lean_inc_ref(v___y_3376_);
v___x_3384_ = lean_apply_7(v___f_3373_, v_a_3383_, v_a_3374_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, lean_box(0));
return v___x_3384_;
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec(v_a_3374_);
lean_dec_ref(v___f_3373_);
v_a_3385_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3382_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3382_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3393_, lean_object* v_a_3394_, lean_object* v_x_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3393_, v_a_3394_, v_x_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v_x_3395_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3402_, lean_object* v_____r_3403_, lean_object* v_mvarId_u2082_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3404_, v___x_3402_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3420_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3420_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3420_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v_snd_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v_snd_3415_ = lean_ctor_get(v_a_3411_, 1);
lean_inc(v_snd_3415_);
lean_dec(v_a_3411_);
v___x_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3416_, 0, v_snd_3415_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3416_);
v___x_3418_ = v___x_3413_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
v_a_3421_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3410_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3410_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3429_, lean_object* v_____r_3430_, lean_object* v_mvarId_u2082_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
uint8_t v___x_5941__boxed_3437_; lean_object* v_res_3438_; 
v___x_5941__boxed_3437_ = lean_unbox(v___x_3429_);
v_res_3438_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5941__boxed_3437_, v_____r_3430_, v_mvarId_u2082_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
return v_res_3438_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_box(0);
v___x_3445_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2));
v___x_3446_ = l_Lean_mkConst(v___x_3445_, v___x_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v___y_3454_; lean_object* v___x_3474_; 
lean_inc(v_a_3447_);
v___x_3474_ = l_Lean_MVarId_getType(v_a_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3534_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3534_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3534_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
if (lean_obj_tag(v_a_3475_) == 7)
{
lean_object* v_binderType_3479_; lean_object* v_body_3480_; uint8_t v___x_3481_; 
v_binderType_3479_ = lean_ctor_get(v_a_3475_, 1);
lean_inc_ref(v_binderType_3479_);
v_body_3480_ = lean_ctor_get(v_a_3475_, 2);
lean_inc_ref(v_body_3480_);
lean_dec_ref_known(v_a_3475_, 3);
v___x_3481_ = l_Lean_Expr_hasLooseBVars(v_body_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
lean_del_object(v___x_3477_);
v___x_3482_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3479_, v___y_3449_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3484_; lean_object* v___f_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
lean_dec_ref_known(v___x_3482_, 1);
v___x_3484_ = lean_box(v___x_3481_);
v___f_3485_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3485_, 0, v___x_3484_);
v___x_3486_ = l_Lean_Expr_cleanupAnnotations(v_a_3483_);
v___x_3487_ = l_Lean_Expr_isApp(v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec_ref(v___x_3486_);
lean_dec_ref(v_body_3480_);
v___x_3488_ = lean_box(0);
v___x_3489_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3485_, v_a_3447_, v___x_3488_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
v___y_3454_ = v___x_3489_;
goto v___jp_3453_;
}
else
{
lean_object* v_arg_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v_arg_3490_ = lean_ctor_get(v___x_3486_, 1);
lean_inc_ref(v_arg_3490_);
v___x_3491_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3486_);
v___x_3492_ = l_Lean_Expr_isApp(v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_dec_ref(v___x_3491_);
lean_dec_ref(v_arg_3490_);
lean_dec_ref(v_body_3480_);
v___x_3493_ = lean_box(0);
v___x_3494_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3485_, v_a_3447_, v___x_3493_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
v___y_3454_ = v___x_3494_;
goto v___jp_3453_;
}
else
{
lean_object* v_arg_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v_arg_3495_ = lean_ctor_get(v___x_3491_, 1);
lean_inc_ref(v_arg_3495_);
v___x_3496_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3491_);
v___x_3497_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3498_ = l_Lean_Expr_isConstOf(v___x_3496_, v___x_3497_);
lean_dec_ref(v___x_3496_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_dec_ref(v_arg_3495_);
lean_dec_ref(v_arg_3490_);
lean_dec_ref(v_body_3480_);
v___x_3499_ = lean_box(0);
v___x_3500_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3485_, v_a_3447_, v___x_3499_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
v___y_3454_ = v___x_3500_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3501_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3);
v___x_3502_ = l_Lean_mkApp3(v___x_3501_, v_arg_3495_, v_arg_3490_, v_body_3480_);
v___x_3503_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3447_);
v___x_3504_ = l_Lean_MVarId_applyN(v_a_3447_, v___x_3502_, v___x_3503_, v___x_3498_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3504_, 1);
if (lean_obj_tag(v_a_3505_) == 1)
{
lean_object* v_tail_3506_; 
v_tail_3506_ = lean_ctor_get(v_a_3505_, 1);
if (lean_obj_tag(v_tail_3506_) == 0)
{
lean_object* v_head_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
lean_dec_ref(v___f_3485_);
lean_dec(v_a_3447_);
v_head_3507_ = lean_ctor_get(v_a_3505_, 0);
lean_inc(v_head_3507_);
lean_dec_ref_known(v_a_3505_, 2);
v___x_3508_ = lean_box(0);
v___x_3509_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3481_, v___x_3508_, v_head_3507_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
v___y_3454_ = v___x_3509_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3510_; 
v___x_3510_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3485_, v_a_3447_, v_a_3505_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec_ref_known(v_a_3505_, 2);
v___y_3454_ = v___x_3510_;
goto v___jp_3453_;
}
}
else
{
lean_object* v___x_3511_; 
v___x_3511_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3485_, v_a_3447_, v_a_3505_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v_a_3505_);
v___y_3454_ = v___x_3511_;
goto v___jp_3453_;
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v___f_3485_);
lean_dec(v_a_3447_);
v_a_3512_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3504_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3504_);
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
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v_body_3480_);
lean_dec(v_a_3447_);
v_a_3520_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3482_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3482_);
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
}
else
{
lean_object* v___x_3529_; 
lean_dec_ref(v_body_3480_);
lean_dec_ref(v_binderType_3479_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v_a_3447_);
v___x_3529_ = v___x_3477_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3447_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
else
{
lean_object* v___x_3532_; 
lean_dec(v_a_3475_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v_a_3447_);
v___x_3532_ = v___x_3477_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3447_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec(v_a_3447_);
v_a_3535_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3474_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3474_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
v___jp_3453_:
{
if (lean_obj_tag(v___y_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3465_; 
v_a_3455_ = lean_ctor_get(v___y_3454_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___y_3454_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3457_ = v___y_3454_;
v_isShared_3458_ = v_isSharedCheck_3465_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___y_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3465_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
if (lean_obj_tag(v_a_3455_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; 
v_a_3459_ = lean_ctor_get(v_a_3455_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v_a_3455_, 1);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v_a_3459_);
v___x_3461_ = v___x_3457_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
else
{
lean_object* v_a_3463_; 
lean_del_object(v___x_3457_);
v_a_3463_ = lean_ctor_get(v_a_3455_, 0);
lean_inc(v_a_3463_);
lean_dec_ref_known(v_a_3455_, 1);
v_a_3447_ = v_a_3463_;
goto _start;
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
v_a_3466_ = lean_ctor_get(v___y_3454_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___y_3454_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___y_3454_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___y_3454_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
return v_res_3549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = lean_box(0);
v___x_3556_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3557_ = l_Lean_mkConst(v___x_3556_, v___x_3555_);
return v___x_3557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3565_, lean_object* v_xs_3566_, lean_object* v_type_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = lean_box(0);
v___x_3574_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3567_, v___x_3573_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; uint8_t v___x_3580_; lean_object* v___y_3582_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3574_, 1);
v___x_3576_ = l_Lean_Expr_mvarId_x21(v_a_3575_);
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3579_ = 1;
v___x_3580_ = 0;
v___x_3593_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3594_ = lean_box(0);
v___x_3595_ = l_Lean_MVarId_apply(v___x_3576_, v___x_3578_, v___x_3593_, v___x_3594_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3595_, 1);
if (lean_obj_tag(v_a_3596_) == 1)
{
lean_object* v_tail_3610_; 
v_tail_3610_ = lean_ctor_get(v_a_3596_, 1);
lean_inc(v_tail_3610_);
if (lean_obj_tag(v_tail_3610_) == 1)
{
lean_object* v_tail_3611_; 
v_tail_3611_ = lean_ctor_get(v_tail_3610_, 1);
if (lean_obj_tag(v_tail_3611_) == 0)
{
lean_object* v_toConstantVal_3612_; lean_object* v_head_3613_; lean_object* v_head_3614_; lean_object* v_name_3615_; lean_object* v_levelParams_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v_toConstantVal_3612_ = lean_ctor_get(v_ctorVal_3565_, 0);
lean_inc_ref(v_toConstantVal_3612_);
lean_dec_ref(v_ctorVal_3565_);
v_head_3613_ = lean_ctor_get(v_a_3596_, 0);
lean_inc(v_head_3613_);
lean_dec_ref_known(v_a_3596_, 2);
v_head_3614_ = lean_ctor_get(v_tail_3610_, 0);
lean_inc(v_head_3614_);
lean_dec_ref_known(v_tail_3610_, 2);
v_name_3615_ = lean_ctor_get(v_toConstantVal_3612_, 0);
lean_inc_n(v_name_3615_, 2);
v_levelParams_3616_ = lean_ctor_get(v_toConstantVal_3612_, 1);
lean_inc(v_levelParams_3616_);
lean_dec_ref(v_toConstantVal_3612_);
v___x_3617_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3615_);
v___x_3618_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3616_, v___x_3577_);
v___x_3619_ = l_Lean_mkConst(v___x_3617_, v___x_3618_);
v___x_3620_ = l_Lean_mkAppN(v___x_3619_, v_xs_3566_);
v___x_3621_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3613_, v___x_3620_, v___y_3569_);
lean_dec_ref(v___x_3621_);
v___x_3622_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3614_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3624_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
v___x_3624_ = l_Lean_MVarId_refl(v_a_3623_, v___x_3579_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_dec(v_name_3615_);
v___y_3582_ = v___x_3624_;
goto v___jp_3581_;
}
else
{
lean_object* v_a_3625_; uint8_t v___y_3627_; uint8_t v___x_3630_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
v___x_3630_ = l_Lean_Exception_isInterrupt(v_a_3625_);
if (v___x_3630_ == 0)
{
uint8_t v___x_3631_; 
v___x_3631_ = l_Lean_Exception_isRuntime(v_a_3625_);
v___y_3627_ = v___x_3631_;
goto v___jp_3626_;
}
else
{
lean_dec(v_a_3625_);
v___y_3627_ = v___x_3630_;
goto v___jp_3626_;
}
v___jp_3626_:
{
if (v___y_3627_ == 0)
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
lean_dec_ref_known(v___x_3624_, 1);
v___x_3628_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3615_);
v___x_3629_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3628_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
v___y_3582_ = v___x_3629_;
goto v___jp_3581_;
}
else
{
lean_dec(v_name_3615_);
v___y_3582_ = v___x_3624_;
goto v___jp_3581_;
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_name_3615_);
lean_dec(v_a_3575_);
v_a_3632_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3622_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3622_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3610_, 2);
lean_dec_ref_known(v_a_3596_, 2);
lean_dec(v_a_3575_);
v___y_3598_ = v___y_3568_;
v___y_3599_ = v___y_3569_;
v___y_3600_ = v___y_3570_;
v___y_3601_ = v___y_3571_;
goto v___jp_3597_;
}
}
else
{
lean_dec_ref_known(v_a_3596_, 2);
lean_dec(v_tail_3610_);
lean_dec(v_a_3575_);
v___y_3598_ = v___y_3568_;
v___y_3599_ = v___y_3569_;
v___y_3600_ = v___y_3570_;
v___y_3601_ = v___y_3571_;
goto v___jp_3597_;
}
}
else
{
lean_dec(v_a_3596_);
lean_dec(v_a_3575_);
v___y_3598_ = v___y_3568_;
v___y_3599_ = v___y_3569_;
v___y_3600_ = v___y_3570_;
v___y_3601_ = v___y_3571_;
goto v___jp_3597_;
}
v___jp_3597_:
{
lean_object* v_toConstantVal_3602_; lean_object* v_name_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_toConstantVal_3602_ = lean_ctor_get(v_ctorVal_3565_, 0);
lean_inc_ref(v_toConstantVal_3602_);
lean_dec_ref(v_ctorVal_3565_);
v_name_3603_ = lean_ctor_get(v_toConstantVal_3602_, 0);
lean_inc(v_name_3603_);
lean_dec_ref(v_toConstantVal_3602_);
v___x_3604_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3605_ = l_Lean_MessageData_ofName(v_name_3603_);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3608_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3609_;
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec(v_a_3575_);
lean_dec_ref(v_ctorVal_3565_);
v_a_3640_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3595_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3595_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
v___jp_3581_:
{
if (lean_obj_tag(v___y_3582_) == 0)
{
uint8_t v___x_3583_; lean_object* v___x_3584_; 
lean_dec_ref_known(v___y_3582_, 1);
v___x_3583_ = 1;
v___x_3584_ = l_Lean_Meta_mkLambdaFVars(v_xs_3566_, v_a_3575_, v___x_3580_, v___x_3579_, v___x_3580_, v___x_3579_, v___x_3583_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
return v___x_3584_;
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec(v_a_3575_);
v_a_3585_ = lean_ctor_get(v___y_3582_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___y_3582_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___y_3582_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___y_3582_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorVal_3565_);
return v___x_3574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3648_, lean_object* v_xs_3649_, lean_object* v_type_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3648_, v_xs_3649_, v_type_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_xs_3649_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3657_, lean_object* v_targetType_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v___f_3664_; uint8_t v___x_3665_; lean_object* v___x_3666_; 
v___f_3664_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3664_, 0, v_ctorVal_3657_);
v___x_3665_ = 0;
v___x_3666_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3658_, v___f_3664_, v___x_3665_, v___x_3665_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3667_, lean_object* v_targetType_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3667_, v_targetType_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3675_, lean_object* v_val_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3675_, v_val_3676_, v___y_3678_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3683_, lean_object* v_val_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3683_, v_val_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3691_, lean_object* v_a_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3699_, lean_object* v_a_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3699_, v_a_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3707_, lean_object* v_x_3708_, lean_object* v_x_3709_, lean_object* v_x_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3708_, v_x_3709_, v_x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3712_, lean_object* v_x_3713_, size_t v_x_3714_, size_t v_x_3715_, lean_object* v_x_3716_, lean_object* v_x_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3713_, v_x_3714_, v_x_3715_, v_x_3716_, v_x_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3719_, lean_object* v_x_3720_, lean_object* v_x_3721_, lean_object* v_x_3722_, lean_object* v_x_3723_, lean_object* v_x_3724_){
_start:
{
size_t v_x_6492__boxed_3725_; size_t v_x_6493__boxed_3726_; lean_object* v_res_3727_; 
v_x_6492__boxed_3725_ = lean_unbox_usize(v_x_3721_);
lean_dec(v_x_3721_);
v_x_6493__boxed_3726_ = lean_unbox_usize(v_x_3722_);
lean_dec(v_x_3722_);
v_res_3727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3719_, v_x_3720_, v_x_6492__boxed_3725_, v_x_6493__boxed_3726_, v_x_3723_, v_x_3724_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3728_, lean_object* v_n_3729_, lean_object* v_k_3730_, lean_object* v_v_3731_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3729_, v_k_3730_, v_v_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3733_, size_t v_depth_3734_, lean_object* v_keys_3735_, lean_object* v_vals_3736_, lean_object* v_heq_3737_, lean_object* v_i_3738_, lean_object* v_entries_3739_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3734_, v_keys_3735_, v_vals_3736_, v_i_3738_, v_entries_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3741_, lean_object* v_depth_3742_, lean_object* v_keys_3743_, lean_object* v_vals_3744_, lean_object* v_heq_3745_, lean_object* v_i_3746_, lean_object* v_entries_3747_){
_start:
{
size_t v_depth_boxed_3748_; lean_object* v_res_3749_; 
v_depth_boxed_3748_ = lean_unbox_usize(v_depth_3742_);
lean_dec(v_depth_3742_);
v_res_3749_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3741_, v_depth_boxed_3748_, v_keys_3743_, v_vals_3744_, v_heq_3745_, v_i_3746_, v_entries_3747_);
lean_dec_ref(v_vals_3744_);
lean_dec_ref(v_keys_3743_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3750_, lean_object* v_x_3751_, lean_object* v_x_3752_, lean_object* v_x_3753_, lean_object* v_x_3754_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3751_, v_x_3752_, v_x_3753_, v_x_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3756_, lean_object* v_val_3757_, lean_object* v_name_3758_, lean_object* v_levelParams_3759_, uint8_t v___x_3760_, uint8_t v_hasTrace_3761_, lean_object* v_____r_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v___x_3768_; 
lean_inc_ref(v_val_3757_);
v___x_3768_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3756_, v_val_3757_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3770_; lean_object* v_a_3771_; lean_object* v___x_3772_; lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3789_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v___x_3768_, 1);
v___x_3770_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3757_, v___y_3764_);
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3769_, v___y_3764_);
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3775_ = v___x_3772_;
v_isShared_3776_ = v_isSharedCheck_3789_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3772_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3789_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_inc_n(v_name_3758_, 2);
v___x_3777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3777_, 0, v_name_3758_);
lean_ctor_set(v___x_3777_, 1, v_levelParams_3759_);
lean_ctor_set(v___x_3777_, 2, v_a_3771_);
v___x_3778_ = lean_box(0);
v___x_3779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3779_, 0, v_name_3758_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3777_);
lean_ctor_set(v___x_3780_, 1, v_a_3773_);
lean_ctor_set(v___x_3780_, 2, v___x_3779_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set_tag(v___x_3775_, 2);
lean_ctor_set(v___x_3775_, 0, v___x_3780_);
v___x_3782_ = v___x_3775_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; 
v___x_3783_ = l_Lean_addDecl(v___x_3782_, v___x_3760_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v___x_3784_; uint8_t v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_dec_ref_known(v___x_3783_, 1);
v___x_3784_ = l_Lean_Meta_simpExtension;
v___x_3785_ = 0;
v___x_3786_ = lean_unsigned_to_nat(1000u);
v___x_3787_ = l_Lean_Meta_addSimpTheorem(v___x_3784_, v_name_3758_, v_hasTrace_3761_, v___x_3760_, v___x_3785_, v___x_3786_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
return v___x_3787_;
}
else
{
lean_dec(v_name_3758_);
return v___x_3783_;
}
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec(v_levelParams_3759_);
lean_dec(v_name_3758_);
lean_dec_ref(v_val_3757_);
v_a_3790_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3768_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3768_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3798_, lean_object* v_val_3799_, lean_object* v_name_3800_, lean_object* v_levelParams_3801_, lean_object* v___x_3802_, lean_object* v_hasTrace_3803_, lean_object* v_____r_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
uint8_t v___x_9095__boxed_3810_; uint8_t v_hasTrace_boxed_3811_; lean_object* v_res_3812_; 
v___x_9095__boxed_3810_ = lean_unbox(v___x_3802_);
v_hasTrace_boxed_3811_ = lean_unbox(v_hasTrace_3803_);
v_res_3812_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3798_, v_val_3799_, v_name_3800_, v_levelParams_3801_, v___x_9095__boxed_3810_, v_hasTrace_boxed_3811_, v_____r_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3813_, lean_object* v_val_3814_, lean_object* v_name_3815_, lean_object* v_levelParams_3816_, uint8_t v___x_3817_, lean_object* v_____r_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v___x_3824_; 
lean_inc_ref(v_val_3814_);
v___x_3824_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3813_, v_val_3814_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3826_; lean_object* v_a_3827_; lean_object* v___x_3828_; lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3846_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___x_3826_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3814_, v___y_3820_);
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref(v___x_3826_);
v___x_3828_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3825_, v___y_3820_);
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3846_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3846_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3838_; 
lean_inc_n(v_name_3815_, 2);
v___x_3833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3833_, 0, v_name_3815_);
lean_ctor_set(v___x_3833_, 1, v_levelParams_3816_);
lean_ctor_set(v___x_3833_, 2, v_a_3827_);
v___x_3834_ = lean_box(0);
v___x_3835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3835_, 0, v_name_3815_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
v___x_3836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3833_);
lean_ctor_set(v___x_3836_, 1, v_a_3829_);
lean_ctor_set(v___x_3836_, 2, v___x_3835_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set_tag(v___x_3831_, 2);
lean_ctor_set(v___x_3831_, 0, v___x_3836_);
v___x_3838_ = v___x_3831_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
uint8_t v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = 0;
v___x_3840_ = l_Lean_addDecl(v___x_3838_, v___x_3839_, v___y_3821_, v___y_3822_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v___x_3841_; uint8_t v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_dec_ref_known(v___x_3840_, 1);
v___x_3841_ = l_Lean_Meta_simpExtension;
v___x_3842_ = 0;
v___x_3843_ = lean_unsigned_to_nat(1000u);
v___x_3844_ = l_Lean_Meta_addSimpTheorem(v___x_3841_, v_name_3815_, v___x_3817_, v___x_3839_, v___x_3842_, v___x_3843_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
return v___x_3844_;
}
else
{
lean_dec(v_name_3815_);
return v___x_3840_;
}
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec(v_levelParams_3816_);
lean_dec(v_name_3815_);
lean_dec_ref(v_val_3814_);
v_a_3847_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3824_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3824_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3855_, lean_object* v_val_3856_, lean_object* v_name_3857_, lean_object* v_levelParams_3858_, lean_object* v___x_3859_, lean_object* v_____r_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
uint8_t v___x_9183__boxed_3866_; lean_object* v_res_3867_; 
v___x_9183__boxed_3866_ = lean_unbox(v___x_3859_);
v_res_3867_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3855_, v_val_3856_, v_name_3857_, v_levelParams_3858_, v___x_9183__boxed_3866_, v_____r_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_toConstantVal_3874_; lean_object* v_options_3875_; lean_object* v_name_3876_; lean_object* v_levelParams_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_4097_; 
v_toConstantVal_3874_ = lean_ctor_get(v_ctorVal_3868_, 0);
lean_inc_ref(v_toConstantVal_3874_);
v_options_3875_ = lean_ctor_get(v_a_3871_, 2);
v_name_3876_ = lean_ctor_get(v_toConstantVal_3874_, 0);
v_levelParams_3877_ = lean_ctor_get(v_toConstantVal_3874_, 1);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_toConstantVal_3874_);
if (v_isSharedCheck_4097_ == 0)
{
lean_object* v_unused_4098_; 
v_unused_4098_ = lean_ctor_get(v_toConstantVal_3874_, 2);
lean_dec(v_unused_4098_);
v___x_3879_ = v_toConstantVal_3874_;
v_isShared_3880_ = v_isSharedCheck_4097_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_levelParams_3877_);
lean_inc(v_name_3876_);
lean_dec(v_toConstantVal_3874_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_4097_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v_inheritedTraceOptions_3881_; uint8_t v_hasTrace_3882_; lean_object* v_name_3883_; 
v_inheritedTraceOptions_3881_ = lean_ctor_get(v_a_3871_, 13);
v_hasTrace_3882_ = lean_ctor_get_uint8(v_options_3875_, sizeof(void*)*1);
v_name_3883_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3876_);
if (v_hasTrace_3882_ == 0)
{
lean_object* v___x_3884_; 
lean_inc_ref(v_ctorVal_3868_);
v___x_3884_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3927_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3887_ = v___x_3884_;
v_isShared_3888_ = v_isSharedCheck_3927_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3927_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
if (lean_obj_tag(v_a_3885_) == 1)
{
lean_object* v_val_3889_; lean_object* v___x_3890_; 
lean_del_object(v___x_3887_);
v_val_3889_ = lean_ctor_get(v_a_3885_, 0);
lean_inc_n(v_val_3889_, 2);
lean_dec_ref_known(v_a_3885_, 1);
v___x_3890_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3868_, v_val_3889_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3892_; lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3914_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v___x_3892_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3889_, v_a_3870_);
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref(v___x_3892_);
v___x_3894_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3891_, v_a_3870_);
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3897_ = v___x_3894_;
v_isShared_3898_ = v_isSharedCheck_3914_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3914_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
lean_inc(v_name_3883_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 2, v_a_3893_);
lean_ctor_set(v___x_3879_, 0, v_name_3883_);
v___x_3900_ = v___x_3879_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_name_3883_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v_levelParams_3877_);
lean_ctor_set(v_reuseFailAlloc_3913_, 2, v_a_3893_);
v___x_3900_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3901_ = lean_box(0);
lean_inc(v_name_3883_);
v___x_3902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3902_, 0, v_name_3883_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3900_);
lean_ctor_set(v___x_3903_, 1, v_a_3895_);
lean_ctor_set(v___x_3903_, 2, v___x_3902_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set_tag(v___x_3897_, 2);
lean_ctor_set(v___x_3897_, 0, v___x_3903_);
v___x_3905_ = v___x_3897_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_addDecl(v___x_3905_, v_hasTrace_3882_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v___x_3907_; uint8_t v___x_3908_; uint8_t v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec_ref_known(v___x_3906_, 1);
v___x_3907_ = l_Lean_Meta_simpExtension;
v___x_3908_ = 1;
v___x_3909_ = 0;
v___x_3910_ = lean_unsigned_to_nat(1000u);
v___x_3911_ = l_Lean_Meta_addSimpTheorem(v___x_3907_, v_name_3883_, v___x_3908_, v_hasTrace_3882_, v___x_3909_, v___x_3910_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
return v___x_3911_;
}
else
{
lean_dec(v_name_3883_);
return v___x_3906_;
}
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v_val_3889_);
lean_dec(v_name_3883_);
lean_del_object(v___x_3879_);
lean_dec(v_levelParams_3877_);
v_a_3915_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3890_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3890_);
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
else
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
lean_dec(v_a_3885_);
lean_dec(v_name_3883_);
lean_del_object(v___x_3879_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v___x_3923_ = lean_box(0);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v___x_3923_);
v___x_3925_ = v___x_3887_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec(v_name_3883_);
lean_del_object(v___x_3879_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v_a_3928_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3884_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3884_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
else
{
lean_object* v___f_3936_; lean_object* v_cls_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; uint8_t v___x_3940_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v_a_3944_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v_a_3956_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v_a_3961_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v_a_3972_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v_a_3987_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v_a_3992_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; 
lean_inc(v_name_3883_);
v___f_3936_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3936_, 0, v_name_3883_);
v_cls_3937_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3938_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3939_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3940_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3881_, v_options_3875_, v___x_3939_);
if (v___x_3940_ == 0)
{
lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4035_ = l_Lean_trace_profiler;
v___x_4036_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3875_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; 
lean_dec_ref(v___f_3936_);
lean_inc_ref(v_ctorVal_3868_);
v___x_4037_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4088_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4040_ = v___x_4037_;
v_isShared_4041_ = v_isSharedCheck_4088_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4088_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
if (lean_obj_tag(v_a_4038_) == 1)
{
lean_object* v_val_4042_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; 
lean_del_object(v___x_4040_);
v_val_4042_ = lean_ctor_get(v_a_4038_, 0);
lean_inc(v_val_4042_);
lean_dec_ref_known(v_a_4038_, 1);
if (v___x_3940_ == 0)
{
v___y_4044_ = v_a_3869_;
v___y_4045_ = v_a_3870_;
v___y_4046_ = v_a_3871_;
v___y_4047_ = v_a_3872_;
goto v___jp_4043_;
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4080_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_4042_);
v___x_4081_ = l_Lean_MessageData_ofExpr(v_val_4042_);
v___x_4082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4080_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3937_, v___x_4082_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_dec_ref_known(v___x_4083_, 1);
v___y_4044_ = v_a_3869_;
v___y_4045_ = v_a_3870_;
v___y_4046_ = v_a_3871_;
v___y_4047_ = v_a_3872_;
goto v___jp_4043_;
}
else
{
lean_dec(v_val_4042_);
lean_dec(v_name_3883_);
lean_del_object(v___x_3879_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
return v___x_4083_;
}
}
v___jp_4043_:
{
lean_object* v___x_4048_; 
lean_inc(v_val_4042_);
v___x_4048_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3868_, v_val_4042_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4050_; lean_object* v_a_4051_; lean_object* v___x_4052_; lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4071_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref_known(v___x_4048_, 1);
v___x_4050_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_4042_, v___y_4045_);
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref(v___x_4050_);
v___x_4052_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_4049_, v___y_4045_);
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4071_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4071_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
lean_inc(v_name_3883_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 2, v_a_4051_);
lean_ctor_set(v___x_3879_, 0, v_name_3883_);
v___x_4058_ = v___x_3879_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_name_3883_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_levelParams_3877_);
lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_a_4051_);
v___x_4058_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4063_; 
v___x_4059_ = lean_box(0);
lean_inc(v_name_3883_);
v___x_4060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4060_, 0, v_name_3883_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
v___x_4061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4058_);
lean_ctor_set(v___x_4061_, 1, v_a_4053_);
lean_ctor_set(v___x_4061_, 2, v___x_4060_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set_tag(v___x_4055_, 2);
lean_ctor_set(v___x_4055_, 0, v___x_4061_);
v___x_4063_ = v___x_4055_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4064_; 
v___x_4064_ = l_Lean_addDecl(v___x_4063_, v___x_4036_, v___y_4046_, v___y_4047_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v___x_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; 
lean_dec_ref_known(v___x_4064_, 1);
v___x_4065_ = l_Lean_Meta_simpExtension;
v___x_4066_ = 0;
v___x_4067_ = lean_unsigned_to_nat(1000u);
v___x_4068_ = l_Lean_Meta_addSimpTheorem(v___x_4065_, v_name_3883_, v_hasTrace_3882_, v___x_4036_, v___x_4066_, v___x_4067_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
return v___x_4068_;
}
else
{
lean_dec(v_name_3883_);
return v___x_4064_;
}
}
}
}
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4079_; 
lean_dec(v_val_4042_);
lean_dec(v_name_3883_);
lean_del_object(v___x_3879_);
lean_dec(v_levelParams_3877_);
v_a_4072_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4074_ = v___x_4048_;
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4048_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
}
else
{
lean_object* v___x_4084_; lean_object* v___x_4086_; 
lean_dec(v_a_4038_);
lean_dec(v_name_3883_);
lean_del_object(v___x_3879_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v___x_4084_ = lean_box(0);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4084_);
v___x_4086_ = v___x_4040_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4084_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v_name_3883_);
lean_del_object(v___x_3879_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v_a_4089_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4037_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4037_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
else
{
lean_del_object(v___x_3879_);
goto v___jp_4000_;
}
}
else
{
lean_del_object(v___x_3879_);
goto v___jp_4000_;
}
v___jp_3941_:
{
lean_object* v___x_3945_; double v___x_3946_; double v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3945_ = lean_io_get_num_heartbeats();
v___x_3946_ = lean_float_of_nat(v___y_3943_);
v___x_3947_ = lean_float_of_nat(v___x_3945_);
v___x_3948_ = lean_box_float(v___x_3946_);
v___x_3949_ = lean_box_float(v___x_3947_);
v___x_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3951_, 0, v_a_3944_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3937_, v_hasTrace_3882_, v___x_3938_, v_options_3875_, v___x_3940_, v___y_3942_, v___f_3936_, v___x_3951_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
return v___x_3952_;
}
v___jp_3953_:
{
lean_object* v___x_3957_; 
v___x_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3957_, 0, v_a_3956_);
v___y_3942_ = v___y_3954_;
v___y_3943_ = v___y_3955_;
v_a_3944_ = v___x_3957_;
goto v___jp_3941_;
}
v___jp_3958_:
{
lean_object* v___x_3962_; 
v___x_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3962_, 0, v_a_3961_);
v___y_3942_ = v___y_3959_;
v___y_3943_ = v___y_3960_;
v_a_3944_ = v___x_3962_;
goto v___jp_3941_;
}
v___jp_3963_:
{
if (lean_obj_tag(v___y_3966_) == 0)
{
lean_object* v_a_3967_; 
v_a_3967_ = lean_ctor_get(v___y_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___y_3966_, 1);
v___y_3959_ = v___y_3964_;
v___y_3960_ = v___y_3965_;
v_a_3961_ = v_a_3967_;
goto v___jp_3958_;
}
else
{
lean_object* v_a_3968_; 
v_a_3968_ = lean_ctor_get(v___y_3966_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v___y_3966_, 1);
v___y_3954_ = v___y_3964_;
v___y_3955_ = v___y_3965_;
v_a_3956_ = v_a_3968_;
goto v___jp_3953_;
}
}
v___jp_3969_:
{
lean_object* v___x_3973_; double v___x_3974_; double v___x_3975_; double v___x_3976_; double v___x_3977_; double v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3973_ = lean_io_mono_nanos_now();
v___x_3974_ = lean_float_of_nat(v___y_3971_);
v___x_3975_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3976_ = lean_float_div(v___x_3974_, v___x_3975_);
v___x_3977_ = lean_float_of_nat(v___x_3973_);
v___x_3978_ = lean_float_div(v___x_3977_, v___x_3975_);
v___x_3979_ = lean_box_float(v___x_3976_);
v___x_3980_ = lean_box_float(v___x_3978_);
v___x_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3979_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v_a_3972_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3937_, v_hasTrace_3882_, v___x_3938_, v_options_3875_, v___x_3940_, v___y_3970_, v___f_3936_, v___x_3982_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
return v___x_3983_;
}
v___jp_3984_:
{
lean_object* v___x_3988_; 
v___x_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3988_, 0, v_a_3987_);
v___y_3970_ = v___y_3985_;
v___y_3971_ = v___y_3986_;
v_a_3972_ = v___x_3988_;
goto v___jp_3969_;
}
v___jp_3989_:
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3993_, 0, v_a_3992_);
v___y_3970_ = v___y_3990_;
v___y_3971_ = v___y_3991_;
v_a_3972_ = v___x_3993_;
goto v___jp_3969_;
}
v___jp_3994_:
{
if (lean_obj_tag(v___y_3997_) == 0)
{
lean_object* v_a_3998_; 
v_a_3998_ = lean_ctor_get(v___y_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v___y_3997_, 1);
v___y_3985_ = v___y_3995_;
v___y_3986_ = v___y_3996_;
v_a_3987_ = v_a_3998_;
goto v___jp_3984_;
}
else
{
lean_object* v_a_3999_; 
v_a_3999_ = lean_ctor_get(v___y_3997_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___y_3997_, 1);
v___y_3990_ = v___y_3995_;
v___y_3991_ = v___y_3996_;
v_a_3992_ = v_a_3999_;
goto v___jp_3989_;
}
}
v___jp_4000_:
{
lean_object* v___x_4001_; lean_object* v_a_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v___x_4001_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3872_);
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref(v___x_4001_);
v___x_4003_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4004_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3875_, v___x_4003_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3868_);
v___x_4006_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
if (lean_obj_tag(v_a_4007_) == 1)
{
if (v___x_3940_ == 0)
{
lean_object* v_val_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v_val_4008_ = lean_ctor_get(v_a_4007_, 0);
lean_inc(v_val_4008_);
lean_dec_ref_known(v_a_4007_, 1);
v___x_4009_ = lean_box(0);
v___x_4010_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3868_, v_val_4008_, v_name_3883_, v_levelParams_3877_, v___x_4004_, v_hasTrace_3882_, v___x_4009_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
v___y_3995_ = v_a_4002_;
v___y_3996_ = v___x_4005_;
v___y_3997_ = v___x_4010_;
goto v___jp_3994_;
}
else
{
lean_object* v_val_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
v_val_4011_ = lean_ctor_get(v_a_4007_, 0);
lean_inc_n(v_val_4011_, 2);
lean_dec_ref_known(v_a_4007_, 1);
v___x_4012_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_4013_ = l_Lean_MessageData_ofExpr(v_val_4011_);
v___x_4014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4012_);
lean_ctor_set(v___x_4014_, 1, v___x_4013_);
v___x_4015_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3937_, v___x_4014_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4017_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
v___x_4017_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3868_, v_val_4011_, v_name_3883_, v_levelParams_3877_, v___x_4004_, v_hasTrace_3882_, v_a_4016_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
v___y_3995_ = v_a_4002_;
v___y_3996_ = v___x_4005_;
v___y_3997_ = v___x_4017_;
goto v___jp_3994_;
}
else
{
lean_dec(v_val_4011_);
lean_dec(v_name_3883_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v___y_3995_ = v_a_4002_;
v___y_3996_ = v___x_4005_;
v___y_3997_ = v___x_4015_;
goto v___jp_3994_;
}
}
}
else
{
lean_object* v___x_4018_; 
lean_dec(v_a_4007_);
lean_dec(v_name_3883_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v___x_4018_ = lean_box(0);
v___y_3985_ = v_a_4002_;
v___y_3986_ = v___x_4005_;
v_a_3987_ = v___x_4018_;
goto v___jp_3984_;
}
}
else
{
lean_object* v_a_4019_; 
lean_dec(v_name_3883_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v_a_4019_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4019_);
lean_dec_ref_known(v___x_4006_, 1);
v___y_3990_ = v_a_4002_;
v___y_3991_ = v___x_4005_;
v_a_3992_ = v_a_4019_;
goto v___jp_3989_;
}
}
else
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3868_);
v___x_4021_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
if (lean_obj_tag(v_a_4022_) == 1)
{
if (v___x_3940_ == 0)
{
lean_object* v_val_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v_val_4023_ = lean_ctor_get(v_a_4022_, 0);
lean_inc(v_val_4023_);
lean_dec_ref_known(v_a_4022_, 1);
v___x_4024_ = lean_box(0);
v___x_4025_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3868_, v_val_4023_, v_name_3883_, v_levelParams_3877_, v___x_4004_, v___x_4024_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
v___y_3964_ = v_a_4002_;
v___y_3965_ = v___x_4020_;
v___y_3966_ = v___x_4025_;
goto v___jp_3963_;
}
else
{
lean_object* v_val_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_val_4026_ = lean_ctor_get(v_a_4022_, 0);
lean_inc_n(v_val_4026_, 2);
lean_dec_ref_known(v_a_4022_, 1);
v___x_4027_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_4028_ = l_Lean_MessageData_ofExpr(v_val_4026_);
v___x_4029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4027_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3937_, v___x_4029_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4032_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4030_, 1);
v___x_4032_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3868_, v_val_4026_, v_name_3883_, v_levelParams_3877_, v___x_4004_, v_a_4031_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
v___y_3964_ = v_a_4002_;
v___y_3965_ = v___x_4020_;
v___y_3966_ = v___x_4032_;
goto v___jp_3963_;
}
else
{
lean_dec(v_val_4026_);
lean_dec(v_name_3883_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v___y_3964_ = v_a_4002_;
v___y_3965_ = v___x_4020_;
v___y_3966_ = v___x_4030_;
goto v___jp_3963_;
}
}
}
else
{
lean_object* v___x_4033_; 
lean_dec(v_a_4022_);
lean_dec(v_name_3883_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v___x_4033_ = lean_box(0);
v___y_3959_ = v_a_4002_;
v___y_3960_ = v___x_4020_;
v_a_3961_ = v___x_4033_;
goto v___jp_3958_;
}
}
else
{
lean_object* v_a_4034_; 
lean_dec(v_name_3883_);
lean_dec(v_levelParams_3877_);
lean_dec_ref(v_ctorVal_3868_);
v_a_4034_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4021_, 1);
v___y_3954_ = v_a_4002_;
v___y_3955_ = v___x_4020_;
v_a_3956_ = v_a_4034_;
goto v___jp_3953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_4106_, lean_object* v_decl_4107_, lean_object* v_ref_4108_){
_start:
{
lean_object* v_defValue_4110_; lean_object* v_descr_4111_; lean_object* v_deprecation_x3f_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v_defValue_4110_ = lean_ctor_get(v_decl_4107_, 0);
v_descr_4111_ = lean_ctor_get(v_decl_4107_, 1);
v_deprecation_x3f_4112_ = lean_ctor_get(v_decl_4107_, 2);
v___x_4113_ = lean_alloc_ctor(1, 0, 1);
v___x_4114_ = lean_unbox(v_defValue_4110_);
lean_ctor_set_uint8(v___x_4113_, 0, v___x_4114_);
lean_inc(v_deprecation_x3f_4112_);
lean_inc_ref(v_descr_4111_);
lean_inc_n(v_name_4106_, 2);
v___x_4115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4115_, 0, v_name_4106_);
lean_ctor_set(v___x_4115_, 1, v_ref_4108_);
lean_ctor_set(v___x_4115_, 2, v___x_4113_);
lean_ctor_set(v___x_4115_, 3, v_descr_4111_);
lean_ctor_set(v___x_4115_, 4, v_deprecation_x3f_4112_);
v___x_4116_ = lean_register_option(v_name_4106_, v___x_4115_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4124_; 
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4124_ == 0)
{
lean_object* v_unused_4125_; 
v_unused_4125_ = lean_ctor_get(v___x_4116_, 0);
lean_dec(v_unused_4125_);
v___x_4118_ = v___x_4116_;
v_isShared_4119_ = v_isSharedCheck_4124_;
goto v_resetjp_4117_;
}
else
{
lean_dec(v___x_4116_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4124_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4120_; lean_object* v___x_4122_; 
lean_inc(v_defValue_4110_);
v___x_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4120_, 0, v_name_4106_);
lean_ctor_set(v___x_4120_, 1, v_defValue_4110_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4120_);
v___x_4122_ = v___x_4118_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec(v_name_4106_);
v_a_4126_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4116_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4116_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4134_, lean_object* v_decl_4135_, lean_object* v_ref_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4134_, v_decl_4135_, v_ref_4136_);
lean_dec_ref(v_decl_4135_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4153_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4154_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4155_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4156_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4153_, v___x_4154_, v___x_4155_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4159_, uint8_t v_isExporting_4160_, lean_object* v___x_4161_, lean_object* v___y_4162_, lean_object* v___x_4163_, lean_object* v_a_x3f_4164_){
_start:
{
lean_object* v___x_4166_; lean_object* v_env_4167_; lean_object* v_nextMacroScope_4168_; lean_object* v_ngen_4169_; lean_object* v_auxDeclNGen_4170_; lean_object* v_traceState_4171_; lean_object* v_messages_4172_; lean_object* v_infoState_4173_; lean_object* v_snapshotTasks_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4199_; 
v___x_4166_ = lean_st_ref_take(v___y_4159_);
v_env_4167_ = lean_ctor_get(v___x_4166_, 0);
v_nextMacroScope_4168_ = lean_ctor_get(v___x_4166_, 1);
v_ngen_4169_ = lean_ctor_get(v___x_4166_, 2);
v_auxDeclNGen_4170_ = lean_ctor_get(v___x_4166_, 3);
v_traceState_4171_ = lean_ctor_get(v___x_4166_, 4);
v_messages_4172_ = lean_ctor_get(v___x_4166_, 6);
v_infoState_4173_ = lean_ctor_get(v___x_4166_, 7);
v_snapshotTasks_4174_ = lean_ctor_get(v___x_4166_, 8);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4199_ == 0)
{
lean_object* v_unused_4200_; 
v_unused_4200_ = lean_ctor_get(v___x_4166_, 5);
lean_dec(v_unused_4200_);
v___x_4176_ = v___x_4166_;
v_isShared_4177_ = v_isSharedCheck_4199_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_snapshotTasks_4174_);
lean_inc(v_infoState_4173_);
lean_inc(v_messages_4172_);
lean_inc(v_traceState_4171_);
lean_inc(v_auxDeclNGen_4170_);
lean_inc(v_ngen_4169_);
lean_inc(v_nextMacroScope_4168_);
lean_inc(v_env_4167_);
lean_dec(v___x_4166_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4199_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4178_; lean_object* v___x_4180_; 
v___x_4178_ = l_Lean_Environment_setExporting(v_env_4167_, v_isExporting_4160_);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 5, v___x_4161_);
lean_ctor_set(v___x_4176_, 0, v___x_4178_);
v___x_4180_ = v___x_4176_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4178_);
lean_ctor_set(v_reuseFailAlloc_4198_, 1, v_nextMacroScope_4168_);
lean_ctor_set(v_reuseFailAlloc_4198_, 2, v_ngen_4169_);
lean_ctor_set(v_reuseFailAlloc_4198_, 3, v_auxDeclNGen_4170_);
lean_ctor_set(v_reuseFailAlloc_4198_, 4, v_traceState_4171_);
lean_ctor_set(v_reuseFailAlloc_4198_, 5, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4198_, 6, v_messages_4172_);
lean_ctor_set(v_reuseFailAlloc_4198_, 7, v_infoState_4173_);
lean_ctor_set(v_reuseFailAlloc_4198_, 8, v_snapshotTasks_4174_);
v___x_4180_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v_mctx_4183_; lean_object* v_zetaDeltaFVarIds_4184_; lean_object* v_postponed_4185_; lean_object* v_diag_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4196_; 
v___x_4181_ = lean_st_ref_put(v___y_4159_, v___x_4180_);
v___x_4182_ = lean_st_ref_take(v___y_4162_);
v_mctx_4183_ = lean_ctor_get(v___x_4182_, 0);
v_zetaDeltaFVarIds_4184_ = lean_ctor_get(v___x_4182_, 2);
v_postponed_4185_ = lean_ctor_get(v___x_4182_, 3);
v_diag_4186_ = lean_ctor_get(v___x_4182_, 4);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4196_ == 0)
{
lean_object* v_unused_4197_; 
v_unused_4197_ = lean_ctor_get(v___x_4182_, 1);
lean_dec(v_unused_4197_);
v___x_4188_ = v___x_4182_;
v_isShared_4189_ = v_isSharedCheck_4196_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_diag_4186_);
lean_inc(v_postponed_4185_);
lean_inc(v_zetaDeltaFVarIds_4184_);
lean_inc(v_mctx_4183_);
lean_dec(v___x_4182_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4196_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 1, v___x_4163_);
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_mctx_4183_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v___x_4163_);
lean_ctor_set(v_reuseFailAlloc_4195_, 2, v_zetaDeltaFVarIds_4184_);
lean_ctor_set(v_reuseFailAlloc_4195_, 3, v_postponed_4185_);
lean_ctor_set(v_reuseFailAlloc_4195_, 4, v_diag_4186_);
v___x_4191_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4192_ = lean_st_ref_put(v___y_4162_, v___x_4191_);
v___x_4193_ = lean_box(0);
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4201_, lean_object* v_isExporting_4202_, lean_object* v___x_4203_, lean_object* v___y_4204_, lean_object* v___x_4205_, lean_object* v_a_x3f_4206_, lean_object* v___y_4207_){
_start:
{
uint8_t v_isExporting_boxed_4208_; lean_object* v_res_4209_; 
v_isExporting_boxed_4208_ = lean_unbox(v_isExporting_4202_);
v_res_4209_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4201_, v_isExporting_boxed_4208_, v___x_4203_, v___y_4204_, v___x_4205_, v_a_x3f_4206_);
lean_dec(v_a_x3f_4206_);
lean_dec(v___y_4204_);
lean_dec(v___y_4201_);
return v_res_4209_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4210_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4211_);
return v___x_4212_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4216_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
lean_ctor_set(v___x_4216_, 2, v___x_4215_);
lean_ctor_set(v___x_4216_, 3, v___x_4215_);
lean_ctor_set(v___x_4216_, 4, v___x_4215_);
lean_ctor_set(v___x_4216_, 5, v___x_4215_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4217_, uint8_t v_isExporting_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; lean_object* v_env_4225_; uint8_t v_isExporting_4226_; lean_object* v___x_4292_; uint8_t v_isModule_4293_; 
v___x_4224_ = lean_st_ref_get(v___y_4222_);
v_env_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc_ref(v_env_4225_);
lean_dec(v___x_4224_);
v_isExporting_4226_ = lean_ctor_get_uint8(v_env_4225_, sizeof(void*)*8);
v___x_4292_ = l_Lean_Environment_header(v_env_4225_);
lean_dec_ref(v_env_4225_);
v_isModule_4293_ = lean_ctor_get_uint8(v___x_4292_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4292_);
if (v_isModule_4293_ == 0)
{
lean_object* v___x_4294_; 
lean_inc(v___y_4222_);
lean_inc_ref(v___y_4221_);
lean_inc(v___y_4220_);
lean_inc_ref(v___y_4219_);
v___x_4294_ = lean_apply_5(v_x_4217_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, lean_box(0));
return v___x_4294_;
}
else
{
if (v_isExporting_4226_ == 0)
{
if (v_isExporting_4218_ == 0)
{
lean_object* v___x_4295_; 
lean_inc(v___y_4222_);
lean_inc_ref(v___y_4221_);
lean_inc(v___y_4220_);
lean_inc_ref(v___y_4219_);
v___x_4295_ = lean_apply_5(v_x_4217_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, lean_box(0));
return v___x_4295_;
}
else
{
goto v___jp_4227_;
}
}
else
{
if (v_isExporting_4218_ == 0)
{
goto v___jp_4227_;
}
else
{
lean_object* v___x_4296_; 
lean_inc(v___y_4222_);
lean_inc_ref(v___y_4221_);
lean_inc(v___y_4220_);
lean_inc_ref(v___y_4219_);
v___x_4296_ = lean_apply_5(v_x_4217_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, lean_box(0));
return v___x_4296_;
}
}
}
v___jp_4227_:
{
lean_object* v___x_4228_; lean_object* v_env_4229_; lean_object* v_nextMacroScope_4230_; lean_object* v_ngen_4231_; lean_object* v_auxDeclNGen_4232_; lean_object* v_traceState_4233_; lean_object* v_messages_4234_; lean_object* v_infoState_4235_; lean_object* v_snapshotTasks_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4290_; 
v___x_4228_ = lean_st_ref_take(v___y_4222_);
v_env_4229_ = lean_ctor_get(v___x_4228_, 0);
v_nextMacroScope_4230_ = lean_ctor_get(v___x_4228_, 1);
v_ngen_4231_ = lean_ctor_get(v___x_4228_, 2);
v_auxDeclNGen_4232_ = lean_ctor_get(v___x_4228_, 3);
v_traceState_4233_ = lean_ctor_get(v___x_4228_, 4);
v_messages_4234_ = lean_ctor_get(v___x_4228_, 6);
v_infoState_4235_ = lean_ctor_get(v___x_4228_, 7);
v_snapshotTasks_4236_ = lean_ctor_get(v___x_4228_, 8);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4290_ == 0)
{
lean_object* v_unused_4291_; 
v_unused_4291_ = lean_ctor_get(v___x_4228_, 5);
lean_dec(v_unused_4291_);
v___x_4238_ = v___x_4228_;
v_isShared_4239_ = v_isSharedCheck_4290_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_snapshotTasks_4236_);
lean_inc(v_infoState_4235_);
lean_inc(v_messages_4234_);
lean_inc(v_traceState_4233_);
lean_inc(v_auxDeclNGen_4232_);
lean_inc(v_ngen_4231_);
lean_inc(v_nextMacroScope_4230_);
lean_inc(v_env_4229_);
lean_dec(v___x_4228_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4290_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
v___x_4240_ = l_Lean_Environment_setExporting(v_env_4229_, v_isExporting_4218_);
v___x_4241_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 5, v___x_4241_);
lean_ctor_set(v___x_4238_, 0, v___x_4240_);
v___x_4243_ = v___x_4238_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4240_);
lean_ctor_set(v_reuseFailAlloc_4289_, 1, v_nextMacroScope_4230_);
lean_ctor_set(v_reuseFailAlloc_4289_, 2, v_ngen_4231_);
lean_ctor_set(v_reuseFailAlloc_4289_, 3, v_auxDeclNGen_4232_);
lean_ctor_set(v_reuseFailAlloc_4289_, 4, v_traceState_4233_);
lean_ctor_set(v_reuseFailAlloc_4289_, 5, v___x_4241_);
lean_ctor_set(v_reuseFailAlloc_4289_, 6, v_messages_4234_);
lean_ctor_set(v_reuseFailAlloc_4289_, 7, v_infoState_4235_);
lean_ctor_set(v_reuseFailAlloc_4289_, 8, v_snapshotTasks_4236_);
v___x_4243_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v_mctx_4246_; lean_object* v_zetaDeltaFVarIds_4247_; lean_object* v_postponed_4248_; lean_object* v_diag_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4287_; 
v___x_4244_ = lean_st_ref_put(v___y_4222_, v___x_4243_);
v___x_4245_ = lean_st_ref_take(v___y_4220_);
v_mctx_4246_ = lean_ctor_get(v___x_4245_, 0);
v_zetaDeltaFVarIds_4247_ = lean_ctor_get(v___x_4245_, 2);
v_postponed_4248_ = lean_ctor_get(v___x_4245_, 3);
v_diag_4249_ = lean_ctor_get(v___x_4245_, 4);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4287_ == 0)
{
lean_object* v_unused_4288_; 
v_unused_4288_ = lean_ctor_get(v___x_4245_, 1);
lean_dec(v_unused_4288_);
v___x_4251_ = v___x_4245_;
v_isShared_4252_ = v_isSharedCheck_4287_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_diag_4249_);
lean_inc(v_postponed_4248_);
lean_inc(v_zetaDeltaFVarIds_4247_);
lean_inc(v_mctx_4246_);
lean_dec(v___x_4245_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4287_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4253_; lean_object* v___x_4255_; 
v___x_4253_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 1, v___x_4253_);
v___x_4255_ = v___x_4251_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_mctx_4246_);
lean_ctor_set(v_reuseFailAlloc_4286_, 1, v___x_4253_);
lean_ctor_set(v_reuseFailAlloc_4286_, 2, v_zetaDeltaFVarIds_4247_);
lean_ctor_set(v_reuseFailAlloc_4286_, 3, v_postponed_4248_);
lean_ctor_set(v_reuseFailAlloc_4286_, 4, v_diag_4249_);
v___x_4255_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
lean_object* v___x_4256_; lean_object* v_r_4257_; 
v___x_4256_ = lean_st_ref_put(v___y_4220_, v___x_4255_);
lean_inc(v___y_4222_);
lean_inc_ref(v___y_4221_);
lean_inc(v___y_4220_);
lean_inc_ref(v___y_4219_);
v_r_4257_ = lean_apply_5(v_x_4217_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, lean_box(0));
if (lean_obj_tag(v_r_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4274_; 
v_a_4258_ = lean_ctor_get(v_r_4257_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v_r_4257_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4260_ = v_r_4257_;
v_isShared_4261_ = v_isSharedCheck_4274_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v_r_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4274_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
lean_inc(v_a_4258_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set_tag(v___x_4260_, 1);
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
lean_object* v___x_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
v___x_4264_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4222_, v_isExporting_4226_, v___x_4241_, v___y_4220_, v___x_4253_, v___x_4263_);
lean_dec_ref(v___x_4263_);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4271_ == 0)
{
lean_object* v_unused_4272_; 
v_unused_4272_ = lean_ctor_get(v___x_4264_, 0);
lean_dec(v_unused_4272_);
v___x_4266_ = v___x_4264_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_dec(v___x_4264_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 0, v_a_4258_);
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4258_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
v_a_4275_ = lean_ctor_get(v_r_4257_, 0);
lean_inc(v_a_4275_);
lean_dec_ref_known(v_r_4257_, 1);
v___x_4276_ = lean_box(0);
v___x_4277_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4222_, v_isExporting_4226_, v___x_4241_, v___y_4220_, v___x_4253_, v___x_4276_);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4284_ == 0)
{
lean_object* v_unused_4285_; 
v_unused_4285_ = lean_ctor_get(v___x_4277_, 0);
lean_dec(v_unused_4285_);
v___x_4279_ = v___x_4277_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_dec(v___x_4277_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
lean_ctor_set_tag(v___x_4279_, 1);
lean_ctor_set(v___x_4279_, 0, v_a_4275_);
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4275_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4297_, lean_object* v_isExporting_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
uint8_t v_isExporting_boxed_4304_; lean_object* v_res_4305_; 
v_isExporting_boxed_4304_ = lean_unbox(v_isExporting_4298_);
v_res_4305_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4297_, v_isExporting_boxed_4304_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4306_, lean_object* v_x_4307_, uint8_t v_isExporting_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4307_, v_isExporting_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4315_, lean_object* v_x_4316_, lean_object* v_isExporting_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
uint8_t v_isExporting_boxed_4323_; lean_object* v_res_4324_; 
v_isExporting_boxed_4323_ = lean_unbox(v_isExporting_4317_);
v_res_4324_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4315_, v_x_4316_, v_isExporting_boxed_4323_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4325_, lean_object* v_localInsts_4326_, lean_object* v_x_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4325_, v_localInsts_4326_, v_x_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4333_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
v_a_4342_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4333_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4333_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4350_, lean_object* v_localInsts_4351_, lean_object* v_x_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4350_, v_localInsts_4351_, v_x_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4359_, lean_object* v_lctx_4360_, lean_object* v_localInsts_4361_, lean_object* v_x_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v___x_4368_; 
v___x_4368_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4360_, v_localInsts_4361_, v_x_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4369_, lean_object* v_lctx_4370_, lean_object* v_localInsts_4371_, lean_object* v_x_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4369_, v_lctx_4370_, v_localInsts_4371_, v_x_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4379_, lean_object* v_x_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = l_Lean_MessageData_ofName(v_declName_4379_);
v___x_4387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4388_, lean_object* v_x_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4388_, v_x_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec_ref(v_x_4389_);
return v_res_4395_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = l_instMonadEIO(lean_box(0));
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v_toApplicative_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4470_; 
v___x_4407_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4408_ = l_StateRefT_x27_instMonad___redArg(v___x_4407_);
v_toApplicative_4409_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4470_ == 0)
{
lean_object* v_unused_4471_; 
v_unused_4471_ = lean_ctor_get(v___x_4408_, 1);
lean_dec(v_unused_4471_);
v___x_4411_ = v___x_4408_;
v_isShared_4412_ = v_isSharedCheck_4470_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_toApplicative_4409_);
lean_dec(v___x_4408_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4470_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v_toFunctor_4413_; lean_object* v_toSeq_4414_; lean_object* v_toSeqLeft_4415_; lean_object* v_toSeqRight_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4468_; 
v_toFunctor_4413_ = lean_ctor_get(v_toApplicative_4409_, 0);
v_toSeq_4414_ = lean_ctor_get(v_toApplicative_4409_, 2);
v_toSeqLeft_4415_ = lean_ctor_get(v_toApplicative_4409_, 3);
v_toSeqRight_4416_ = lean_ctor_get(v_toApplicative_4409_, 4);
v_isSharedCheck_4468_ = !lean_is_exclusive(v_toApplicative_4409_);
if (v_isSharedCheck_4468_ == 0)
{
lean_object* v_unused_4469_; 
v_unused_4469_ = lean_ctor_get(v_toApplicative_4409_, 1);
lean_dec(v_unused_4469_);
v___x_4418_ = v_toApplicative_4409_;
v_isShared_4419_ = v_isSharedCheck_4468_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_toSeqRight_4416_);
lean_inc(v_toSeqLeft_4415_);
lean_inc(v_toSeq_4414_);
lean_inc(v_toFunctor_4413_);
lean_dec(v_toApplicative_4409_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4468_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___f_4420_; lean_object* v___f_4421_; lean_object* v___f_4422_; lean_object* v___f_4423_; lean_object* v___x_4424_; lean_object* v___f_4425_; lean_object* v___f_4426_; lean_object* v___f_4427_; lean_object* v___x_4429_; 
v___f_4420_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4421_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4413_);
v___f_4422_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4422_, 0, v_toFunctor_4413_);
v___f_4423_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4423_, 0, v_toFunctor_4413_);
v___x_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4424_, 0, v___f_4422_);
lean_ctor_set(v___x_4424_, 1, v___f_4423_);
v___f_4425_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4425_, 0, v_toSeqRight_4416_);
v___f_4426_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4426_, 0, v_toSeqLeft_4415_);
v___f_4427_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4427_, 0, v_toSeq_4414_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 4, v___f_4425_);
lean_ctor_set(v___x_4418_, 3, v___f_4426_);
lean_ctor_set(v___x_4418_, 2, v___f_4427_);
lean_ctor_set(v___x_4418_, 1, v___f_4420_);
lean_ctor_set(v___x_4418_, 0, v___x_4424_);
v___x_4429_ = v___x_4418_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4467_, 1, v___f_4420_);
lean_ctor_set(v_reuseFailAlloc_4467_, 2, v___f_4427_);
lean_ctor_set(v_reuseFailAlloc_4467_, 3, v___f_4426_);
lean_ctor_set(v_reuseFailAlloc_4467_, 4, v___f_4425_);
v___x_4429_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
lean_object* v___x_4431_; 
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 1, v___f_4421_);
lean_ctor_set(v___x_4411_, 0, v___x_4429_);
v___x_4431_ = v___x_4411_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4429_);
lean_ctor_set(v_reuseFailAlloc_4466_, 1, v___f_4421_);
v___x_4431_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4432_; lean_object* v_toApplicative_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4464_; 
v___x_4432_ = l_StateRefT_x27_instMonad___redArg(v___x_4431_);
v_toApplicative_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4464_ == 0)
{
lean_object* v_unused_4465_; 
v_unused_4465_ = lean_ctor_get(v___x_4432_, 1);
lean_dec(v_unused_4465_);
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4464_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_toApplicative_4433_);
lean_dec(v___x_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4464_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v_toFunctor_4437_; lean_object* v_toSeq_4438_; lean_object* v_toSeqLeft_4439_; lean_object* v_toSeqRight_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4462_; 
v_toFunctor_4437_ = lean_ctor_get(v_toApplicative_4433_, 0);
v_toSeq_4438_ = lean_ctor_get(v_toApplicative_4433_, 2);
v_toSeqLeft_4439_ = lean_ctor_get(v_toApplicative_4433_, 3);
v_toSeqRight_4440_ = lean_ctor_get(v_toApplicative_4433_, 4);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_toApplicative_4433_);
if (v_isSharedCheck_4462_ == 0)
{
lean_object* v_unused_4463_; 
v_unused_4463_ = lean_ctor_get(v_toApplicative_4433_, 1);
lean_dec(v_unused_4463_);
v___x_4442_ = v_toApplicative_4433_;
v_isShared_4443_ = v_isSharedCheck_4462_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_toSeqRight_4440_);
lean_inc(v_toSeqLeft_4439_);
lean_inc(v_toSeq_4438_);
lean_inc(v_toFunctor_4437_);
lean_dec(v_toApplicative_4433_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4462_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___f_4444_; lean_object* v___f_4445_; lean_object* v___f_4446_; lean_object* v___f_4447_; lean_object* v___x_4448_; lean_object* v___f_4449_; lean_object* v___f_4450_; lean_object* v___f_4451_; lean_object* v___x_4453_; 
v___f_4444_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4445_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4437_);
v___f_4446_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4446_, 0, v_toFunctor_4437_);
v___f_4447_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4447_, 0, v_toFunctor_4437_);
v___x_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___f_4446_);
lean_ctor_set(v___x_4448_, 1, v___f_4447_);
v___f_4449_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4449_, 0, v_toSeqRight_4440_);
v___f_4450_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4450_, 0, v_toSeqLeft_4439_);
v___f_4451_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4451_, 0, v_toSeq_4438_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 4, v___f_4449_);
lean_ctor_set(v___x_4442_, 3, v___f_4450_);
lean_ctor_set(v___x_4442_, 2, v___f_4451_);
lean_ctor_set(v___x_4442_, 1, v___f_4444_);
lean_ctor_set(v___x_4442_, 0, v___x_4448_);
v___x_4453_ = v___x_4442_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4448_);
lean_ctor_set(v_reuseFailAlloc_4461_, 1, v___f_4444_);
lean_ctor_set(v_reuseFailAlloc_4461_, 2, v___f_4451_);
lean_ctor_set(v_reuseFailAlloc_4461_, 3, v___f_4450_);
lean_ctor_set(v_reuseFailAlloc_4461_, 4, v___f_4449_);
v___x_4453_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4455_; 
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 1, v___f_4445_);
lean_ctor_set(v___x_4435_, 0, v___x_4453_);
v___x_4455_ = v___x_4435_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4453_);
lean_ctor_set(v_reuseFailAlloc_4460_, 1, v___f_4445_);
v___x_4455_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_19120__overap_4458_; lean_object* v___x_4459_; 
v___x_4456_ = lean_box(0);
v___x_4457_ = l_instInhabitedOfMonad___redArg(v___x_4455_, v___x_4456_);
v___x_19120__overap_4458_ = lean_panic_fn_borrowed(v___x_4457_, v_msg_4401_);
lean_dec(v___x_4457_);
lean_inc(v___y_4405_);
lean_inc_ref(v___y_4404_);
lean_inc(v___y_4403_);
lean_inc_ref(v___y_4402_);
v___x_4459_ = lean_apply_5(v___x_19120__overap_4458_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, lean_box(0));
return v___x_4459_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
return v_res_4478_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4480_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4481_ = l_Lean_stringToMessageData(v___x_4480_);
return v___x_4481_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4484_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4485_ = lean_unsigned_to_nat(11u);
v___x_4486_ = lean_unsigned_to_nat(122u);
v___x_4487_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4488_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4489_ = l_mkPanicMessageWithDecl(v___x_4488_, v___x_4487_, v___x_4486_, v___x_4485_, v___x_4484_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4504_; lean_object* v_env_4505_; uint8_t v___x_4506_; lean_object* v___x_4507_; 
v___x_4504_ = lean_st_ref_get(v___y_4494_);
v_env_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc_ref(v_env_4505_);
lean_dec(v___x_4504_);
v___x_4506_ = 0;
lean_inc(v_constName_4490_);
v___x_4507_ = l_Lean_Environment_findAsync_x3f(v_env_4505_, v_constName_4490_, v___x_4506_);
if (lean_obj_tag(v___x_4507_) == 1)
{
lean_object* v_val_4508_; uint8_t v_kind_4509_; 
v_val_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_val_4508_);
lean_dec_ref_known(v___x_4507_, 1);
v_kind_4509_ = lean_ctor_get_uint8(v_val_4508_, sizeof(void*)*3);
if (v_kind_4509_ == 6)
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4508_);
if (lean_obj_tag(v___x_4510_) == 6)
{
lean_object* v_val_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4518_; 
lean_dec(v_constName_4490_);
v_val_4511_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4513_ = v___x_4510_;
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_val_4511_);
lean_dec(v___x_4510_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
lean_ctor_set_tag(v___x_4513_, 0);
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_val_4511_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
else
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
lean_dec_ref(v___x_4510_);
v___x_4519_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4520_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4519_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4529_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4523_ = v___x_4520_;
v_isShared_4524_ = v_isSharedCheck_4529_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4520_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4529_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
if (lean_obj_tag(v_a_4521_) == 0)
{
lean_del_object(v___x_4523_);
goto v___jp_4496_;
}
else
{
lean_object* v_val_4525_; lean_object* v___x_4527_; 
lean_dec(v_constName_4490_);
v_val_4525_ = lean_ctor_get(v_a_4521_, 0);
lean_inc(v_val_4525_);
lean_dec_ref_known(v_a_4521_, 1);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v_val_4525_);
v___x_4527_ = v___x_4523_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_val_4525_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
lean_dec(v_constName_4490_);
v_a_4530_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4520_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4520_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
}
else
{
lean_dec(v_val_4508_);
goto v___jp_4496_;
}
}
else
{
lean_dec(v___x_4507_);
goto v___jp_4496_;
}
v___jp_4496_:
{
lean_object* v___x_4497_; uint8_t v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4497_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4498_ = 0;
v___x_4499_ = l_Lean_MessageData_ofConstName(v_constName_4490_, v___x_4498_);
v___x_4500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4497_);
lean_ctor_set(v___x_4500_, 1, v___x_4499_);
v___x_4501_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4500_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
v___x_4503_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4502_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
return v___x_4503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4545_, lean_object* v___x_4546_, lean_object* v___x_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4545_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4565_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4556_ = v___x_4553_;
v_isShared_4557_ = v_isSharedCheck_4565_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4553_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4565_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v_numFields_4558_; uint8_t v___x_4559_; 
v_numFields_4558_ = lean_ctor_get(v_a_4554_, 4);
v___x_4559_ = lean_nat_dec_lt(v___x_4546_, v_numFields_4558_);
if (v___x_4559_ == 0)
{
lean_object* v___x_4561_; 
lean_dec(v_a_4554_);
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 0, v___x_4547_);
v___x_4561_ = v___x_4556_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4547_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
else
{
lean_object* v___x_4563_; 
lean_del_object(v___x_4556_);
lean_inc(v_a_4554_);
v___x_4563_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4554_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v___x_4564_; 
lean_dec_ref_known(v___x_4563_, 1);
v___x_4564_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4554_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
return v___x_4564_;
}
else
{
lean_dec(v_a_4554_);
return v___x_4563_;
}
}
}
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
v_a_4566_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4553_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4553_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4574_, lean_object* v___x_4575_, lean_object* v___x_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4574_, v___x_4575_, v___x_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___x_4575_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4583_, uint8_t v___x_4584_, lean_object* v_as_x27_4585_, lean_object* v_b_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
if (lean_obj_tag(v_as_x27_4585_) == 0)
{
lean_object* v___x_4592_; 
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v_b_4586_);
return v___x_4592_;
}
else
{
lean_object* v_head_4593_; lean_object* v_tail_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___f_4597_; uint8_t v___y_4599_; uint8_t v___x_4602_; 
v_head_4593_ = lean_ctor_get(v_as_x27_4585_, 0);
v_tail_4594_ = lean_ctor_get(v_as_x27_4585_, 1);
v___x_4595_ = lean_unsigned_to_nat(0u);
v___x_4596_ = lean_box(0);
lean_inc(v_head_4593_);
v___f_4597_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4597_, 0, v_head_4593_);
lean_closure_set(v___f_4597_, 1, v___x_4595_);
lean_closure_set(v___f_4597_, 2, v___x_4596_);
v___x_4602_ = l_Lean_isPrivateName(v_head_4593_);
if (v___x_4602_ == 0)
{
v___y_4599_ = v___y_4583_;
goto v___jp_4598_;
}
else
{
v___y_4599_ = v___x_4584_;
goto v___jp_4598_;
}
v___jp_4598_:
{
lean_object* v___x_4600_; 
v___x_4600_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4597_, v___y_4599_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_dec_ref_known(v___x_4600_, 1);
v_as_x27_4585_ = v_tail_4594_;
v_b_4586_ = v___x_4596_;
goto _start;
}
else
{
return v___x_4600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4603_, lean_object* v___x_4604_, lean_object* v_as_x27_4605_, lean_object* v_b_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
uint8_t v___y_20240__boxed_4612_; uint8_t v___x_20241__boxed_4613_; lean_object* v_res_4614_; 
v___y_20240__boxed_4612_ = lean_unbox(v___y_4603_);
v___x_20241__boxed_4613_ = lean_unbox(v___x_4604_);
v_res_4614_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_20240__boxed_4612_, v___x_20241__boxed_4613_, v_as_x27_4605_, v_b_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v_as_x27_4605_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4615_, uint8_t v_hasTrace_4616_, lean_object* v_ctors_4617_, lean_object* v___x_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v___x_4624_; 
v___x_4624_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4615_, v_hasTrace_4616_, v_ctors_4617_, v___x_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4631_ == 0)
{
lean_object* v_unused_4632_; 
v_unused_4632_ = lean_ctor_get(v___x_4624_, 0);
lean_dec(v_unused_4632_);
v___x_4626_ = v___x_4624_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_dec(v___x_4624_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v___x_4618_);
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4618_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
else
{
return v___x_4624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4633_, lean_object* v_hasTrace_4634_, lean_object* v_ctors_4635_, lean_object* v___x_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
uint8_t v___y_20285__boxed_4642_; uint8_t v_hasTrace_boxed_4643_; lean_object* v_res_4644_; 
v___y_20285__boxed_4642_ = lean_unbox(v___y_4633_);
v_hasTrace_boxed_4643_ = lean_unbox(v_hasTrace_4634_);
v_res_4644_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_20285__boxed_4642_, v_hasTrace_boxed_4643_, v_ctors_4635_, v___x_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v_ctors_4635_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t v_hasTrace_4645_, uint8_t v___x_4646_, lean_object* v_ctors_4647_, lean_object* v___x_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_hasTrace_4645_, v___x_4646_, v_ctors_4647_, v___x_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
if (lean_obj_tag(v___x_4654_) == 0)
{
lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4661_ == 0)
{
lean_object* v_unused_4662_; 
v_unused_4662_ = lean_ctor_get(v___x_4654_, 0);
lean_dec(v_unused_4662_);
v___x_4656_ = v___x_4654_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_dec(v___x_4654_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 0, v___x_4648_);
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4648_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
else
{
return v___x_4654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object* v_hasTrace_4663_, lean_object* v___x_4664_, lean_object* v_ctors_4665_, lean_object* v___x_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
uint8_t v_hasTrace_boxed_4672_; uint8_t v___x_20326__boxed_4673_; lean_object* v_res_4674_; 
v_hasTrace_boxed_4672_ = lean_unbox(v_hasTrace_4663_);
v___x_20326__boxed_4673_ = lean_unbox(v___x_4664_);
v_res_4674_ = l_Lean_Meta_mkInjectiveTheorems___lam__2(v_hasTrace_boxed_4672_, v___x_20326__boxed_4673_, v_ctors_4665_, v___x_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec(v_ctors_4665_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t v___x_4675_, uint8_t v_isUnsafe_4676_, lean_object* v_ctors_4677_, lean_object* v___x_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
lean_object* v___x_4684_; 
v___x_4684_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4675_, v_isUnsafe_4676_, v_ctors_4677_, v___x_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4691_ == 0)
{
lean_object* v_unused_4692_; 
v_unused_4692_ = lean_ctor_get(v___x_4684_, 0);
lean_dec(v_unused_4692_);
v___x_4686_ = v___x_4684_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_dec(v___x_4684_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
lean_ctor_set(v___x_4686_, 0, v___x_4678_);
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4678_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
else
{
return v___x_4684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object* v___x_4693_, lean_object* v_isUnsafe_4694_, lean_object* v_ctors_4695_, lean_object* v___x_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
uint8_t v___x_20367__boxed_4702_; uint8_t v_isUnsafe_boxed_4703_; lean_object* v_res_4704_; 
v___x_20367__boxed_4702_ = lean_unbox(v___x_4693_);
v_isUnsafe_boxed_4703_ = lean_unbox(v_isUnsafe_4694_);
v_res_4704_ = l_Lean_Meta_mkInjectiveTheorems___lam__3(v___x_20367__boxed_4702_, v_isUnsafe_boxed_4703_, v_ctors_4695_, v___x_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v_ctors_4695_);
return v_res_4704_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4707_ = l_Lean_stringToMessageData(v___x_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v___x_4714_; lean_object* v_env_4715_; lean_object* v___x_4716_; 
v___x_4714_ = lean_st_ref_get(v___y_4712_);
v_env_4715_ = lean_ctor_get(v___x_4714_, 0);
lean_inc_ref(v_env_4715_);
lean_dec(v___x_4714_);
lean_inc(v_constName_4708_);
v___x_4716_ = l_Lean_isInductiveCore_x3f(v_env_4715_, v_constName_4708_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v___x_4717_; uint8_t v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4717_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4718_ = 0;
v___x_4719_ = l_Lean_MessageData_ofConstName(v_constName_4708_, v___x_4718_);
v___x_4720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4717_);
lean_ctor_set(v___x_4720_, 1, v___x_4719_);
v___x_4721_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4720_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
v___x_4723_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4722_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
return v___x_4723_;
}
else
{
lean_object* v_val_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
lean_dec(v_constName_4708_);
v_val_4724_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4726_ = v___x_4716_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_val_4724_);
lean_dec(v___x_4716_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
lean_ctor_set_tag(v___x_4726_, 0);
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_val_4724_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
return v_res_4738_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4739_; 
v___x_4739_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4739_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4740_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
return v___x_4741_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = lean_unsigned_to_nat(32u);
v___x_4743_ = lean_mk_empty_array_with_capacity(v___x_4742_);
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4745_ = ((size_t)5ULL);
v___x_4746_ = lean_unsigned_to_nat(0u);
v___x_4747_ = lean_unsigned_to_nat(32u);
v___x_4748_ = lean_mk_empty_array_with_capacity(v___x_4747_);
v___x_4749_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4750_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
lean_ctor_set(v___x_4750_, 1, v___x_4748_);
lean_ctor_set(v___x_4750_, 2, v___x_4746_);
lean_ctor_set(v___x_4750_, 3, v___x_4746_);
lean_ctor_set_usize(v___x_4750_, 4, v___x_4745_);
return v___x_4750_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4751_ = lean_box(1);
v___x_4752_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4753_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
lean_ctor_set(v___x_4754_, 1, v___x_4752_);
lean_ctor_set(v___x_4754_, 2, v___x_4751_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = lean_st_ref_get(v_a_4761_);
lean_inc(v_declName_4757_);
v___x_4764_ = l_Lean_Meta_isInductivePredicate(v_declName_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4961_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4767_ = v___x_4764_;
v_isShared_4768_ = v_isSharedCheck_4961_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4764_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4961_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v_env_4774_; lean_object* v___f_4775_; lean_object* v___x_4776_; uint8_t v___x_4777_; lean_object* v___y_4779_; lean_object* v___y_4780_; lean_object* v___y_4781_; uint8_t v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4784_; lean_object* v_a_4785_; lean_object* v___y_4795_; lean_object* v___y_4796_; lean_object* v___y_4797_; uint8_t v___y_4798_; lean_object* v___y_4799_; lean_object* v___y_4800_; lean_object* v_a_4801_; lean_object* v___y_4804_; lean_object* v___y_4805_; lean_object* v___y_4806_; uint8_t v___y_4807_; lean_object* v___y_4808_; lean_object* v___y_4809_; lean_object* v_a_4810_; lean_object* v___y_4813_; lean_object* v___y_4814_; uint8_t v___y_4815_; lean_object* v___y_4816_; lean_object* v___y_4817_; lean_object* v___y_4818_; lean_object* v_a_4819_; lean_object* v___y_4832_; lean_object* v___y_4833_; uint8_t v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4836_; lean_object* v___y_4837_; lean_object* v_a_4838_; lean_object* v___y_4841_; lean_object* v___y_4842_; uint8_t v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; lean_object* v___y_4846_; lean_object* v_a_4847_; uint8_t v___y_4850_; lean_object* v___y_4851_; uint8_t v___y_4852_; lean_object* v___y_4853_; lean_object* v___y_4854_; uint8_t v___y_4892_; uint8_t v___x_4957_; 
v_env_4774_ = lean_ctor_get(v___x_4763_, 0);
lean_inc_ref(v_env_4774_);
lean_dec(v___x_4763_);
lean_inc(v_declName_4757_);
v___f_4775_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4775_, 0, v_declName_4757_);
v___x_4776_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4777_ = 1;
v___x_4957_ = l_Lean_Environment_contains(v_env_4774_, v___x_4776_, v___x_4777_);
if (v___x_4957_ == 0)
{
v___y_4892_ = v___x_4957_;
goto v___jp_4891_;
}
else
{
lean_object* v_options_4958_; lean_object* v___x_4959_; uint8_t v___x_4960_; 
v_options_4958_ = lean_ctor_get(v_a_4760_, 2);
v___x_4959_ = l_Lean_Meta_genInjectivity;
v___x_4960_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4958_, v___x_4959_);
v___y_4892_ = v___x_4960_;
goto v___jp_4891_;
}
v___jp_4769_:
{
lean_object* v___x_4770_; lean_object* v___x_4772_; 
v___x_4770_ = lean_box(0);
if (v_isShared_4768_ == 0)
{
lean_ctor_set(v___x_4767_, 0, v___x_4770_);
v___x_4772_ = v___x_4767_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4770_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
v___jp_4778_:
{
lean_object* v___x_4786_; double v___x_4787_; double v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4786_ = lean_io_get_num_heartbeats();
v___x_4787_ = lean_float_of_nat(v___y_4780_);
v___x_4788_ = lean_float_of_nat(v___x_4786_);
v___x_4789_ = lean_box_float(v___x_4787_);
v___x_4790_ = lean_box_float(v___x_4788_);
v___x_4791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4789_);
lean_ctor_set(v___x_4791_, 1, v___x_4790_);
v___x_4792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4792_, 0, v_a_4785_);
lean_ctor_set(v___x_4792_, 1, v___x_4791_);
lean_inc_ref(v___y_4784_);
lean_inc(v___y_4783_);
v___x_4793_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4783_, v___x_4777_, v___y_4784_, v___y_4779_, v___y_4782_, v___y_4781_, v___f_4775_, v___x_4792_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
return v___x_4793_;
}
v___jp_4794_:
{
lean_object* v___x_4802_; 
v___x_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4802_, 0, v_a_4801_);
v___y_4779_ = v___y_4795_;
v___y_4780_ = v___y_4796_;
v___y_4781_ = v___y_4797_;
v___y_4782_ = v___y_4798_;
v___y_4783_ = v___y_4799_;
v___y_4784_ = v___y_4800_;
v_a_4785_ = v___x_4802_;
goto v___jp_4778_;
}
v___jp_4803_:
{
lean_object* v___x_4811_; 
v___x_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4811_, 0, v_a_4810_);
v___y_4779_ = v___y_4804_;
v___y_4780_ = v___y_4805_;
v___y_4781_ = v___y_4806_;
v___y_4782_ = v___y_4807_;
v___y_4783_ = v___y_4808_;
v___y_4784_ = v___y_4809_;
v_a_4785_ = v___x_4811_;
goto v___jp_4778_;
}
v___jp_4812_:
{
lean_object* v___x_4820_; double v___x_4821_; double v___x_4822_; double v___x_4823_; double v___x_4824_; double v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4820_ = lean_io_mono_nanos_now();
v___x_4821_ = lean_float_of_nat(v___y_4818_);
v___x_4822_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4823_ = lean_float_div(v___x_4821_, v___x_4822_);
v___x_4824_ = lean_float_of_nat(v___x_4820_);
v___x_4825_ = lean_float_div(v___x_4824_, v___x_4822_);
v___x_4826_ = lean_box_float(v___x_4823_);
v___x_4827_ = lean_box_float(v___x_4825_);
v___x_4828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4826_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
v___x_4829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4829_, 0, v_a_4819_);
lean_ctor_set(v___x_4829_, 1, v___x_4828_);
lean_inc_ref(v___y_4817_);
lean_inc(v___y_4816_);
v___x_4830_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4816_, v___x_4777_, v___y_4817_, v___y_4813_, v___y_4815_, v___y_4814_, v___f_4775_, v___x_4829_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
return v___x_4830_;
}
v___jp_4831_:
{
lean_object* v___x_4839_; 
v___x_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4839_, 0, v_a_4838_);
v___y_4813_ = v___y_4832_;
v___y_4814_ = v___y_4833_;
v___y_4815_ = v___y_4834_;
v___y_4816_ = v___y_4835_;
v___y_4817_ = v___y_4836_;
v___y_4818_ = v___y_4837_;
v_a_4819_ = v___x_4839_;
goto v___jp_4812_;
}
v___jp_4840_:
{
lean_object* v___x_4848_; 
v___x_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4848_, 0, v_a_4847_);
v___y_4813_ = v___y_4841_;
v___y_4814_ = v___y_4842_;
v___y_4815_ = v___y_4843_;
v___y_4816_ = v___y_4844_;
v___y_4817_ = v___y_4845_;
v___y_4818_ = v___y_4846_;
v_a_4819_ = v___x_4848_;
goto v___jp_4812_;
}
v___jp_4849_:
{
lean_object* v___x_4855_; lean_object* v_a_4856_; lean_object* v___x_4857_; uint8_t v___x_4858_; 
v___x_4855_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4761_);
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc(v_a_4856_);
lean_dec_ref(v___x_4855_);
v___x_4857_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4858_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4851_, v___x_4857_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4859_ = lean_io_mono_nanos_now();
v___x_4860_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; uint8_t v_isUnsafe_4862_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref_known(v___x_4860_, 1);
v_isUnsafe_4862_ = lean_ctor_get_uint8(v_a_4861_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4862_ == 0)
{
lean_object* v_ctors_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___f_4869_; lean_object* v___x_4870_; 
v_ctors_4863_ = lean_ctor_get(v_a_4861_, 4);
lean_inc(v_ctors_4863_);
lean_dec(v_a_4861_);
v___x_4864_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4865_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4866_ = lean_box(0);
v___x_4867_ = lean_box(v___y_4850_);
v___x_4868_ = lean_box(v___x_4858_);
v___f_4869_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4869_, 0, v___x_4867_);
lean_closure_set(v___f_4869_, 1, v___x_4868_);
lean_closure_set(v___f_4869_, 2, v_ctors_4863_);
lean_closure_set(v___f_4869_, 3, v___x_4866_);
v___x_4870_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4864_, v___x_4865_, v___f_4869_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
lean_inc(v_a_4871_);
lean_dec_ref_known(v___x_4870_, 1);
v___y_4832_ = v___y_4851_;
v___y_4833_ = v_a_4856_;
v___y_4834_ = v___y_4852_;
v___y_4835_ = v___y_4853_;
v___y_4836_ = v___y_4854_;
v___y_4837_ = v___x_4859_;
v_a_4838_ = v_a_4871_;
goto v___jp_4831_;
}
else
{
lean_object* v_a_4872_; 
v_a_4872_ = lean_ctor_get(v___x_4870_, 0);
lean_inc(v_a_4872_);
lean_dec_ref_known(v___x_4870_, 1);
v___y_4841_ = v___y_4851_;
v___y_4842_ = v_a_4856_;
v___y_4843_ = v___y_4852_;
v___y_4844_ = v___y_4853_;
v___y_4845_ = v___y_4854_;
v___y_4846_ = v___x_4859_;
v_a_4847_ = v_a_4872_;
goto v___jp_4840_;
}
}
else
{
lean_object* v___x_4873_; 
lean_dec(v_a_4861_);
v___x_4873_ = lean_box(0);
v___y_4832_ = v___y_4851_;
v___y_4833_ = v_a_4856_;
v___y_4834_ = v___y_4852_;
v___y_4835_ = v___y_4853_;
v___y_4836_ = v___y_4854_;
v___y_4837_ = v___x_4859_;
v_a_4838_ = v___x_4873_;
goto v___jp_4831_;
}
}
else
{
lean_object* v_a_4874_; 
v_a_4874_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4874_);
lean_dec_ref_known(v___x_4860_, 1);
v___y_4841_ = v___y_4851_;
v___y_4842_ = v_a_4856_;
v___y_4843_ = v___y_4852_;
v___y_4844_ = v___y_4853_;
v___y_4845_ = v___y_4854_;
v___y_4846_ = v___x_4859_;
v_a_4847_ = v_a_4874_;
goto v___jp_4840_;
}
}
else
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_io_get_num_heartbeats();
v___x_4876_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; uint8_t v_isUnsafe_4878_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4877_);
lean_dec_ref_known(v___x_4876_, 1);
v_isUnsafe_4878_ = lean_ctor_get_uint8(v_a_4877_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4878_ == 0)
{
lean_object* v_ctors_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___f_4885_; lean_object* v___x_4886_; 
v_ctors_4879_ = lean_ctor_get(v_a_4877_, 4);
lean_inc(v_ctors_4879_);
lean_dec(v_a_4877_);
v___x_4880_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4881_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4882_ = lean_box(0);
v___x_4883_ = lean_box(v___x_4858_);
v___x_4884_ = lean_box(v_isUnsafe_4878_);
v___f_4885_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed), 9, 4);
lean_closure_set(v___f_4885_, 0, v___x_4883_);
lean_closure_set(v___f_4885_, 1, v___x_4884_);
lean_closure_set(v___f_4885_, 2, v_ctors_4879_);
lean_closure_set(v___f_4885_, 3, v___x_4882_);
v___x_4886_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4880_, v___x_4881_, v___f_4885_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4887_);
lean_dec_ref_known(v___x_4886_, 1);
v___y_4795_ = v___y_4851_;
v___y_4796_ = v___x_4875_;
v___y_4797_ = v_a_4856_;
v___y_4798_ = v___y_4852_;
v___y_4799_ = v___y_4853_;
v___y_4800_ = v___y_4854_;
v_a_4801_ = v_a_4887_;
goto v___jp_4794_;
}
else
{
lean_object* v_a_4888_; 
v_a_4888_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4888_);
lean_dec_ref_known(v___x_4886_, 1);
v___y_4804_ = v___y_4851_;
v___y_4805_ = v___x_4875_;
v___y_4806_ = v_a_4856_;
v___y_4807_ = v___y_4852_;
v___y_4808_ = v___y_4853_;
v___y_4809_ = v___y_4854_;
v_a_4810_ = v_a_4888_;
goto v___jp_4803_;
}
}
else
{
lean_object* v___x_4889_; 
lean_dec(v_a_4877_);
v___x_4889_ = lean_box(0);
v___y_4795_ = v___y_4851_;
v___y_4796_ = v___x_4875_;
v___y_4797_ = v_a_4856_;
v___y_4798_ = v___y_4852_;
v___y_4799_ = v___y_4853_;
v___y_4800_ = v___y_4854_;
v_a_4801_ = v___x_4889_;
goto v___jp_4794_;
}
}
else
{
lean_object* v_a_4890_; 
v_a_4890_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4876_, 1);
v___y_4804_ = v___y_4851_;
v___y_4805_ = v___x_4875_;
v___y_4806_ = v_a_4856_;
v___y_4807_ = v___y_4852_;
v___y_4808_ = v___y_4853_;
v___y_4809_ = v___y_4854_;
v_a_4810_ = v_a_4890_;
goto v___jp_4803_;
}
}
}
v___jp_4891_:
{
if (v___y_4892_ == 0)
{
lean_dec_ref(v___f_4775_);
lean_dec(v_a_4765_);
lean_dec(v_declName_4757_);
goto v___jp_4769_;
}
else
{
uint8_t v___x_4893_; 
v___x_4893_ = lean_unbox(v_a_4765_);
lean_dec(v_a_4765_);
if (v___x_4893_ == 0)
{
lean_object* v_options_4894_; uint8_t v_hasTrace_4895_; 
lean_del_object(v___x_4767_);
v_options_4894_ = lean_ctor_get(v_a_4760_, 2);
v_hasTrace_4895_ = lean_ctor_get_uint8(v_options_4894_, sizeof(void*)*1);
if (v_hasTrace_4895_ == 0)
{
lean_object* v___x_4896_; 
lean_dec_ref(v___f_4775_);
v___x_4896_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4914_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4914_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4914_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
uint8_t v_isUnsafe_4901_; 
v_isUnsafe_4901_ = lean_ctor_get_uint8(v_a_4897_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4901_ == 0)
{
lean_object* v_ctors_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___f_4908_; lean_object* v___x_4909_; 
lean_del_object(v___x_4899_);
v_ctors_4902_ = lean_ctor_get(v_a_4897_, 4);
lean_inc(v_ctors_4902_);
lean_dec(v_a_4897_);
v___x_4903_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4904_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4905_ = lean_box(0);
v___x_4906_ = lean_box(v___y_4892_);
v___x_4907_ = lean_box(v_hasTrace_4895_);
v___f_4908_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4908_, 0, v___x_4906_);
lean_closure_set(v___f_4908_, 1, v___x_4907_);
lean_closure_set(v___f_4908_, 2, v_ctors_4902_);
lean_closure_set(v___f_4908_, 3, v___x_4905_);
v___x_4909_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4903_, v___x_4904_, v___f_4908_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
return v___x_4909_;
}
else
{
lean_object* v___x_4910_; lean_object* v___x_4912_; 
lean_dec(v_a_4897_);
v___x_4910_ = lean_box(0);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4910_);
v___x_4912_ = v___x_4899_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4910_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
v_a_4915_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4896_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4896_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; uint8_t v___x_4927_; 
v_inheritedTraceOptions_4923_ = lean_ctor_get(v_a_4760_, 13);
v___x_4924_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4925_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4926_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4923_, v_options_4894_, v___x_4926_);
if (v___x_4927_ == 0)
{
lean_object* v___x_4928_; uint8_t v___x_4929_; 
v___x_4928_ = l_Lean_trace_profiler;
v___x_4929_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4894_, v___x_4928_);
if (v___x_4929_ == 0)
{
lean_object* v___x_4930_; 
lean_dec_ref(v___f_4775_);
v___x_4930_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4948_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4933_ = v___x_4930_;
v_isShared_4934_ = v_isSharedCheck_4948_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_a_4931_);
lean_dec(v___x_4930_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4948_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
uint8_t v_isUnsafe_4935_; 
v_isUnsafe_4935_ = lean_ctor_get_uint8(v_a_4931_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4935_ == 0)
{
lean_object* v_ctors_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___f_4942_; lean_object* v___x_4943_; 
lean_del_object(v___x_4933_);
v_ctors_4936_ = lean_ctor_get(v_a_4931_, 4);
lean_inc(v_ctors_4936_);
lean_dec(v_a_4931_);
v___x_4937_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4938_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4939_ = lean_box(0);
v___x_4940_ = lean_box(v_hasTrace_4895_);
v___x_4941_ = lean_box(v___x_4929_);
v___f_4942_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4942_, 0, v___x_4940_);
lean_closure_set(v___f_4942_, 1, v___x_4941_);
lean_closure_set(v___f_4942_, 2, v_ctors_4936_);
lean_closure_set(v___f_4942_, 3, v___x_4939_);
v___x_4943_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4937_, v___x_4938_, v___f_4942_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
return v___x_4943_;
}
else
{
lean_object* v___x_4944_; lean_object* v___x_4946_; 
lean_dec(v_a_4931_);
v___x_4944_ = lean_box(0);
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 0, v___x_4944_);
v___x_4946_ = v___x_4933_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4944_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
v_a_4949_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4930_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4930_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
else
{
v___y_4850_ = v_hasTrace_4895_;
v___y_4851_ = v_options_4894_;
v___y_4852_ = v___x_4927_;
v___y_4853_ = v___x_4924_;
v___y_4854_ = v___x_4925_;
goto v___jp_4849_;
}
}
else
{
v___y_4850_ = v_hasTrace_4895_;
v___y_4851_ = v_options_4894_;
v___y_4852_ = v___x_4927_;
v___y_4853_ = v___x_4924_;
v___y_4854_ = v___x_4925_;
goto v___jp_4849_;
}
}
}
else
{
lean_dec_ref(v___f_4775_);
lean_dec(v_declName_4757_);
goto v___jp_4769_;
}
}
}
}
}
else
{
lean_object* v_a_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4969_; 
lean_dec(v___x_4763_);
lean_dec(v_declName_4757_);
v_a_4962_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4964_ = v___x_4764_;
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_a_4962_);
lean_dec(v___x_4764_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4967_; 
if (v_isShared_4965_ == 0)
{
v___x_4967_ = v___x_4964_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_);
lean_dec(v_a_4974_);
lean_dec_ref(v_a_4973_);
lean_dec(v_a_4972_);
lean_dec_ref(v_a_4971_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4977_, uint8_t v___x_4978_, lean_object* v_as_4979_, lean_object* v_as_x27_4980_, lean_object* v_b_4981_, lean_object* v_a_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v___x_4988_; 
v___x_4988_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4977_, v___x_4978_, v_as_x27_4980_, v_b_4981_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4989_, lean_object* v___x_4990_, lean_object* v_as_4991_, lean_object* v_as_x27_4992_, lean_object* v_b_4993_, lean_object* v_a_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
uint8_t v___y_20994__boxed_5000_; uint8_t v___x_20995__boxed_5001_; lean_object* v_res_5002_; 
v___y_20994__boxed_5000_ = lean_unbox(v___y_4989_);
v___x_20995__boxed_5001_ = lean_unbox(v___x_4990_);
v_res_5002_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_20994__boxed_5000_, v___x_20995__boxed_5001_, v_as_4991_, v_as_x27_4992_, v_b_4993_, v_a_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec(v_as_x27_4992_);
lean_dec(v_as_4991_);
return v_res_5002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5043_ = lean_unsigned_to_nat(4172903888u);
v___x_5044_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_5045_ = l_Lean_Name_num___override(v___x_5044_, v___x_5043_);
return v___x_5045_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5047_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_5048_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_5049_ = l_Lean_Name_str___override(v___x_5048_, v___x_5047_);
return v___x_5049_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5051_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_5052_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_5053_ = l_Lean_Name_str___override(v___x_5052_, v___x_5051_);
return v___x_5053_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5054_ = lean_unsigned_to_nat(2u);
v___x_5055_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_5056_ = l_Lean_Name_num___override(v___x_5055_, v___x_5054_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5058_; uint8_t v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5058_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_5059_ = 0;
v___x_5060_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_5061_ = l_Lean_registerTraceClass(v___x_5058_, v___x_5059_, v___x_5060_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_5064_, lean_object* v_b_5065_){
_start:
{
lean_object* v_array_5066_; lean_object* v_start_5067_; lean_object* v_stop_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5081_; 
v_array_5066_ = lean_ctor_get(v_a_5064_, 0);
v_start_5067_ = lean_ctor_get(v_a_5064_, 1);
v_stop_5068_ = lean_ctor_get(v_a_5064_, 2);
v_isSharedCheck_5081_ = !lean_is_exclusive(v_a_5064_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5070_ = v_a_5064_;
v_isShared_5071_ = v_isSharedCheck_5081_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_stop_5068_);
lean_inc(v_start_5067_);
lean_inc(v_array_5066_);
lean_dec(v_a_5064_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5081_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
uint8_t v___x_5072_; 
v___x_5072_ = lean_nat_dec_lt(v_start_5067_, v_stop_5068_);
if (v___x_5072_ == 0)
{
lean_del_object(v___x_5070_);
lean_dec(v_stop_5068_);
lean_dec(v_start_5067_);
lean_dec_ref(v_array_5066_);
return v_b_5065_;
}
else
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5076_; 
v___x_5073_ = lean_unsigned_to_nat(1u);
v___x_5074_ = lean_nat_add(v_start_5067_, v___x_5073_);
lean_inc_ref(v_array_5066_);
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 1, v___x_5074_);
v___x_5076_ = v___x_5070_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_array_5066_);
lean_ctor_set(v_reuseFailAlloc_5080_, 1, v___x_5074_);
lean_ctor_set(v_reuseFailAlloc_5080_, 2, v_stop_5068_);
v___x_5076_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5077_ = lean_array_fget(v_array_5066_, v_start_5067_);
lean_dec(v_start_5067_);
lean_dec_ref(v_array_5066_);
v___x_5078_ = lean_array_push(v_b_5065_, v___x_5077_);
v_a_5064_ = v___x_5076_;
v_b_5065_ = v___x_5078_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5082_; 
v___x_5082_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5083_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5084_, 0, v___x_5083_);
return v___x_5084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5085_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_5086_ = lean_unsigned_to_nat(0u);
v___x_5087_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5087_, 0, v___x_5086_);
lean_ctor_set(v___x_5087_, 1, v___x_5086_);
lean_ctor_set(v___x_5087_, 2, v___x_5086_);
lean_ctor_set(v___x_5087_, 3, v___x_5086_);
lean_ctor_set(v___x_5087_, 4, v___x_5085_);
lean_ctor_set(v___x_5087_, 5, v___x_5085_);
lean_ctor_set(v___x_5087_, 6, v___x_5085_);
lean_ctor_set(v___x_5087_, 7, v___x_5085_);
lean_ctor_set(v___x_5087_, 8, v___x_5085_);
lean_ctor_set(v___x_5087_, 9, v___x_5085_);
lean_ctor_set(v___x_5087_, 10, v___x_5085_);
return v___x_5087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5088_ = lean_box(1);
v___x_5089_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_5090_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_5091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5090_);
lean_ctor_set(v___x_5091_, 1, v___x_5089_);
lean_ctor_set(v___x_5091_, 2, v___x_5088_);
return v___x_5091_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_5094_ = l_Lean_stringToMessageData(v___x_5093_);
return v___x_5094_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5096_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_5097_ = l_Lean_stringToMessageData(v___x_5096_);
return v___x_5097_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5099_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_5100_ = l_Lean_stringToMessageData(v___x_5099_);
return v___x_5100_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5102_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_5103_ = l_Lean_stringToMessageData(v___x_5102_);
return v___x_5103_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5105_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_5106_ = l_Lean_stringToMessageData(v___x_5105_);
return v___x_5106_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5108_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_5109_ = l_Lean_stringToMessageData(v___x_5108_);
return v___x_5109_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; 
v___x_5111_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_5112_ = l_Lean_stringToMessageData(v___x_5111_);
return v___x_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_5113_, lean_object* v_declHint_5114_, lean_object* v___y_5115_){
_start:
{
lean_object* v___x_5117_; lean_object* v_env_5118_; uint8_t v___x_5119_; 
v___x_5117_ = lean_st_ref_get(v___y_5115_);
v_env_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc_ref(v_env_5118_);
lean_dec(v___x_5117_);
v___x_5119_ = l_Lean_Name_isAnonymous(v_declHint_5114_);
if (v___x_5119_ == 0)
{
uint8_t v_isExporting_5120_; 
v_isExporting_5120_ = lean_ctor_get_uint8(v_env_5118_, sizeof(void*)*8);
if (v_isExporting_5120_ == 0)
{
lean_object* v___x_5121_; 
lean_dec_ref(v_env_5118_);
lean_dec(v_declHint_5114_);
v___x_5121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5121_, 0, v_msg_5113_);
return v___x_5121_;
}
else
{
lean_object* v___x_5122_; uint8_t v___x_5123_; 
lean_inc_ref(v_env_5118_);
v___x_5122_ = l_Lean_Environment_setExporting(v_env_5118_, v___x_5119_);
lean_inc(v_declHint_5114_);
lean_inc_ref(v___x_5122_);
v___x_5123_ = l_Lean_Environment_contains(v___x_5122_, v_declHint_5114_, v_isExporting_5120_);
if (v___x_5123_ == 0)
{
lean_object* v___x_5124_; 
lean_dec_ref(v___x_5122_);
lean_dec_ref(v_env_5118_);
lean_dec(v_declHint_5114_);
v___x_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5124_, 0, v_msg_5113_);
return v___x_5124_;
}
else
{
lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v_c_5130_; lean_object* v___x_5131_; 
v___x_5125_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_5126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_5127_ = l_Lean_Options_empty;
v___x_5128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5122_);
lean_ctor_set(v___x_5128_, 1, v___x_5125_);
lean_ctor_set(v___x_5128_, 2, v___x_5126_);
lean_ctor_set(v___x_5128_, 3, v___x_5127_);
lean_inc(v_declHint_5114_);
v___x_5129_ = l_Lean_MessageData_ofConstName(v_declHint_5114_, v___x_5119_);
v_c_5130_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_5130_, 0, v___x_5128_);
lean_ctor_set(v_c_5130_, 1, v___x_5129_);
v___x_5131_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5118_, v_declHint_5114_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
lean_dec_ref(v_env_5118_);
lean_dec(v_declHint_5114_);
v___x_5132_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_5133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5133_, 0, v___x_5132_);
lean_ctor_set(v___x_5133_, 1, v_c_5130_);
v___x_5134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_5135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5135_, 0, v___x_5133_);
lean_ctor_set(v___x_5135_, 1, v___x_5134_);
v___x_5136_ = l_Lean_MessageData_note(v___x_5135_);
v___x_5137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5137_, 0, v_msg_5113_);
lean_ctor_set(v___x_5137_, 1, v___x_5136_);
v___x_5138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5137_);
return v___x_5138_;
}
else
{
lean_object* v_val_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5174_; 
v_val_5139_ = lean_ctor_get(v___x_5131_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5131_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5141_ = v___x_5131_;
v_isShared_5142_ = v_isSharedCheck_5174_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_val_5139_);
lean_dec(v___x_5131_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5174_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v_mod_5146_; uint8_t v___x_5147_; 
v___x_5143_ = lean_box(0);
v___x_5144_ = l_Lean_Environment_header(v_env_5118_);
lean_dec_ref(v_env_5118_);
v___x_5145_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5144_);
v_mod_5146_ = lean_array_get(v___x_5143_, v___x_5145_, v_val_5139_);
lean_dec(v_val_5139_);
lean_dec_ref(v___x_5145_);
v___x_5147_ = l_Lean_isPrivateName(v_declHint_5114_);
lean_dec(v_declHint_5114_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5159_; 
v___x_5148_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_5149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5149_, 0, v___x_5148_);
lean_ctor_set(v___x_5149_, 1, v_c_5130_);
v___x_5150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_5151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5151_, 0, v___x_5149_);
lean_ctor_set(v___x_5151_, 1, v___x_5150_);
v___x_5152_ = l_Lean_MessageData_ofName(v_mod_5146_);
v___x_5153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5151_);
lean_ctor_set(v___x_5153_, 1, v___x_5152_);
v___x_5154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_5155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5153_);
lean_ctor_set(v___x_5155_, 1, v___x_5154_);
v___x_5156_ = l_Lean_MessageData_note(v___x_5155_);
v___x_5157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5157_, 0, v_msg_5113_);
lean_ctor_set(v___x_5157_, 1, v___x_5156_);
if (v_isShared_5142_ == 0)
{
lean_ctor_set_tag(v___x_5141_, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5157_);
v___x_5159_ = v___x_5141_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5157_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
else
{
lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5172_; 
v___x_5161_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_5162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5161_);
lean_ctor_set(v___x_5162_, 1, v_c_5130_);
v___x_5163_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_5164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5162_);
lean_ctor_set(v___x_5164_, 1, v___x_5163_);
v___x_5165_ = l_Lean_MessageData_ofName(v_mod_5146_);
v___x_5166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5166_, 0, v___x_5164_);
lean_ctor_set(v___x_5166_, 1, v___x_5165_);
v___x_5167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_5168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5166_);
lean_ctor_set(v___x_5168_, 1, v___x_5167_);
v___x_5169_ = l_Lean_MessageData_note(v___x_5168_);
v___x_5170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5170_, 0, v_msg_5113_);
lean_ctor_set(v___x_5170_, 1, v___x_5169_);
if (v_isShared_5142_ == 0)
{
lean_ctor_set_tag(v___x_5141_, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5170_);
v___x_5172_ = v___x_5141_;
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
}
}
}
else
{
lean_object* v___x_5175_; 
lean_dec_ref(v_env_5118_);
lean_dec(v_declHint_5114_);
v___x_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5175_, 0, v_msg_5113_);
return v___x_5175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_5176_, lean_object* v_declHint_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5176_, v_declHint_5177_, v___y_5178_);
lean_dec(v___y_5178_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_5181_, lean_object* v_declHint_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_){
_start:
{
lean_object* v___x_5188_; lean_object* v_a_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5198_; 
v___x_5188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5181_, v_declHint_5182_, v___y_5186_);
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5191_ = v___x_5188_;
v_isShared_5192_ = v_isSharedCheck_5198_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_a_5189_);
lean_dec(v___x_5188_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5198_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5196_; 
v___x_5193_ = l_Lean_unknownIdentifierMessageTag;
v___x_5194_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5193_);
lean_ctor_set(v___x_5194_, 1, v_a_5189_);
if (v_isShared_5192_ == 0)
{
lean_ctor_set(v___x_5191_, 0, v___x_5194_);
v___x_5196_ = v___x_5191_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v___x_5194_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
return v___x_5196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5199_, lean_object* v_declHint_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5199_, v_declHint_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5207_, lean_object* v_msg_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_){
_start:
{
lean_object* v_fileName_5214_; lean_object* v_fileMap_5215_; lean_object* v_options_5216_; lean_object* v_currRecDepth_5217_; lean_object* v_maxRecDepth_5218_; lean_object* v_ref_5219_; lean_object* v_currNamespace_5220_; lean_object* v_openDecls_5221_; lean_object* v_initHeartbeats_5222_; lean_object* v_maxHeartbeats_5223_; lean_object* v_quotContext_5224_; lean_object* v_currMacroScope_5225_; uint8_t v_diag_5226_; lean_object* v_cancelTk_x3f_5227_; uint8_t v_suppressElabErrors_5228_; lean_object* v_inheritedTraceOptions_5229_; lean_object* v_ref_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; 
v_fileName_5214_ = lean_ctor_get(v___y_5211_, 0);
v_fileMap_5215_ = lean_ctor_get(v___y_5211_, 1);
v_options_5216_ = lean_ctor_get(v___y_5211_, 2);
v_currRecDepth_5217_ = lean_ctor_get(v___y_5211_, 3);
v_maxRecDepth_5218_ = lean_ctor_get(v___y_5211_, 4);
v_ref_5219_ = lean_ctor_get(v___y_5211_, 5);
v_currNamespace_5220_ = lean_ctor_get(v___y_5211_, 6);
v_openDecls_5221_ = lean_ctor_get(v___y_5211_, 7);
v_initHeartbeats_5222_ = lean_ctor_get(v___y_5211_, 8);
v_maxHeartbeats_5223_ = lean_ctor_get(v___y_5211_, 9);
v_quotContext_5224_ = lean_ctor_get(v___y_5211_, 10);
v_currMacroScope_5225_ = lean_ctor_get(v___y_5211_, 11);
v_diag_5226_ = lean_ctor_get_uint8(v___y_5211_, sizeof(void*)*14);
v_cancelTk_x3f_5227_ = lean_ctor_get(v___y_5211_, 12);
v_suppressElabErrors_5228_ = lean_ctor_get_uint8(v___y_5211_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5229_ = lean_ctor_get(v___y_5211_, 13);
v_ref_5230_ = l_Lean_replaceRef(v_ref_5207_, v_ref_5219_);
lean_inc_ref(v_inheritedTraceOptions_5229_);
lean_inc(v_cancelTk_x3f_5227_);
lean_inc(v_currMacroScope_5225_);
lean_inc(v_quotContext_5224_);
lean_inc(v_maxHeartbeats_5223_);
lean_inc(v_initHeartbeats_5222_);
lean_inc(v_openDecls_5221_);
lean_inc(v_currNamespace_5220_);
lean_inc(v_maxRecDepth_5218_);
lean_inc(v_currRecDepth_5217_);
lean_inc_ref(v_options_5216_);
lean_inc_ref(v_fileMap_5215_);
lean_inc_ref(v_fileName_5214_);
v___x_5231_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5231_, 0, v_fileName_5214_);
lean_ctor_set(v___x_5231_, 1, v_fileMap_5215_);
lean_ctor_set(v___x_5231_, 2, v_options_5216_);
lean_ctor_set(v___x_5231_, 3, v_currRecDepth_5217_);
lean_ctor_set(v___x_5231_, 4, v_maxRecDepth_5218_);
lean_ctor_set(v___x_5231_, 5, v_ref_5230_);
lean_ctor_set(v___x_5231_, 6, v_currNamespace_5220_);
lean_ctor_set(v___x_5231_, 7, v_openDecls_5221_);
lean_ctor_set(v___x_5231_, 8, v_initHeartbeats_5222_);
lean_ctor_set(v___x_5231_, 9, v_maxHeartbeats_5223_);
lean_ctor_set(v___x_5231_, 10, v_quotContext_5224_);
lean_ctor_set(v___x_5231_, 11, v_currMacroScope_5225_);
lean_ctor_set(v___x_5231_, 12, v_cancelTk_x3f_5227_);
lean_ctor_set(v___x_5231_, 13, v_inheritedTraceOptions_5229_);
lean_ctor_set_uint8(v___x_5231_, sizeof(void*)*14, v_diag_5226_);
lean_ctor_set_uint8(v___x_5231_, sizeof(void*)*14 + 1, v_suppressElabErrors_5228_);
v___x_5232_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5208_, v___y_5209_, v___y_5210_, v___x_5231_, v___y_5212_);
lean_dec_ref_known(v___x_5231_, 14);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5233_, lean_object* v_msg_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5233_, v_msg_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
lean_dec(v_ref_5233_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5241_, lean_object* v_msg_5242_, lean_object* v_declHint_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v___x_5249_; lean_object* v_a_5250_; lean_object* v___x_5251_; 
v___x_5249_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5242_, v_declHint_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
v_a_5250_ = lean_ctor_get(v___x_5249_, 0);
lean_inc(v_a_5250_);
lean_dec_ref(v___x_5249_);
v___x_5251_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5241_, v_a_5250_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5252_, lean_object* v_msg_5253_, lean_object* v_declHint_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5252_, v_msg_5253_, v_declHint_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v_ref_5252_);
return v_res_5260_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5262_; lean_object* v___x_5263_; 
v___x_5262_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5263_ = l_Lean_stringToMessageData(v___x_5262_);
return v___x_5263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5264_, lean_object* v_constName_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_){
_start:
{
lean_object* v___x_5271_; uint8_t v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5271_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5272_ = 0;
lean_inc(v_constName_5265_);
v___x_5273_ = l_Lean_MessageData_ofConstName(v_constName_5265_, v___x_5272_);
v___x_5274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5271_);
lean_ctor_set(v___x_5274_, 1, v___x_5273_);
v___x_5275_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5276_, 0, v___x_5274_);
lean_ctor_set(v___x_5276_, 1, v___x_5275_);
v___x_5277_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5264_, v___x_5276_, v_constName_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
return v___x_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5278_, lean_object* v_constName_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5278_, v_constName_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v_ref_5278_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_){
_start:
{
lean_object* v_ref_5292_; lean_object* v___x_5293_; 
v_ref_5292_ = lean_ctor_get(v___y_5289_, 5);
v___x_5293_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5292_, v_constName_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
return v___x_5293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_){
_start:
{
lean_object* v_res_5300_; 
v_res_5300_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_);
lean_dec(v___y_5298_);
lean_dec_ref(v___y_5297_);
lean_dec(v___y_5296_);
lean_dec_ref(v___y_5295_);
return v_res_5300_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v___x_5307_; lean_object* v_env_5308_; uint8_t v___x_5309_; lean_object* v___x_5310_; 
v___x_5307_ = lean_st_ref_get(v___y_5305_);
v_env_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc_ref(v_env_5308_);
lean_dec(v___x_5307_);
v___x_5309_ = 0;
lean_inc(v_constName_5301_);
v___x_5310_ = l_Lean_Environment_find_x3f(v_env_5308_, v_constName_5301_, v___x_5309_);
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v___x_5311_; 
v___x_5311_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
return v___x_5311_;
}
else
{
lean_object* v_val_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5319_; 
lean_dec(v_constName_5301_);
v_val_5312_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5314_ = v___x_5310_;
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_val_5312_);
lean_dec(v___x_5310_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
if (v_isShared_5315_ == 0)
{
lean_ctor_set_tag(v___x_5314_, 0);
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_val_5312_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
lean_object* v_res_5326_; 
v_res_5326_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
return v_res_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5329_, lean_object* v_x_5330_, lean_object* v_x_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
if (lean_obj_tag(v_x_5329_) == 5)
{
lean_object* v_fn_5337_; lean_object* v_arg_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; 
v_fn_5337_ = lean_ctor_get(v_x_5329_, 0);
lean_inc_ref(v_fn_5337_);
v_arg_5338_ = lean_ctor_get(v_x_5329_, 1);
lean_inc_ref(v_arg_5338_);
lean_dec_ref_known(v_x_5329_, 2);
v___x_5339_ = lean_array_set(v_x_5330_, v_x_5331_, v_arg_5338_);
v___x_5340_ = lean_unsigned_to_nat(1u);
v___x_5341_ = lean_nat_sub(v_x_5331_, v___x_5340_);
lean_dec(v_x_5331_);
v_x_5329_ = v_fn_5337_;
v_x_5330_ = v___x_5339_;
v_x_5331_ = v___x_5341_;
goto _start;
}
else
{
lean_dec(v_x_5331_);
if (lean_obj_tag(v_x_5329_) == 4)
{
lean_object* v_declName_5343_; lean_object* v___x_5344_; 
v_declName_5343_ = lean_ctor_get(v_x_5329_, 0);
lean_inc(v_declName_5343_);
lean_dec_ref_known(v_x_5329_, 2);
v___x_5344_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5343_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
if (lean_obj_tag(v___x_5344_) == 0)
{
lean_object* v_a_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5376_; 
v_a_5345_ = lean_ctor_get(v___x_5344_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5344_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5347_ = v___x_5344_;
v_isShared_5348_ = v_isSharedCheck_5376_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_a_5345_);
lean_dec(v___x_5344_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5376_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
lean_object* v_lower_5350_; lean_object* v_upper_5351_; 
if (lean_obj_tag(v_a_5345_) == 5)
{
lean_object* v_val_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5373_; 
v_val_5359_ = lean_ctor_get(v_a_5345_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v_a_5345_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5361_ = v_a_5345_;
v_isShared_5362_ = v_isSharedCheck_5373_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_val_5359_);
lean_dec(v_a_5345_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5373_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v_numParams_5363_; lean_object* v_numIndices_5364_; lean_object* v___x_5365_; uint8_t v___x_5366_; 
v_numParams_5363_ = lean_ctor_get(v_val_5359_, 1);
lean_inc(v_numParams_5363_);
v_numIndices_5364_ = lean_ctor_get(v_val_5359_, 2);
lean_inc(v_numIndices_5364_);
lean_dec_ref(v_val_5359_);
v___x_5365_ = lean_unsigned_to_nat(0u);
v___x_5366_ = lean_nat_dec_eq(v_numIndices_5364_, v___x_5365_);
lean_dec(v_numIndices_5364_);
if (v___x_5366_ == 0)
{
lean_object* v___x_5367_; uint8_t v___x_5368_; 
lean_del_object(v___x_5361_);
v___x_5367_ = lean_array_get_size(v_x_5330_);
v___x_5368_ = lean_nat_dec_le(v_numParams_5363_, v___x_5365_);
if (v___x_5368_ == 0)
{
v_lower_5350_ = v_numParams_5363_;
v_upper_5351_ = v___x_5367_;
goto v___jp_5349_;
}
else
{
lean_dec(v_numParams_5363_);
v_lower_5350_ = v___x_5365_;
v_upper_5351_ = v___x_5367_;
goto v___jp_5349_;
}
}
else
{
lean_object* v___x_5369_; lean_object* v___x_5371_; 
lean_dec(v_numParams_5363_);
lean_del_object(v___x_5347_);
lean_dec_ref(v_x_5330_);
v___x_5369_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5362_ == 0)
{
lean_ctor_set_tag(v___x_5361_, 0);
lean_ctor_set(v___x_5361_, 0, v___x_5369_);
v___x_5371_ = v___x_5361_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
else
{
lean_object* v___x_5374_; lean_object* v___x_5375_; 
lean_del_object(v___x_5347_);
lean_dec(v_a_5345_);
lean_dec_ref(v_x_5330_);
v___x_5374_ = lean_box(0);
v___x_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5374_);
return v___x_5375_;
}
v___jp_5349_:
{
lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5357_; 
v___x_5352_ = l_Array_toSubarray___redArg(v_x_5330_, v_lower_5350_, v_upper_5351_);
v___x_5353_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5354_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5352_, v___x_5353_);
v___x_5355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5354_);
if (v_isShared_5348_ == 0)
{
lean_ctor_set(v___x_5347_, 0, v___x_5355_);
v___x_5357_ = v___x_5347_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v___x_5355_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
else
{
lean_object* v_a_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5384_; 
lean_dec_ref(v_x_5330_);
v_a_5377_ = lean_ctor_get(v___x_5344_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v___x_5344_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5379_ = v___x_5344_;
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_a_5377_);
lean_dec(v___x_5344_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
else
{
lean_object* v___x_5385_; lean_object* v___x_5386_; 
lean_dec_ref(v_x_5330_);
lean_dec_ref(v_x_5329_);
v___x_5385_ = lean_box(0);
v___x_5386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5385_);
return v___x_5386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5387_, lean_object* v_x_5388_, lean_object* v_x_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5387_, v_x_5388_, v_x_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_){
_start:
{
lean_object* v___x_5402_; 
lean_inc(v_a_5400_);
lean_inc_ref(v_a_5399_);
lean_inc(v_a_5398_);
lean_inc_ref(v_a_5397_);
v___x_5402_ = lean_infer_type(v_ctorApp_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_);
if (lean_obj_tag(v___x_5402_) == 0)
{
lean_object* v_a_5403_; lean_object* v___x_5404_; 
v_a_5403_ = lean_ctor_get(v___x_5402_, 0);
lean_inc(v_a_5403_);
lean_dec_ref_known(v___x_5402_, 1);
v___x_5404_ = l_Lean_Meta_whnfD(v_a_5403_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_);
if (lean_obj_tag(v___x_5404_) == 0)
{
lean_object* v_a_5405_; lean_object* v_dummy_5406_; lean_object* v_nargs_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v_a_5405_ = lean_ctor_get(v___x_5404_, 0);
lean_inc(v_a_5405_);
lean_dec_ref_known(v___x_5404_, 1);
v_dummy_5406_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5407_ = l_Lean_Expr_getAppNumArgs(v_a_5405_);
lean_inc(v_nargs_5407_);
v___x_5408_ = lean_mk_array(v_nargs_5407_, v_dummy_5406_);
v___x_5409_ = lean_unsigned_to_nat(1u);
v___x_5410_ = lean_nat_sub(v_nargs_5407_, v___x_5409_);
lean_dec(v_nargs_5407_);
v___x_5411_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5405_, v___x_5408_, v___x_5410_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_);
return v___x_5411_;
}
else
{
lean_object* v_a_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5419_; 
v_a_5412_ = lean_ctor_get(v___x_5404_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5404_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5414_ = v___x_5404_;
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_a_5412_);
lean_dec(v___x_5404_);
v___x_5414_ = lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5419_;
goto v_resetjp_5413_;
}
v_resetjp_5413_:
{
lean_object* v___x_5417_; 
if (v_isShared_5415_ == 0)
{
v___x_5417_ = v___x_5414_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_a_5412_);
v___x_5417_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
return v___x_5417_;
}
}
}
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5427_; 
v_a_5420_ = lean_ctor_get(v___x_5402_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5422_ = v___x_5402_;
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v___x_5402_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5425_; 
if (v_isShared_5423_ == 0)
{
v___x_5425_ = v___x_5422_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_a_5420_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
lean_dec(v_a_5432_);
lean_dec_ref(v_a_5431_);
lean_dec(v_a_5430_);
lean_dec_ref(v_a_5429_);
return v_res_5434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5435_, lean_object* v_R_5436_, lean_object* v_a_5437_, lean_object* v_b_5438_){
_start:
{
lean_object* v___x_5439_; 
v___x_5439_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5437_, v_b_5438_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5440_, lean_object* v_constName_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v___x_5447_; 
v___x_5447_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_);
return v___x_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5448_, lean_object* v_constName_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_){
_start:
{
lean_object* v_res_5455_; 
v_res_5455_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5448_, v_constName_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_);
lean_dec(v___y_5453_);
lean_dec_ref(v___y_5452_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5456_, lean_object* v_ref_5457_, lean_object* v_constName_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v___x_5464_; 
v___x_5464_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5457_, v_constName_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5465_, lean_object* v_ref_5466_, lean_object* v_constName_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_){
_start:
{
lean_object* v_res_5473_; 
v_res_5473_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5465_, v_ref_5466_, v_constName_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
lean_dec(v___y_5469_);
lean_dec_ref(v___y_5468_);
lean_dec(v_ref_5466_);
return v_res_5473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5474_, lean_object* v_ref_5475_, lean_object* v_msg_5476_, lean_object* v_declHint_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v___x_5483_; 
v___x_5483_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5475_, v_msg_5476_, v_declHint_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5484_, lean_object* v_ref_5485_, lean_object* v_msg_5486_, lean_object* v_declHint_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_){
_start:
{
lean_object* v_res_5493_; 
v_res_5493_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5484_, v_ref_5485_, v_msg_5486_, v_declHint_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_);
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
lean_dec(v_ref_5485_);
return v_res_5493_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5494_, lean_object* v_declHint_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_){
_start:
{
lean_object* v___x_5501_; 
v___x_5501_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5494_, v_declHint_5495_, v___y_5499_);
return v___x_5501_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5502_, lean_object* v_declHint_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_){
_start:
{
lean_object* v_res_5509_; 
v_res_5509_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5502_, v_declHint_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
lean_dec(v___y_5507_);
lean_dec_ref(v___y_5506_);
lean_dec(v___y_5505_);
lean_dec_ref(v___y_5504_);
return v_res_5509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5510_, lean_object* v_ref_5511_, lean_object* v_msg_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_){
_start:
{
lean_object* v___x_5518_; 
v___x_5518_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5511_, v_msg_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_);
return v___x_5518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5519_, lean_object* v_ref_5520_, lean_object* v_msg_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v_res_5527_; 
v_res_5527_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5519_, v_ref_5520_, v_msg_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
lean_dec(v___y_5525_);
lean_dec_ref(v___y_5524_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
lean_dec(v_ref_5520_);
return v_res_5527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5528_, lean_object* v_body_5529_, lean_object* v_args2_5530_, lean_object* v_ctorVal_5531_, lean_object* v_args1_5532_, lean_object* v_k_5533_, lean_object* v_arg2_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_){
_start:
{
lean_object* v_res_5540_; 
v_res_5540_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5528_, v_body_5529_, v_args2_5530_, v_ctorVal_5531_, v_args1_5532_, v_k_5533_, v_arg2_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec_ref(v___y_5535_);
lean_dec_ref(v_body_5529_);
lean_dec(v_i_5528_);
return v_res_5540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5541_, lean_object* v_args1_5542_, lean_object* v_k_5543_, lean_object* v_i_5544_, lean_object* v_type_5545_, lean_object* v_args2_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_){
_start:
{
lean_object* v___x_5552_; uint8_t v___x_5553_; 
v___x_5552_ = lean_array_get_size(v_args1_5542_);
v___x_5553_ = lean_nat_dec_lt(v_i_5544_, v___x_5552_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5554_; 
lean_dec_ref(v_type_5545_);
lean_dec(v_i_5544_);
lean_dec_ref(v_args1_5542_);
lean_dec_ref(v_ctorVal_5541_);
lean_inc(v_a_5550_);
lean_inc_ref(v_a_5549_);
lean_inc(v_a_5548_);
lean_inc_ref(v_a_5547_);
v___x_5554_ = lean_apply_6(v_k_5543_, v_args2_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, lean_box(0));
return v___x_5554_;
}
else
{
lean_object* v___x_5555_; 
lean_inc(v_a_5550_);
lean_inc_ref(v_a_5549_);
lean_inc(v_a_5548_);
lean_inc_ref(v_a_5547_);
v___x_5555_ = lean_whnf(v_type_5545_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_);
if (lean_obj_tag(v___x_5555_) == 0)
{
lean_object* v_a_5556_; 
v_a_5556_ = lean_ctor_get(v___x_5555_, 0);
lean_inc(v_a_5556_);
lean_dec_ref_known(v___x_5555_, 1);
if (lean_obj_tag(v_a_5556_) == 7)
{
lean_object* v_binderName_5557_; lean_object* v_binderType_5558_; lean_object* v_body_5559_; lean_object* v___f_5560_; uint8_t v___x_5561_; uint8_t v___x_5562_; lean_object* v___x_5563_; 
v_binderName_5557_ = lean_ctor_get(v_a_5556_, 0);
lean_inc(v_binderName_5557_);
v_binderType_5558_ = lean_ctor_get(v_a_5556_, 1);
lean_inc_ref(v_binderType_5558_);
v_body_5559_ = lean_ctor_get(v_a_5556_, 2);
lean_inc_ref(v_body_5559_);
lean_dec_ref_known(v_a_5556_, 3);
v___f_5560_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5560_, 0, v_i_5544_);
lean_closure_set(v___f_5560_, 1, v_body_5559_);
lean_closure_set(v___f_5560_, 2, v_args2_5546_);
lean_closure_set(v___f_5560_, 3, v_ctorVal_5541_);
lean_closure_set(v___f_5560_, 4, v_args1_5542_);
lean_closure_set(v___f_5560_, 5, v_k_5543_);
v___x_5561_ = 1;
v___x_5562_ = 0;
v___x_5563_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5557_, v___x_5561_, v_binderType_5558_, v___f_5560_, v___x_5562_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_);
return v___x_5563_;
}
else
{
lean_object* v_toConstantVal_5564_; lean_object* v_name_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; 
lean_dec(v_a_5556_);
lean_dec_ref(v_args2_5546_);
lean_dec(v_i_5544_);
lean_dec_ref(v_k_5543_);
lean_dec_ref(v_args1_5542_);
v_toConstantVal_5564_ = lean_ctor_get(v_ctorVal_5541_, 0);
lean_inc_ref(v_toConstantVal_5564_);
lean_dec_ref(v_ctorVal_5541_);
v_name_5565_ = lean_ctor_get(v_toConstantVal_5564_, 0);
lean_inc(v_name_5565_);
lean_dec_ref(v_toConstantVal_5564_);
v___x_5566_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5567_ = l_Lean_MessageData_ofName(v_name_5565_);
v___x_5568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5566_);
lean_ctor_set(v___x_5568_, 1, v___x_5567_);
v___x_5569_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5570_, 0, v___x_5568_);
lean_ctor_set(v___x_5570_, 1, v___x_5569_);
v___x_5571_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5570_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_);
return v___x_5571_;
}
}
else
{
lean_object* v_a_5572_; lean_object* v___x_5574_; uint8_t v_isShared_5575_; uint8_t v_isSharedCheck_5579_; 
lean_dec_ref(v_args2_5546_);
lean_dec(v_i_5544_);
lean_dec_ref(v_k_5543_);
lean_dec_ref(v_args1_5542_);
lean_dec_ref(v_ctorVal_5541_);
v_a_5572_ = lean_ctor_get(v___x_5555_, 0);
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5555_);
if (v_isSharedCheck_5579_ == 0)
{
v___x_5574_ = v___x_5555_;
v_isShared_5575_ = v_isSharedCheck_5579_;
goto v_resetjp_5573_;
}
else
{
lean_inc(v_a_5572_);
lean_dec(v___x_5555_);
v___x_5574_ = lean_box(0);
v_isShared_5575_ = v_isSharedCheck_5579_;
goto v_resetjp_5573_;
}
v_resetjp_5573_:
{
lean_object* v___x_5577_; 
if (v_isShared_5575_ == 0)
{
v___x_5577_ = v___x_5574_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_a_5572_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5580_, lean_object* v_body_5581_, lean_object* v_args2_5582_, lean_object* v_ctorVal_5583_, lean_object* v_args1_5584_, lean_object* v_k_5585_, lean_object* v_arg2_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_){
_start:
{
lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; 
v___x_5592_ = lean_unsigned_to_nat(1u);
v___x_5593_ = lean_nat_add(v_i_5580_, v___x_5592_);
v___x_5594_ = lean_expr_instantiate1(v_body_5581_, v_arg2_5586_);
v___x_5595_ = lean_array_push(v_args2_5582_, v_arg2_5586_);
v___x_5596_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5583_, v_args1_5584_, v_k_5585_, v___x_5593_, v___x_5594_, v___x_5595_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_);
return v___x_5596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5597_, lean_object* v_args1_5598_, lean_object* v_k_5599_, lean_object* v_i_5600_, lean_object* v_type_5601_, lean_object* v_args2_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_){
_start:
{
lean_object* v_res_5608_; 
v_res_5608_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5597_, v_args1_5598_, v_k_5599_, v_i_5600_, v_type_5601_, v_args2_5602_, v_a_5603_, v_a_5604_, v_a_5605_, v_a_5606_);
lean_dec(v_a_5606_);
lean_dec_ref(v_a_5605_);
lean_dec(v_a_5604_);
lean_dec_ref(v_a_5603_);
return v_res_5608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5609_, lean_object* v_us_5610_, lean_object* v_args1_5611_, lean_object* v___x_5612_, lean_object* v_numParams_5613_, lean_object* v___x_5614_, lean_object* v_args2_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_){
_start:
{
lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
lean_inc(v_us_5610_);
v___x_5621_ = l_Lean_mkConst(v_name_5609_, v_us_5610_);
lean_inc_ref(v___x_5621_);
v___x_5622_ = l_Lean_mkAppN(v___x_5621_, v_args1_5611_);
v___x_5623_ = l_Lean_mkAppN(v___x_5621_, v_args2_5615_);
lean_inc_ref(v___x_5623_);
lean_inc_ref(v___x_5622_);
v___x_5624_ = l_Lean_Meta_mkEqHEq(v___x_5622_, v___x_5623_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5624_) == 0)
{
lean_object* v_a_5625_; lean_object* v___x_5626_; uint8_t v___x_5627_; lean_object* v___x_5628_; 
v_a_5625_ = lean_ctor_get(v___x_5624_, 0);
lean_inc(v_a_5625_);
lean_dec_ref_known(v___x_5624_, 1);
lean_inc_ref_n(v_args2_5615_, 2);
v___x_5626_ = l_Array_toSubarray___redArg(v_args2_5615_, v___x_5612_, v_numParams_5613_);
v___x_5627_ = 1;
v___x_5628_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5611_, v_args2_5615_, v___x_5627_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5628_) == 0)
{
lean_object* v_a_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5749_; 
v_a_5629_ = lean_ctor_get(v___x_5628_, 0);
v_isSharedCheck_5749_ = !lean_is_exclusive(v___x_5628_);
if (v_isSharedCheck_5749_ == 0)
{
v___x_5631_ = v___x_5628_;
v_isShared_5632_ = v_isSharedCheck_5749_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_a_5629_);
lean_dec(v___x_5628_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5749_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5633_; 
v___x_5633_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5629_);
if (lean_obj_tag(v___x_5633_) == 1)
{
lean_object* v_val_5634_; lean_object* v___x_5635_; 
lean_del_object(v___x_5631_);
v_val_5634_ = lean_ctor_get(v___x_5633_, 0);
lean_inc(v_val_5634_);
lean_dec_ref_known(v___x_5633_, 1);
v___x_5635_ = l_Lean_mkArrow(v_a_5625_, v_val_5634_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5635_) == 0)
{
lean_object* v_a_5636_; lean_object* v___x_5637_; 
v_a_5636_ = lean_ctor_get(v___x_5635_, 0);
lean_inc(v_a_5636_);
lean_dec_ref_known(v___x_5635_, 1);
v___x_5637_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5622_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5637_) == 0)
{
lean_object* v_a_5638_; lean_object* v___x_5640_; uint8_t v_isShared_5641_; uint8_t v_isSharedCheck_5728_; 
v_a_5638_ = lean_ctor_get(v___x_5637_, 0);
v_isSharedCheck_5728_ = !lean_is_exclusive(v___x_5637_);
if (v_isSharedCheck_5728_ == 0)
{
v___x_5640_ = v___x_5637_;
v_isShared_5641_ = v_isSharedCheck_5728_;
goto v_resetjp_5639_;
}
else
{
lean_inc(v_a_5638_);
lean_dec(v___x_5637_);
v___x_5640_ = lean_box(0);
v_isShared_5641_ = v_isSharedCheck_5728_;
goto v_resetjp_5639_;
}
v_resetjp_5639_:
{
if (lean_obj_tag(v_a_5638_) == 1)
{
lean_object* v_val_5642_; lean_object* v___x_5643_; 
lean_del_object(v___x_5640_);
v_val_5642_ = lean_ctor_get(v_a_5638_, 0);
lean_inc(v_val_5642_);
lean_dec_ref_known(v_a_5638_, 1);
v___x_5643_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5623_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5643_) == 0)
{
lean_object* v_a_5644_; lean_object* v___x_5646_; uint8_t v_isShared_5647_; uint8_t v_isSharedCheck_5715_; 
v_a_5644_ = lean_ctor_get(v___x_5643_, 0);
v_isSharedCheck_5715_ = !lean_is_exclusive(v___x_5643_);
if (v_isSharedCheck_5715_ == 0)
{
v___x_5646_ = v___x_5643_;
v_isShared_5647_ = v_isSharedCheck_5715_;
goto v_resetjp_5645_;
}
else
{
lean_inc(v_a_5644_);
lean_dec(v___x_5643_);
v___x_5646_ = lean_box(0);
v_isShared_5647_ = v_isSharedCheck_5715_;
goto v_resetjp_5645_;
}
v_resetjp_5645_:
{
if (lean_obj_tag(v_a_5644_) == 1)
{
lean_object* v_val_5648_; lean_object* v___x_5650_; uint8_t v_isShared_5651_; uint8_t v_isSharedCheck_5710_; 
lean_del_object(v___x_5646_);
v_val_5648_ = lean_ctor_get(v_a_5644_, 0);
v_isSharedCheck_5710_ = !lean_is_exclusive(v_a_5644_);
if (v_isSharedCheck_5710_ == 0)
{
v___x_5650_ = v_a_5644_;
v_isShared_5651_ = v_isSharedCheck_5710_;
goto v_resetjp_5649_;
}
else
{
lean_inc(v_val_5648_);
lean_dec(v_a_5644_);
v___x_5650_ = lean_box(0);
v_isShared_5651_ = v_isSharedCheck_5710_;
goto v_resetjp_5649_;
}
v_resetjp_5649_:
{
lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; uint8_t v___x_5656_; lean_object* v___x_5657_; 
v___x_5652_ = l_Subarray_copy___redArg(v___x_5614_);
v___x_5653_ = l_Array_append___redArg(v___x_5652_, v_val_5642_);
v___x_5654_ = l_Subarray_copy___redArg(v___x_5626_);
v___x_5655_ = l_Array_append___redArg(v___x_5654_, v_val_5648_);
lean_dec(v_val_5648_);
v___x_5656_ = 0;
v___x_5657_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5653_, v___x_5655_, v___x_5656_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
lean_dec_ref(v___x_5653_);
if (lean_obj_tag(v___x_5657_) == 0)
{
lean_object* v_a_5658_; lean_object* v___x_5659_; 
v_a_5658_ = lean_ctor_get(v___x_5657_, 0);
lean_inc(v_a_5658_);
lean_dec_ref_known(v___x_5657_, 1);
v___x_5659_ = l_Lean_mkArrowN(v_a_5658_, v_a_5636_, v___y_5618_, v___y_5619_);
lean_dec(v_a_5658_);
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_object* v_a_5660_; uint8_t v___x_5661_; lean_object* v___x_5662_; 
v_a_5660_ = lean_ctor_get(v___x_5659_, 0);
lean_inc(v_a_5660_);
lean_dec_ref_known(v___x_5659_, 1);
v___x_5661_ = 1;
v___x_5662_ = l_Lean_Meta_mkForallFVars(v_args2_5615_, v_a_5660_, v___x_5656_, v___x_5627_, v___x_5627_, v___x_5661_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
lean_dec_ref(v_args2_5615_);
if (lean_obj_tag(v___x_5662_) == 0)
{
lean_object* v_a_5663_; lean_object* v___x_5664_; 
v_a_5663_ = lean_ctor_get(v___x_5662_, 0);
lean_inc(v_a_5663_);
lean_dec_ref_known(v___x_5662_, 1);
v___x_5664_ = l_Lean_Meta_mkForallFVars(v_args1_5611_, v_a_5663_, v___x_5656_, v___x_5627_, v___x_5627_, v___x_5661_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
if (lean_obj_tag(v___x_5664_) == 0)
{
lean_object* v_a_5665_; lean_object* v___x_5667_; uint8_t v_isShared_5668_; uint8_t v_isSharedCheck_5677_; 
v_a_5665_ = lean_ctor_get(v___x_5664_, 0);
v_isSharedCheck_5677_ = !lean_is_exclusive(v___x_5664_);
if (v_isSharedCheck_5677_ == 0)
{
v___x_5667_ = v___x_5664_;
v_isShared_5668_ = v_isSharedCheck_5677_;
goto v_resetjp_5666_;
}
else
{
lean_inc(v_a_5665_);
lean_dec(v___x_5664_);
v___x_5667_ = lean_box(0);
v_isShared_5668_ = v_isSharedCheck_5677_;
goto v_resetjp_5666_;
}
v_resetjp_5666_:
{
lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5672_; 
v___x_5669_ = lean_array_get_size(v_val_5642_);
lean_dec(v_val_5642_);
v___x_5670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5670_, 0, v_a_5665_);
lean_ctor_set(v___x_5670_, 1, v_us_5610_);
lean_ctor_set(v___x_5670_, 2, v___x_5669_);
if (v_isShared_5651_ == 0)
{
lean_ctor_set(v___x_5650_, 0, v___x_5670_);
v___x_5672_ = v___x_5650_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v___x_5670_);
v___x_5672_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
lean_object* v___x_5674_; 
if (v_isShared_5668_ == 0)
{
lean_ctor_set(v___x_5667_, 0, v___x_5672_);
v___x_5674_ = v___x_5667_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v___x_5672_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
else
{
lean_object* v_a_5678_; lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5685_; 
lean_del_object(v___x_5650_);
lean_dec(v_val_5642_);
lean_dec(v_us_5610_);
v_a_5678_ = lean_ctor_get(v___x_5664_, 0);
v_isSharedCheck_5685_ = !lean_is_exclusive(v___x_5664_);
if (v_isSharedCheck_5685_ == 0)
{
v___x_5680_ = v___x_5664_;
v_isShared_5681_ = v_isSharedCheck_5685_;
goto v_resetjp_5679_;
}
else
{
lean_inc(v_a_5678_);
lean_dec(v___x_5664_);
v___x_5680_ = lean_box(0);
v_isShared_5681_ = v_isSharedCheck_5685_;
goto v_resetjp_5679_;
}
v_resetjp_5679_:
{
lean_object* v___x_5683_; 
if (v_isShared_5681_ == 0)
{
v___x_5683_ = v___x_5680_;
goto v_reusejp_5682_;
}
else
{
lean_object* v_reuseFailAlloc_5684_; 
v_reuseFailAlloc_5684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5684_, 0, v_a_5678_);
v___x_5683_ = v_reuseFailAlloc_5684_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
return v___x_5683_;
}
}
}
}
else
{
lean_object* v_a_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5693_; 
lean_del_object(v___x_5650_);
lean_dec(v_val_5642_);
lean_dec(v_us_5610_);
v_a_5686_ = lean_ctor_get(v___x_5662_, 0);
v_isSharedCheck_5693_ = !lean_is_exclusive(v___x_5662_);
if (v_isSharedCheck_5693_ == 0)
{
v___x_5688_ = v___x_5662_;
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
else
{
lean_inc(v_a_5686_);
lean_dec(v___x_5662_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v___x_5691_; 
if (v_isShared_5689_ == 0)
{
v___x_5691_ = v___x_5688_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_a_5686_);
v___x_5691_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
return v___x_5691_;
}
}
}
}
else
{
lean_object* v_a_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5701_; 
lean_del_object(v___x_5650_);
lean_dec(v_val_5642_);
lean_dec_ref(v_args2_5615_);
lean_dec(v_us_5610_);
v_a_5694_ = lean_ctor_get(v___x_5659_, 0);
v_isSharedCheck_5701_ = !lean_is_exclusive(v___x_5659_);
if (v_isSharedCheck_5701_ == 0)
{
v___x_5696_ = v___x_5659_;
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_a_5694_);
lean_dec(v___x_5659_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v___x_5699_; 
if (v_isShared_5697_ == 0)
{
v___x_5699_ = v___x_5696_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_a_5694_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
}
}
else
{
lean_object* v_a_5702_; lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5709_; 
lean_del_object(v___x_5650_);
lean_dec(v_val_5642_);
lean_dec(v_a_5636_);
lean_dec_ref(v_args2_5615_);
lean_dec(v_us_5610_);
v_a_5702_ = lean_ctor_get(v___x_5657_, 0);
v_isSharedCheck_5709_ = !lean_is_exclusive(v___x_5657_);
if (v_isSharedCheck_5709_ == 0)
{
v___x_5704_ = v___x_5657_;
v_isShared_5705_ = v_isSharedCheck_5709_;
goto v_resetjp_5703_;
}
else
{
lean_inc(v_a_5702_);
lean_dec(v___x_5657_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5709_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v___x_5707_; 
if (v_isShared_5705_ == 0)
{
v___x_5707_ = v___x_5704_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5708_; 
v_reuseFailAlloc_5708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_a_5702_);
v___x_5707_ = v_reuseFailAlloc_5708_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
return v___x_5707_;
}
}
}
}
}
else
{
lean_object* v___x_5711_; lean_object* v___x_5713_; 
lean_dec(v_a_5644_);
lean_dec(v_val_5642_);
lean_dec(v_a_5636_);
lean_dec_ref(v___x_5626_);
lean_dec_ref(v_args2_5615_);
lean_dec_ref(v___x_5614_);
lean_dec(v_us_5610_);
v___x_5711_ = lean_box(0);
if (v_isShared_5647_ == 0)
{
lean_ctor_set(v___x_5646_, 0, v___x_5711_);
v___x_5713_ = v___x_5646_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v___x_5711_);
v___x_5713_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
return v___x_5713_;
}
}
}
}
else
{
lean_object* v_a_5716_; lean_object* v___x_5718_; uint8_t v_isShared_5719_; uint8_t v_isSharedCheck_5723_; 
lean_dec(v_val_5642_);
lean_dec(v_a_5636_);
lean_dec_ref(v___x_5626_);
lean_dec_ref(v_args2_5615_);
lean_dec_ref(v___x_5614_);
lean_dec(v_us_5610_);
v_a_5716_ = lean_ctor_get(v___x_5643_, 0);
v_isSharedCheck_5723_ = !lean_is_exclusive(v___x_5643_);
if (v_isSharedCheck_5723_ == 0)
{
v___x_5718_ = v___x_5643_;
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
else
{
lean_inc(v_a_5716_);
lean_dec(v___x_5643_);
v___x_5718_ = lean_box(0);
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
v_resetjp_5717_:
{
lean_object* v___x_5721_; 
if (v_isShared_5719_ == 0)
{
v___x_5721_ = v___x_5718_;
goto v_reusejp_5720_;
}
else
{
lean_object* v_reuseFailAlloc_5722_; 
v_reuseFailAlloc_5722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5722_, 0, v_a_5716_);
v___x_5721_ = v_reuseFailAlloc_5722_;
goto v_reusejp_5720_;
}
v_reusejp_5720_:
{
return v___x_5721_;
}
}
}
}
else
{
lean_object* v___x_5724_; lean_object* v___x_5726_; 
lean_dec(v_a_5638_);
lean_dec(v_a_5636_);
lean_dec_ref(v___x_5626_);
lean_dec_ref(v___x_5623_);
lean_dec_ref(v_args2_5615_);
lean_dec_ref(v___x_5614_);
lean_dec(v_us_5610_);
v___x_5724_ = lean_box(0);
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 0, v___x_5724_);
v___x_5726_ = v___x_5640_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v___x_5724_);
v___x_5726_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
return v___x_5726_;
}
}
}
}
else
{
lean_object* v_a_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5736_; 
lean_dec(v_a_5636_);
lean_dec_ref(v___x_5626_);
lean_dec_ref(v___x_5623_);
lean_dec_ref(v_args2_5615_);
lean_dec_ref(v___x_5614_);
lean_dec(v_us_5610_);
v_a_5729_ = lean_ctor_get(v___x_5637_, 0);
v_isSharedCheck_5736_ = !lean_is_exclusive(v___x_5637_);
if (v_isSharedCheck_5736_ == 0)
{
v___x_5731_ = v___x_5637_;
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_a_5729_);
lean_dec(v___x_5637_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5734_; 
if (v_isShared_5732_ == 0)
{
v___x_5734_ = v___x_5731_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5729_);
v___x_5734_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
return v___x_5734_;
}
}
}
}
else
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5744_; 
lean_dec_ref(v___x_5626_);
lean_dec_ref(v___x_5623_);
lean_dec_ref(v___x_5622_);
lean_dec_ref(v_args2_5615_);
lean_dec_ref(v___x_5614_);
lean_dec(v_us_5610_);
v_a_5737_ = lean_ctor_get(v___x_5635_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v___x_5635_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5739_ = v___x_5635_;
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5635_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v___x_5742_; 
if (v_isShared_5740_ == 0)
{
v___x_5742_ = v___x_5739_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
v___x_5742_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
return v___x_5742_;
}
}
}
}
else
{
lean_object* v___x_5745_; lean_object* v___x_5747_; 
lean_dec(v___x_5633_);
lean_dec_ref(v___x_5626_);
lean_dec(v_a_5625_);
lean_dec_ref(v___x_5623_);
lean_dec_ref(v___x_5622_);
lean_dec_ref(v_args2_5615_);
lean_dec_ref(v___x_5614_);
lean_dec(v_us_5610_);
v___x_5745_ = lean_box(0);
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 0, v___x_5745_);
v___x_5747_ = v___x_5631_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5748_; 
v_reuseFailAlloc_5748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5748_, 0, v___x_5745_);
v___x_5747_ = v_reuseFailAlloc_5748_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
return v___x_5747_;
}
}
}
}
else
{
lean_object* v_a_5750_; lean_object* v___x_5752_; uint8_t v_isShared_5753_; uint8_t v_isSharedCheck_5757_; 
lean_dec_ref(v___x_5626_);
lean_dec(v_a_5625_);
lean_dec_ref(v___x_5623_);
lean_dec_ref(v___x_5622_);
lean_dec_ref(v_args2_5615_);
lean_dec_ref(v___x_5614_);
lean_dec(v_us_5610_);
v_a_5750_ = lean_ctor_get(v___x_5628_, 0);
v_isSharedCheck_5757_ = !lean_is_exclusive(v___x_5628_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5752_ = v___x_5628_;
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
else
{
lean_inc(v_a_5750_);
lean_dec(v___x_5628_);
v___x_5752_ = lean_box(0);
v_isShared_5753_ = v_isSharedCheck_5757_;
goto v_resetjp_5751_;
}
v_resetjp_5751_:
{
lean_object* v___x_5755_; 
if (v_isShared_5753_ == 0)
{
v___x_5755_ = v___x_5752_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_a_5750_);
v___x_5755_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
return v___x_5755_;
}
}
}
}
else
{
lean_object* v_a_5758_; lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5765_; 
lean_dec_ref(v___x_5623_);
lean_dec_ref(v___x_5622_);
lean_dec_ref(v_args2_5615_);
lean_dec_ref(v___x_5614_);
lean_dec(v_numParams_5613_);
lean_dec(v___x_5612_);
lean_dec(v_us_5610_);
v_a_5758_ = lean_ctor_get(v___x_5624_, 0);
v_isSharedCheck_5765_ = !lean_is_exclusive(v___x_5624_);
if (v_isSharedCheck_5765_ == 0)
{
v___x_5760_ = v___x_5624_;
v_isShared_5761_ = v_isSharedCheck_5765_;
goto v_resetjp_5759_;
}
else
{
lean_inc(v_a_5758_);
lean_dec(v___x_5624_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5765_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v___x_5763_; 
if (v_isShared_5761_ == 0)
{
v___x_5763_ = v___x_5760_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5764_; 
v_reuseFailAlloc_5764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5764_, 0, v_a_5758_);
v___x_5763_ = v_reuseFailAlloc_5764_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
return v___x_5763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5766_, lean_object* v_us_5767_, lean_object* v_args1_5768_, lean_object* v___x_5769_, lean_object* v_numParams_5770_, lean_object* v___x_5771_, lean_object* v_args2_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_){
_start:
{
lean_object* v_res_5778_; 
v_res_5778_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5766_, v_us_5767_, v_args1_5768_, v___x_5769_, v_numParams_5770_, v___x_5771_, v_args2_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
lean_dec(v___y_5776_);
lean_dec_ref(v___y_5775_);
lean_dec(v___y_5774_);
lean_dec_ref(v___y_5773_);
lean_dec_ref(v_args1_5768_);
return v_res_5778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5779_, lean_object* v_name_5780_, lean_object* v_us_5781_, lean_object* v_ctorVal_5782_, lean_object* v_a_5783_, lean_object* v_args1_5784_, lean_object* v_x_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_){
_start:
{
lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___f_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; 
v___x_5791_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5779_);
lean_inc_ref_n(v_args1_5784_, 3);
v___x_5792_ = l_Array_toSubarray___redArg(v_args1_5784_, v___x_5791_, v_numParams_5779_);
v___f_5793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5793_, 0, v_name_5780_);
lean_closure_set(v___f_5793_, 1, v_us_5781_);
lean_closure_set(v___f_5793_, 2, v_args1_5784_);
lean_closure_set(v___f_5793_, 3, v___x_5791_);
lean_closure_set(v___f_5793_, 4, v_numParams_5779_);
lean_closure_set(v___f_5793_, 5, v___x_5792_);
v___x_5794_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5795_, 0, v_ctorVal_5782_);
lean_closure_set(v___x_5795_, 1, v_args1_5784_);
lean_closure_set(v___x_5795_, 2, v___f_5793_);
lean_closure_set(v___x_5795_, 3, v___x_5791_);
lean_closure_set(v___x_5795_, 4, v_a_5783_);
lean_closure_set(v___x_5795_, 5, v___x_5794_);
v___x_5796_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5784_, v___x_5795_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
return v___x_5796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5797_, lean_object* v_name_5798_, lean_object* v_us_5799_, lean_object* v_ctorVal_5800_, lean_object* v_a_5801_, lean_object* v_args1_5802_, lean_object* v_x_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_){
_start:
{
lean_object* v_res_5809_; 
v_res_5809_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5797_, v_name_5798_, v_us_5799_, v_ctorVal_5800_, v_a_5801_, v_args1_5802_, v_x_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_);
lean_dec(v___y_5807_);
lean_dec_ref(v___y_5806_);
lean_dec(v___y_5805_);
lean_dec_ref(v___y_5804_);
lean_dec_ref(v_x_5803_);
return v_res_5809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_){
_start:
{
lean_object* v_toConstantVal_5816_; lean_object* v_numParams_5817_; lean_object* v_name_5818_; lean_object* v_levelParams_5819_; lean_object* v_type_5820_; lean_object* v___x_5821_; 
v_toConstantVal_5816_ = lean_ctor_get(v_ctorVal_5810_, 0);
v_numParams_5817_ = lean_ctor_get(v_ctorVal_5810_, 3);
lean_inc(v_numParams_5817_);
v_name_5818_ = lean_ctor_get(v_toConstantVal_5816_, 0);
lean_inc(v_name_5818_);
v_levelParams_5819_ = lean_ctor_get(v_toConstantVal_5816_, 1);
v_type_5820_ = lean_ctor_get(v_toConstantVal_5816_, 2);
lean_inc_ref(v_type_5820_);
v___x_5821_ = l_Lean_Meta_elimOptParam(v_type_5820_, v_a_5813_, v_a_5814_);
if (lean_obj_tag(v___x_5821_) == 0)
{
lean_object* v_a_5822_; lean_object* v___x_5823_; lean_object* v_us_5824_; lean_object* v___f_5825_; uint8_t v___x_5826_; lean_object* v___x_5827_; 
v_a_5822_ = lean_ctor_get(v___x_5821_, 0);
lean_inc_n(v_a_5822_, 2);
lean_dec_ref_known(v___x_5821_, 1);
v___x_5823_ = lean_box(0);
lean_inc(v_levelParams_5819_);
v_us_5824_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5819_, v___x_5823_);
v___f_5825_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5825_, 0, v_numParams_5817_);
lean_closure_set(v___f_5825_, 1, v_name_5818_);
lean_closure_set(v___f_5825_, 2, v_us_5824_);
lean_closure_set(v___f_5825_, 3, v_ctorVal_5810_);
lean_closure_set(v___f_5825_, 4, v_a_5822_);
v___x_5826_ = 0;
v___x_5827_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5822_, v___f_5825_, v___x_5826_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_);
return v___x_5827_;
}
else
{
lean_object* v_a_5828_; lean_object* v___x_5830_; uint8_t v_isShared_5831_; uint8_t v_isSharedCheck_5835_; 
lean_dec(v_name_5818_);
lean_dec(v_numParams_5817_);
lean_dec_ref(v_ctorVal_5810_);
v_a_5828_ = lean_ctor_get(v___x_5821_, 0);
v_isSharedCheck_5835_ = !lean_is_exclusive(v___x_5821_);
if (v_isSharedCheck_5835_ == 0)
{
v___x_5830_ = v___x_5821_;
v_isShared_5831_ = v_isSharedCheck_5835_;
goto v_resetjp_5829_;
}
else
{
lean_inc(v_a_5828_);
lean_dec(v___x_5821_);
v___x_5830_ = lean_box(0);
v_isShared_5831_ = v_isSharedCheck_5835_;
goto v_resetjp_5829_;
}
v_resetjp_5829_:
{
lean_object* v___x_5833_; 
if (v_isShared_5831_ == 0)
{
v___x_5833_ = v___x_5830_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_a_5828_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
return v___x_5833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_){
_start:
{
lean_object* v_res_5842_; 
v_res_5842_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_);
lean_dec(v_a_5840_);
lean_dec_ref(v_a_5839_);
lean_dec(v_a_5838_);
lean_dec_ref(v_a_5837_);
return v_res_5842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5844_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5845_ = l_Lean_stringToMessageData(v___x_5844_);
return v___x_5845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_){
_start:
{
lean_object* v_toConstantVal_5852_; lean_object* v_name_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; 
v_toConstantVal_5852_ = lean_ctor_get(v_ctorVal_5846_, 0);
lean_inc_ref(v_toConstantVal_5852_);
lean_dec_ref(v_ctorVal_5846_);
v_name_5853_ = lean_ctor_get(v_toConstantVal_5852_, 0);
lean_inc(v_name_5853_);
lean_dec_ref(v_toConstantVal_5852_);
v___x_5854_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5855_ = l_Lean_MessageData_ofName(v_name_5853_);
v___x_5856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5854_);
lean_ctor_set(v___x_5856_, 1, v___x_5855_);
v___x_5857_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5856_);
lean_ctor_set(v___x_5858_, 1, v___x_5857_);
v___x_5859_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5858_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_);
return v___x_5859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_, lean_object* v_a_5863_, lean_object* v_a_5864_, lean_object* v_a_5865_){
_start:
{
lean_object* v_res_5866_; 
v_res_5866_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5860_, v_a_5861_, v_a_5862_, v_a_5863_, v_a_5864_);
lean_dec(v_a_5864_);
lean_dec_ref(v_a_5863_);
lean_dec(v_a_5862_);
lean_dec_ref(v_a_5861_);
return v_res_5866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5867_, lean_object* v_ctorVal_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_){
_start:
{
lean_object* v___x_5874_; 
v___x_5874_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5868_, v_a_5869_, v_a_5870_, v_a_5871_, v_a_5872_);
return v___x_5874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5875_, lean_object* v_ctorVal_5876_, lean_object* v_a_5877_, lean_object* v_a_5878_, lean_object* v_a_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_){
_start:
{
lean_object* v_res_5882_; 
v_res_5882_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5875_, v_ctorVal_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_);
lean_dec(v_a_5880_);
lean_dec_ref(v_a_5879_);
lean_dec(v_a_5878_);
lean_dec_ref(v_a_5877_);
return v_res_5882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5888_, size_t v_sz_5889_, size_t v_i_5890_, lean_object* v_bs_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_){
_start:
{
uint8_t v___x_5897_; 
v___x_5897_ = lean_usize_dec_lt(v_i_5890_, v_sz_5889_);
if (v___x_5897_ == 0)
{
lean_object* v___x_5898_; 
lean_dec_ref(v_ctorVal_5888_);
v___x_5898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5898_, 0, v_bs_5891_);
return v___x_5898_;
}
else
{
lean_object* v_v_5899_; lean_object* v___x_5900_; 
v_v_5899_ = lean_array_uget_borrowed(v_bs_5891_, v_i_5890_);
lean_inc(v___y_5895_);
lean_inc_ref(v___y_5894_);
lean_inc(v___y_5893_);
lean_inc_ref(v___y_5892_);
lean_inc(v_v_5899_);
v___x_5900_ = lean_infer_type(v_v_5899_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
if (lean_obj_tag(v___x_5900_) == 0)
{
lean_object* v_a_5901_; lean_object* v___x_5902_; 
v_a_5901_ = lean_ctor_get(v___x_5900_, 0);
lean_inc(v_a_5901_);
lean_dec_ref_known(v___x_5900_, 1);
v___x_5902_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5901_, v___y_5893_);
if (lean_obj_tag(v___x_5902_) == 0)
{
lean_object* v_a_5903_; lean_object* v___x_5904_; lean_object* v_bs_x27_5905_; lean_object* v_a_5907_; lean_object* v___y_5913_; lean_object* v_lhs_5924_; lean_object* v_rhs_5925_; lean_object* v___x_5927_; uint8_t v___x_5928_; 
v_a_5903_ = lean_ctor_get(v___x_5902_, 0);
lean_inc(v_a_5903_);
lean_dec_ref_known(v___x_5902_, 1);
v___x_5904_ = lean_unsigned_to_nat(0u);
v_bs_x27_5905_ = lean_array_uset(v_bs_5891_, v_i_5890_, v___x_5904_);
v___x_5927_ = l_Lean_Expr_cleanupAnnotations(v_a_5903_);
v___x_5928_ = l_Lean_Expr_isApp(v___x_5927_);
if (v___x_5928_ == 0)
{
lean_object* v___x_5929_; 
lean_dec_ref(v___x_5927_);
lean_inc_ref(v_ctorVal_5888_);
v___x_5929_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5888_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
v___y_5913_ = v___x_5929_;
goto v___jp_5912_;
}
else
{
lean_object* v_arg_5930_; lean_object* v___x_5931_; uint8_t v___x_5932_; 
v_arg_5930_ = lean_ctor_get(v___x_5927_, 1);
lean_inc_ref(v_arg_5930_);
v___x_5931_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5927_);
v___x_5932_ = l_Lean_Expr_isApp(v___x_5931_);
if (v___x_5932_ == 0)
{
lean_object* v___x_5933_; 
lean_dec_ref(v___x_5931_);
lean_dec_ref(v_arg_5930_);
lean_inc_ref(v_ctorVal_5888_);
v___x_5933_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5888_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
v___y_5913_ = v___x_5933_;
goto v___jp_5912_;
}
else
{
lean_object* v_arg_5934_; lean_object* v___x_5935_; uint8_t v___x_5936_; 
v_arg_5934_ = lean_ctor_get(v___x_5931_, 1);
lean_inc_ref(v_arg_5934_);
v___x_5935_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5931_);
v___x_5936_ = l_Lean_Expr_isApp(v___x_5935_);
if (v___x_5936_ == 0)
{
lean_object* v___x_5937_; 
lean_dec_ref(v___x_5935_);
lean_dec_ref(v_arg_5934_);
lean_dec_ref(v_arg_5930_);
lean_inc_ref(v_ctorVal_5888_);
v___x_5937_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5888_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
v___y_5913_ = v___x_5937_;
goto v___jp_5912_;
}
else
{
lean_object* v_arg_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; uint8_t v___x_5941_; 
v_arg_5938_ = lean_ctor_get(v___x_5935_, 1);
lean_inc_ref(v_arg_5938_);
v___x_5939_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5935_);
v___x_5940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5941_ = l_Lean_Expr_isConstOf(v___x_5939_, v___x_5940_);
if (v___x_5941_ == 0)
{
uint8_t v___x_5942_; 
lean_dec_ref(v_arg_5934_);
v___x_5942_ = l_Lean_Expr_isApp(v___x_5939_);
if (v___x_5942_ == 0)
{
lean_object* v___x_5943_; 
lean_dec_ref(v___x_5939_);
lean_dec_ref(v_arg_5938_);
lean_dec_ref(v_arg_5930_);
lean_inc_ref(v_ctorVal_5888_);
v___x_5943_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5888_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
v___y_5913_ = v___x_5943_;
goto v___jp_5912_;
}
else
{
lean_object* v___x_5944_; lean_object* v___x_5945_; uint8_t v___x_5946_; 
v___x_5944_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5939_);
v___x_5945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5946_ = l_Lean_Expr_isConstOf(v___x_5944_, v___x_5945_);
lean_dec_ref(v___x_5944_);
if (v___x_5946_ == 0)
{
lean_object* v___x_5947_; 
lean_dec_ref(v_arg_5938_);
lean_dec_ref(v_arg_5930_);
lean_inc_ref(v_ctorVal_5888_);
v___x_5947_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5888_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_);
v___y_5913_ = v___x_5947_;
goto v___jp_5912_;
}
else
{
v_lhs_5924_ = v_arg_5938_;
v_rhs_5925_ = v_arg_5930_;
goto v___jp_5923_;
}
}
}
else
{
lean_dec_ref(v___x_5939_);
lean_dec_ref(v_arg_5938_);
v_lhs_5924_ = v_arg_5934_;
v_rhs_5925_ = v_arg_5930_;
goto v___jp_5923_;
}
}
}
}
v___jp_5906_:
{
size_t v___x_5908_; size_t v___x_5909_; lean_object* v___x_5910_; 
v___x_5908_ = ((size_t)1ULL);
v___x_5909_ = lean_usize_add(v_i_5890_, v___x_5908_);
v___x_5910_ = lean_array_uset(v_bs_x27_5905_, v_i_5890_, v_a_5907_);
v_i_5890_ = v___x_5909_;
v_bs_5891_ = v___x_5910_;
goto _start;
}
v___jp_5912_:
{
if (lean_obj_tag(v___y_5913_) == 0)
{
lean_object* v_a_5914_; 
v_a_5914_ = lean_ctor_get(v___y_5913_, 0);
lean_inc(v_a_5914_);
lean_dec_ref_known(v___y_5913_, 1);
v_a_5907_ = v_a_5914_;
goto v___jp_5906_;
}
else
{
lean_object* v_a_5915_; lean_object* v___x_5917_; uint8_t v_isShared_5918_; uint8_t v_isSharedCheck_5922_; 
lean_dec_ref(v_bs_x27_5905_);
lean_dec_ref(v_ctorVal_5888_);
v_a_5915_ = lean_ctor_get(v___y_5913_, 0);
v_isSharedCheck_5922_ = !lean_is_exclusive(v___y_5913_);
if (v_isSharedCheck_5922_ == 0)
{
v___x_5917_ = v___y_5913_;
v_isShared_5918_ = v_isSharedCheck_5922_;
goto v_resetjp_5916_;
}
else
{
lean_inc(v_a_5915_);
lean_dec(v___y_5913_);
v___x_5917_ = lean_box(0);
v_isShared_5918_ = v_isSharedCheck_5922_;
goto v_resetjp_5916_;
}
v_resetjp_5916_:
{
lean_object* v___x_5920_; 
if (v_isShared_5918_ == 0)
{
v___x_5920_ = v___x_5917_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5921_; 
v_reuseFailAlloc_5921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5921_, 0, v_a_5915_);
v___x_5920_ = v_reuseFailAlloc_5921_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
return v___x_5920_;
}
}
}
}
v___jp_5923_:
{
lean_object* v___x_5926_; 
v___x_5926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5926_, 0, v_lhs_5924_);
lean_ctor_set(v___x_5926_, 1, v_rhs_5925_);
v_a_5907_ = v___x_5926_;
goto v___jp_5906_;
}
}
else
{
lean_object* v_a_5948_; lean_object* v___x_5950_; uint8_t v_isShared_5951_; uint8_t v_isSharedCheck_5955_; 
lean_dec_ref(v_bs_5891_);
lean_dec_ref(v_ctorVal_5888_);
v_a_5948_ = lean_ctor_get(v___x_5902_, 0);
v_isSharedCheck_5955_ = !lean_is_exclusive(v___x_5902_);
if (v_isSharedCheck_5955_ == 0)
{
v___x_5950_ = v___x_5902_;
v_isShared_5951_ = v_isSharedCheck_5955_;
goto v_resetjp_5949_;
}
else
{
lean_inc(v_a_5948_);
lean_dec(v___x_5902_);
v___x_5950_ = lean_box(0);
v_isShared_5951_ = v_isSharedCheck_5955_;
goto v_resetjp_5949_;
}
v_resetjp_5949_:
{
lean_object* v___x_5953_; 
if (v_isShared_5951_ == 0)
{
v___x_5953_ = v___x_5950_;
goto v_reusejp_5952_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_a_5948_);
v___x_5953_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5952_;
}
v_reusejp_5952_:
{
return v___x_5953_;
}
}
}
}
else
{
lean_object* v_a_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5963_; 
lean_dec_ref(v_bs_5891_);
lean_dec_ref(v_ctorVal_5888_);
v_a_5956_ = lean_ctor_get(v___x_5900_, 0);
v_isSharedCheck_5963_ = !lean_is_exclusive(v___x_5900_);
if (v_isSharedCheck_5963_ == 0)
{
v___x_5958_ = v___x_5900_;
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_a_5956_);
lean_dec(v___x_5900_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v___x_5961_; 
if (v_isShared_5959_ == 0)
{
v___x_5961_ = v___x_5958_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
v___x_5961_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
return v___x_5961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5964_, lean_object* v_sz_5965_, lean_object* v_i_5966_, lean_object* v_bs_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_){
_start:
{
size_t v_sz_boxed_5973_; size_t v_i_boxed_5974_; lean_object* v_res_5975_; 
v_sz_boxed_5973_ = lean_unbox_usize(v_sz_5965_);
lean_dec(v_sz_5965_);
v_i_boxed_5974_ = lean_unbox_usize(v_i_5966_);
lean_dec(v_i_5966_);
v_res_5975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5964_, v_sz_boxed_5973_, v_i_boxed_5974_, v_bs_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_);
lean_dec(v___y_5971_);
lean_dec_ref(v___y_5970_);
lean_dec(v___y_5969_);
lean_dec_ref(v___y_5968_);
return v_res_5975_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5977_ = lean_unsigned_to_nat(0u);
v___x_5978_ = l_Lean_Level_ofNat(v___x_5977_);
return v___x_5978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5979_, lean_object* v_us_5980_, lean_object* v_numIndices_5981_, lean_object* v_xs_5982_, lean_object* v_type_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_){
_start:
{
lean_object* v_toConstantVal_5989_; lean_object* v_induct_5990_; lean_object* v_numParams_5991_; lean_object* v___x_5992_; lean_object* v_noConfusionName_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v_noConfusion_5997_; lean_object* v_noConfusion_5998_; lean_object* v_lower_6000_; lean_object* v_upper_6001_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v_n_6112_; uint8_t v___x_6113_; 
v_toConstantVal_5989_ = lean_ctor_get(v_ctorVal_5979_, 0);
v_induct_5990_ = lean_ctor_get(v_ctorVal_5979_, 1);
v_numParams_5991_ = lean_ctor_get(v_ctorVal_5979_, 3);
v___x_5992_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5990_);
v_noConfusionName_5993_ = l_Lean_Name_str___override(v_induct_5990_, v___x_5992_);
v___x_5994_ = lean_unsigned_to_nat(0u);
v___x_5995_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
lean_ctor_set(v___x_5996_, 1, v_us_5980_);
v_noConfusion_5997_ = l_Lean_mkConst(v_noConfusionName_5993_, v___x_5996_);
v_noConfusion_5998_ = l_Lean_Expr_app___override(v_noConfusion_5997_, v_type_5983_);
v___x_6108_ = lean_array_get_size(v_xs_5982_);
v___x_6109_ = lean_nat_sub(v___x_6108_, v_numParams_5991_);
v___x_6110_ = lean_nat_sub(v___x_6109_, v_numIndices_5981_);
lean_dec(v___x_6109_);
v___x_6111_ = lean_unsigned_to_nat(1u);
v_n_6112_ = lean_nat_sub(v___x_6110_, v___x_6111_);
lean_dec(v___x_6110_);
v___x_6113_ = lean_nat_dec_le(v_n_6112_, v___x_5994_);
if (v___x_6113_ == 0)
{
v_lower_6000_ = v_n_6112_;
v_upper_6001_ = v___x_6108_;
goto v___jp_5999_;
}
else
{
lean_dec(v_n_6112_);
v_lower_6000_ = v___x_5994_;
v_upper_6001_ = v___x_6108_;
goto v___jp_5999_;
}
v___jp_5999_:
{
lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v_eqs_6004_; size_t v_sz_6005_; size_t v___x_6006_; lean_object* v___x_6007_; 
lean_inc_ref(v_xs_5982_);
v___x_6002_ = l_Array_toSubarray___redArg(v_xs_5982_, v_lower_6000_, v_upper_6001_);
v___x_6003_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_6004_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_6002_, v___x_6003_);
v_sz_6005_ = lean_array_size(v_eqs_6004_);
v___x_6006_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_6004_);
lean_inc_ref(v_ctorVal_5979_);
v___x_6007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5979_, v_sz_6005_, v___x_6006_, v_eqs_6004_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
if (lean_obj_tag(v___x_6007_) == 0)
{
lean_object* v_a_6008_; lean_object* v___x_6009_; lean_object* v_fst_6010_; lean_object* v_snd_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; 
v_a_6008_ = lean_ctor_get(v___x_6007_, 0);
lean_inc(v_a_6008_);
lean_dec_ref_known(v___x_6007_, 1);
v___x_6009_ = l_Array_unzip___redArg(v_a_6008_);
lean_dec(v_a_6008_);
v_fst_6010_ = lean_ctor_get(v___x_6009_, 0);
lean_inc(v_fst_6010_);
v_snd_6011_ = lean_ctor_get(v___x_6009_, 1);
lean_inc(v_snd_6011_);
lean_dec_ref(v___x_6009_);
v___x_6012_ = l_Lean_mkAppN(v_noConfusion_5998_, v_fst_6010_);
lean_dec(v_fst_6010_);
v___x_6013_ = l_Lean_mkAppN(v___x_6012_, v_snd_6011_);
lean_dec(v_snd_6011_);
v___x_6014_ = l_Lean_mkAppN(v___x_6013_, v_eqs_6004_);
lean_dec_ref(v_eqs_6004_);
lean_inc(v___y_5987_);
lean_inc_ref(v___y_5986_);
lean_inc(v___y_5985_);
lean_inc_ref(v___y_5984_);
lean_inc_ref(v___x_6014_);
v___x_6015_ = lean_infer_type(v___x_6014_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
if (lean_obj_tag(v___x_6015_) == 0)
{
lean_object* v_a_6016_; lean_object* v___x_6017_; 
v_a_6016_ = lean_ctor_get(v___x_6015_, 0);
lean_inc(v_a_6016_);
lean_dec_ref_known(v___x_6015_, 1);
lean_inc(v___y_5987_);
lean_inc_ref(v___y_5986_);
lean_inc(v___y_5985_);
lean_inc_ref(v___y_5984_);
v___x_6017_ = lean_whnf(v_a_6016_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
if (lean_obj_tag(v___x_6017_) == 0)
{
lean_object* v_a_6018_; 
v_a_6018_ = lean_ctor_get(v___x_6017_, 0);
lean_inc(v_a_6018_);
lean_dec_ref_known(v___x_6017_, 1);
if (lean_obj_tag(v_a_6018_) == 7)
{
lean_object* v_binderType_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
lean_inc_ref(v_toConstantVal_5989_);
lean_dec_ref(v_ctorVal_5979_);
v_binderType_6019_ = lean_ctor_get(v_a_6018_, 1);
lean_inc_ref(v_binderType_6019_);
lean_dec_ref_known(v_a_6018_, 3);
v___x_6020_ = lean_box(0);
v___x_6021_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_6019_, v___x_6020_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
if (lean_obj_tag(v___x_6021_) == 0)
{
lean_object* v_a_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; 
v_a_6022_ = lean_ctor_get(v___x_6021_, 0);
lean_inc(v_a_6022_);
lean_dec_ref_known(v___x_6021_, 1);
v___x_6023_ = l_Lean_Expr_mvarId_x21(v_a_6022_);
v___x_6024_ = l_Lean_MVarId_intros(v___x_6023_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
if (lean_obj_tag(v___x_6024_) == 0)
{
lean_object* v_a_6025_; lean_object* v_snd_6026_; lean_object* v_name_6027_; lean_object* v___x_6028_; 
v_a_6025_ = lean_ctor_get(v___x_6024_, 0);
lean_inc(v_a_6025_);
lean_dec_ref_known(v___x_6024_, 1);
v_snd_6026_ = lean_ctor_get(v_a_6025_, 1);
lean_inc(v_snd_6026_);
lean_dec(v_a_6025_);
v_name_6027_ = lean_ctor_get(v_toConstantVal_5989_, 0);
lean_inc(v_name_6027_);
lean_dec_ref(v_toConstantVal_5989_);
v___x_6028_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_6026_, v_name_6027_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
if (lean_obj_tag(v___x_6028_) == 0)
{
lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v_a_6031_; lean_object* v___x_6033_; uint8_t v_isShared_6034_; uint8_t v_isSharedCheck_6058_; 
lean_dec_ref_known(v___x_6028_, 1);
v___x_6029_ = l_Lean_Expr_app___override(v___x_6014_, v_a_6022_);
v___x_6030_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_6029_, v___y_5985_);
v_a_6031_ = lean_ctor_get(v___x_6030_, 0);
v_isSharedCheck_6058_ = !lean_is_exclusive(v___x_6030_);
if (v_isSharedCheck_6058_ == 0)
{
v___x_6033_ = v___x_6030_;
v_isShared_6034_ = v_isSharedCheck_6058_;
goto v_resetjp_6032_;
}
else
{
lean_inc(v_a_6031_);
lean_dec(v___x_6030_);
v___x_6033_ = lean_box(0);
v_isShared_6034_ = v_isSharedCheck_6058_;
goto v_resetjp_6032_;
}
v_resetjp_6032_:
{
uint8_t v___x_6035_; uint8_t v___x_6036_; uint8_t v___x_6037_; lean_object* v___x_6038_; 
v___x_6035_ = 0;
v___x_6036_ = 1;
v___x_6037_ = 1;
v___x_6038_ = l_Lean_Meta_mkLambdaFVars(v_xs_5982_, v_a_6031_, v___x_6035_, v___x_6036_, v___x_6035_, v___x_6036_, v___x_6037_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
lean_dec_ref(v_xs_5982_);
if (lean_obj_tag(v___x_6038_) == 0)
{
lean_object* v_a_6039_; lean_object* v___x_6041_; uint8_t v_isShared_6042_; uint8_t v_isSharedCheck_6049_; 
v_a_6039_ = lean_ctor_get(v___x_6038_, 0);
v_isSharedCheck_6049_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6049_ == 0)
{
v___x_6041_ = v___x_6038_;
v_isShared_6042_ = v_isSharedCheck_6049_;
goto v_resetjp_6040_;
}
else
{
lean_inc(v_a_6039_);
lean_dec(v___x_6038_);
v___x_6041_ = lean_box(0);
v_isShared_6042_ = v_isSharedCheck_6049_;
goto v_resetjp_6040_;
}
v_resetjp_6040_:
{
lean_object* v___x_6044_; 
if (v_isShared_6034_ == 0)
{
lean_ctor_set_tag(v___x_6033_, 1);
lean_ctor_set(v___x_6033_, 0, v_a_6039_);
v___x_6044_ = v___x_6033_;
goto v_reusejp_6043_;
}
else
{
lean_object* v_reuseFailAlloc_6048_; 
v_reuseFailAlloc_6048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_a_6039_);
v___x_6044_ = v_reuseFailAlloc_6048_;
goto v_reusejp_6043_;
}
v_reusejp_6043_:
{
lean_object* v___x_6046_; 
if (v_isShared_6042_ == 0)
{
lean_ctor_set(v___x_6041_, 0, v___x_6044_);
v___x_6046_ = v___x_6041_;
goto v_reusejp_6045_;
}
else
{
lean_object* v_reuseFailAlloc_6047_; 
v_reuseFailAlloc_6047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6047_, 0, v___x_6044_);
v___x_6046_ = v_reuseFailAlloc_6047_;
goto v_reusejp_6045_;
}
v_reusejp_6045_:
{
return v___x_6046_;
}
}
}
}
else
{
lean_object* v_a_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6057_; 
lean_del_object(v___x_6033_);
v_a_6050_ = lean_ctor_get(v___x_6038_, 0);
v_isSharedCheck_6057_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6057_ == 0)
{
v___x_6052_ = v___x_6038_;
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_a_6050_);
lean_dec(v___x_6038_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6055_; 
if (v_isShared_6053_ == 0)
{
v___x_6055_ = v___x_6052_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
v___x_6055_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
return v___x_6055_;
}
}
}
}
}
else
{
lean_object* v_a_6059_; lean_object* v___x_6061_; uint8_t v_isShared_6062_; uint8_t v_isSharedCheck_6066_; 
lean_dec(v_a_6022_);
lean_dec_ref(v___x_6014_);
lean_dec_ref(v_xs_5982_);
v_a_6059_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6066_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6066_ == 0)
{
v___x_6061_ = v___x_6028_;
v_isShared_6062_ = v_isSharedCheck_6066_;
goto v_resetjp_6060_;
}
else
{
lean_inc(v_a_6059_);
lean_dec(v___x_6028_);
v___x_6061_ = lean_box(0);
v_isShared_6062_ = v_isSharedCheck_6066_;
goto v_resetjp_6060_;
}
v_resetjp_6060_:
{
lean_object* v___x_6064_; 
if (v_isShared_6062_ == 0)
{
v___x_6064_ = v___x_6061_;
goto v_reusejp_6063_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6059_);
v___x_6064_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6063_;
}
v_reusejp_6063_:
{
return v___x_6064_;
}
}
}
}
else
{
lean_object* v_a_6067_; lean_object* v___x_6069_; uint8_t v_isShared_6070_; uint8_t v_isSharedCheck_6074_; 
lean_dec(v_a_6022_);
lean_dec_ref(v___x_6014_);
lean_dec_ref(v_toConstantVal_5989_);
lean_dec_ref(v_xs_5982_);
v_a_6067_ = lean_ctor_get(v___x_6024_, 0);
v_isSharedCheck_6074_ = !lean_is_exclusive(v___x_6024_);
if (v_isSharedCheck_6074_ == 0)
{
v___x_6069_ = v___x_6024_;
v_isShared_6070_ = v_isSharedCheck_6074_;
goto v_resetjp_6068_;
}
else
{
lean_inc(v_a_6067_);
lean_dec(v___x_6024_);
v___x_6069_ = lean_box(0);
v_isShared_6070_ = v_isSharedCheck_6074_;
goto v_resetjp_6068_;
}
v_resetjp_6068_:
{
lean_object* v___x_6072_; 
if (v_isShared_6070_ == 0)
{
v___x_6072_ = v___x_6069_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6073_; 
v_reuseFailAlloc_6073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6073_, 0, v_a_6067_);
v___x_6072_ = v_reuseFailAlloc_6073_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
return v___x_6072_;
}
}
}
}
else
{
lean_object* v_a_6075_; lean_object* v___x_6077_; uint8_t v_isShared_6078_; uint8_t v_isSharedCheck_6082_; 
lean_dec_ref(v___x_6014_);
lean_dec_ref(v_toConstantVal_5989_);
lean_dec_ref(v_xs_5982_);
v_a_6075_ = lean_ctor_get(v___x_6021_, 0);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___x_6021_);
if (v_isSharedCheck_6082_ == 0)
{
v___x_6077_ = v___x_6021_;
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
else
{
lean_inc(v_a_6075_);
lean_dec(v___x_6021_);
v___x_6077_ = lean_box(0);
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
v_resetjp_6076_:
{
lean_object* v___x_6080_; 
if (v_isShared_6078_ == 0)
{
v___x_6080_ = v___x_6077_;
goto v_reusejp_6079_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v_a_6075_);
v___x_6080_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6079_;
}
v_reusejp_6079_:
{
return v___x_6080_;
}
}
}
}
else
{
lean_object* v___x_6083_; 
lean_dec(v_a_6018_);
lean_dec_ref(v___x_6014_);
lean_dec_ref(v_xs_5982_);
v___x_6083_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5979_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
return v___x_6083_;
}
}
else
{
lean_object* v_a_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6091_; 
lean_dec_ref(v___x_6014_);
lean_dec_ref(v_xs_5982_);
lean_dec_ref(v_ctorVal_5979_);
v_a_6084_ = lean_ctor_get(v___x_6017_, 0);
v_isSharedCheck_6091_ = !lean_is_exclusive(v___x_6017_);
if (v_isSharedCheck_6091_ == 0)
{
v___x_6086_ = v___x_6017_;
v_isShared_6087_ = v_isSharedCheck_6091_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_a_6084_);
lean_dec(v___x_6017_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6091_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
lean_object* v___x_6089_; 
if (v_isShared_6087_ == 0)
{
v___x_6089_ = v___x_6086_;
goto v_reusejp_6088_;
}
else
{
lean_object* v_reuseFailAlloc_6090_; 
v_reuseFailAlloc_6090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6090_, 0, v_a_6084_);
v___x_6089_ = v_reuseFailAlloc_6090_;
goto v_reusejp_6088_;
}
v_reusejp_6088_:
{
return v___x_6089_;
}
}
}
}
else
{
lean_object* v_a_6092_; lean_object* v___x_6094_; uint8_t v_isShared_6095_; uint8_t v_isSharedCheck_6099_; 
lean_dec_ref(v___x_6014_);
lean_dec_ref(v_xs_5982_);
lean_dec_ref(v_ctorVal_5979_);
v_a_6092_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6099_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6099_ == 0)
{
v___x_6094_ = v___x_6015_;
v_isShared_6095_ = v_isSharedCheck_6099_;
goto v_resetjp_6093_;
}
else
{
lean_inc(v_a_6092_);
lean_dec(v___x_6015_);
v___x_6094_ = lean_box(0);
v_isShared_6095_ = v_isSharedCheck_6099_;
goto v_resetjp_6093_;
}
v_resetjp_6093_:
{
lean_object* v___x_6097_; 
if (v_isShared_6095_ == 0)
{
v___x_6097_ = v___x_6094_;
goto v_reusejp_6096_;
}
else
{
lean_object* v_reuseFailAlloc_6098_; 
v_reuseFailAlloc_6098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6092_);
v___x_6097_ = v_reuseFailAlloc_6098_;
goto v_reusejp_6096_;
}
v_reusejp_6096_:
{
return v___x_6097_;
}
}
}
}
else
{
lean_object* v_a_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6107_; 
lean_dec_ref(v_eqs_6004_);
lean_dec_ref(v_noConfusion_5998_);
lean_dec_ref(v_xs_5982_);
lean_dec_ref(v_ctorVal_5979_);
v_a_6100_ = lean_ctor_get(v___x_6007_, 0);
v_isSharedCheck_6107_ = !lean_is_exclusive(v___x_6007_);
if (v_isSharedCheck_6107_ == 0)
{
v___x_6102_ = v___x_6007_;
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_a_6100_);
lean_dec(v___x_6007_);
v___x_6102_ = lean_box(0);
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
v_resetjp_6101_:
{
lean_object* v___x_6105_; 
if (v_isShared_6103_ == 0)
{
v___x_6105_ = v___x_6102_;
goto v_reusejp_6104_;
}
else
{
lean_object* v_reuseFailAlloc_6106_; 
v_reuseFailAlloc_6106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6106_, 0, v_a_6100_);
v___x_6105_ = v_reuseFailAlloc_6106_;
goto v_reusejp_6104_;
}
v_reusejp_6104_:
{
return v___x_6105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_6114_, lean_object* v_us_6115_, lean_object* v_numIndices_6116_, lean_object* v_xs_6117_, lean_object* v_type_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_){
_start:
{
lean_object* v_res_6124_; 
v_res_6124_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_6114_, v_us_6115_, v_numIndices_6116_, v_xs_6117_, v_type_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
lean_dec(v___y_6122_);
lean_dec_ref(v___y_6121_);
lean_dec(v___y_6120_);
lean_dec_ref(v___y_6119_);
lean_dec(v_numIndices_6116_);
return v_res_6124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_6125_, lean_object* v_typeInfo_6126_, lean_object* v_a_6127_, lean_object* v_a_6128_, lean_object* v_a_6129_, lean_object* v_a_6130_){
_start:
{
lean_object* v_thmType_6132_; lean_object* v_us_6133_; lean_object* v_numIndices_6134_; lean_object* v___f_6135_; uint8_t v___x_6136_; lean_object* v___x_6137_; 
v_thmType_6132_ = lean_ctor_get(v_typeInfo_6126_, 0);
lean_inc_ref(v_thmType_6132_);
v_us_6133_ = lean_ctor_get(v_typeInfo_6126_, 1);
lean_inc(v_us_6133_);
v_numIndices_6134_ = lean_ctor_get(v_typeInfo_6126_, 2);
lean_inc(v_numIndices_6134_);
lean_dec_ref(v_typeInfo_6126_);
v___f_6135_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6135_, 0, v_ctorVal_6125_);
lean_closure_set(v___f_6135_, 1, v_us_6133_);
lean_closure_set(v___f_6135_, 2, v_numIndices_6134_);
v___x_6136_ = 0;
v___x_6137_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_6132_, v___f_6135_, v___x_6136_, v___x_6136_, v_a_6127_, v_a_6128_, v_a_6129_, v_a_6130_);
return v___x_6137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_6138_, lean_object* v_typeInfo_6139_, lean_object* v_a_6140_, lean_object* v_a_6141_, lean_object* v_a_6142_, lean_object* v_a_6143_, lean_object* v_a_6144_){
_start:
{
lean_object* v_res_6145_; 
v_res_6145_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_6138_, v_typeInfo_6139_, v_a_6140_, v_a_6141_, v_a_6142_, v_a_6143_);
lean_dec(v_a_6143_);
lean_dec_ref(v_a_6142_);
lean_dec(v_a_6141_);
lean_dec_ref(v_a_6140_);
return v_res_6145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_6148_){
_start:
{
lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6149_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6150_ = l_Lean_Name_str___override(v_ctorName_6148_, v___x_6149_);
return v___x_6150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_6151_, lean_object* v_ctorVal_6152_, lean_object* v_a_6153_, lean_object* v_a_6154_, lean_object* v_a_6155_, lean_object* v_a_6156_){
_start:
{
lean_object* v___x_6158_; 
lean_inc_ref(v_ctorVal_6152_);
v___x_6158_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_6152_, v_a_6153_, v_a_6154_, v_a_6155_, v_a_6156_);
if (lean_obj_tag(v___x_6158_) == 0)
{
lean_object* v_a_6159_; lean_object* v___x_6161_; uint8_t v_isShared_6162_; uint8_t v_isSharedCheck_6220_; 
v_a_6159_ = lean_ctor_get(v___x_6158_, 0);
v_isSharedCheck_6220_ = !lean_is_exclusive(v___x_6158_);
if (v_isSharedCheck_6220_ == 0)
{
v___x_6161_ = v___x_6158_;
v_isShared_6162_ = v_isSharedCheck_6220_;
goto v_resetjp_6160_;
}
else
{
lean_inc(v_a_6159_);
lean_dec(v___x_6158_);
v___x_6161_ = lean_box(0);
v_isShared_6162_ = v_isSharedCheck_6220_;
goto v_resetjp_6160_;
}
v_resetjp_6160_:
{
if (lean_obj_tag(v_a_6159_) == 1)
{
lean_object* v_val_6163_; lean_object* v___x_6164_; 
lean_del_object(v___x_6161_);
v_val_6163_ = lean_ctor_get(v_a_6159_, 0);
lean_inc_n(v_val_6163_, 2);
lean_dec_ref_known(v_a_6159_, 1);
lean_inc_ref(v_ctorVal_6152_);
v___x_6164_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_6152_, v_val_6163_, v_a_6153_, v_a_6154_, v_a_6155_, v_a_6156_);
if (lean_obj_tag(v___x_6164_) == 0)
{
lean_object* v_a_6165_; lean_object* v___x_6167_; uint8_t v_isShared_6168_; uint8_t v_isSharedCheck_6207_; 
v_a_6165_ = lean_ctor_get(v___x_6164_, 0);
v_isSharedCheck_6207_ = !lean_is_exclusive(v___x_6164_);
if (v_isSharedCheck_6207_ == 0)
{
v___x_6167_ = v___x_6164_;
v_isShared_6168_ = v_isSharedCheck_6207_;
goto v_resetjp_6166_;
}
else
{
lean_inc(v_a_6165_);
lean_dec(v___x_6164_);
v___x_6167_ = lean_box(0);
v_isShared_6168_ = v_isSharedCheck_6207_;
goto v_resetjp_6166_;
}
v_resetjp_6166_:
{
if (lean_obj_tag(v_a_6165_) == 1)
{
lean_object* v_toConstantVal_6169_; lean_object* v_val_6170_; lean_object* v___x_6172_; uint8_t v_isShared_6173_; uint8_t v_isSharedCheck_6202_; 
v_toConstantVal_6169_ = lean_ctor_get(v_ctorVal_6152_, 0);
lean_inc_ref(v_toConstantVal_6169_);
lean_dec_ref(v_ctorVal_6152_);
v_val_6170_ = lean_ctor_get(v_a_6165_, 0);
v_isSharedCheck_6202_ = !lean_is_exclusive(v_a_6165_);
if (v_isSharedCheck_6202_ == 0)
{
v___x_6172_ = v_a_6165_;
v_isShared_6173_ = v_isSharedCheck_6202_;
goto v_resetjp_6171_;
}
else
{
lean_inc(v_val_6170_);
lean_dec(v_a_6165_);
v___x_6172_ = lean_box(0);
v_isShared_6173_ = v_isSharedCheck_6202_;
goto v_resetjp_6171_;
}
v_resetjp_6171_:
{
lean_object* v_levelParams_6174_; lean_object* v___x_6176_; uint8_t v_isShared_6177_; uint8_t v_isSharedCheck_6199_; 
v_levelParams_6174_ = lean_ctor_get(v_toConstantVal_6169_, 1);
v_isSharedCheck_6199_ = !lean_is_exclusive(v_toConstantVal_6169_);
if (v_isSharedCheck_6199_ == 0)
{
lean_object* v_unused_6200_; lean_object* v_unused_6201_; 
v_unused_6200_ = lean_ctor_get(v_toConstantVal_6169_, 2);
lean_dec(v_unused_6200_);
v_unused_6201_ = lean_ctor_get(v_toConstantVal_6169_, 0);
lean_dec(v_unused_6201_);
v___x_6176_ = v_toConstantVal_6169_;
v_isShared_6177_ = v_isSharedCheck_6199_;
goto v_resetjp_6175_;
}
else
{
lean_inc(v_levelParams_6174_);
lean_dec(v_toConstantVal_6169_);
v___x_6176_ = lean_box(0);
v_isShared_6177_ = v_isSharedCheck_6199_;
goto v_resetjp_6175_;
}
v_resetjp_6175_:
{
lean_object* v_thmType_6178_; lean_object* v___x_6180_; uint8_t v_isShared_6181_; uint8_t v_isSharedCheck_6196_; 
v_thmType_6178_ = lean_ctor_get(v_val_6163_, 0);
v_isSharedCheck_6196_ = !lean_is_exclusive(v_val_6163_);
if (v_isSharedCheck_6196_ == 0)
{
lean_object* v_unused_6197_; lean_object* v_unused_6198_; 
v_unused_6197_ = lean_ctor_get(v_val_6163_, 2);
lean_dec(v_unused_6197_);
v_unused_6198_ = lean_ctor_get(v_val_6163_, 1);
lean_dec(v_unused_6198_);
v___x_6180_ = v_val_6163_;
v_isShared_6181_ = v_isSharedCheck_6196_;
goto v_resetjp_6179_;
}
else
{
lean_inc(v_thmType_6178_);
lean_dec(v_val_6163_);
v___x_6180_ = lean_box(0);
v_isShared_6181_ = v_isSharedCheck_6196_;
goto v_resetjp_6179_;
}
v_resetjp_6179_:
{
lean_object* v___x_6183_; 
lean_inc(v_thmName_6151_);
if (v_isShared_6177_ == 0)
{
lean_ctor_set(v___x_6176_, 2, v_thmType_6178_);
lean_ctor_set(v___x_6176_, 0, v_thmName_6151_);
v___x_6183_ = v___x_6176_;
goto v_reusejp_6182_;
}
else
{
lean_object* v_reuseFailAlloc_6195_; 
v_reuseFailAlloc_6195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6195_, 0, v_thmName_6151_);
lean_ctor_set(v_reuseFailAlloc_6195_, 1, v_levelParams_6174_);
lean_ctor_set(v_reuseFailAlloc_6195_, 2, v_thmType_6178_);
v___x_6183_ = v_reuseFailAlloc_6195_;
goto v_reusejp_6182_;
}
v_reusejp_6182_:
{
lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6187_; 
v___x_6184_ = lean_box(0);
v___x_6185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6185_, 0, v_thmName_6151_);
lean_ctor_set(v___x_6185_, 1, v___x_6184_);
if (v_isShared_6181_ == 0)
{
lean_ctor_set(v___x_6180_, 2, v___x_6185_);
lean_ctor_set(v___x_6180_, 1, v_val_6170_);
lean_ctor_set(v___x_6180_, 0, v___x_6183_);
v___x_6187_ = v___x_6180_;
goto v_reusejp_6186_;
}
else
{
lean_object* v_reuseFailAlloc_6194_; 
v_reuseFailAlloc_6194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6194_, 0, v___x_6183_);
lean_ctor_set(v_reuseFailAlloc_6194_, 1, v_val_6170_);
lean_ctor_set(v_reuseFailAlloc_6194_, 2, v___x_6185_);
v___x_6187_ = v_reuseFailAlloc_6194_;
goto v_reusejp_6186_;
}
v_reusejp_6186_:
{
lean_object* v___x_6189_; 
if (v_isShared_6173_ == 0)
{
lean_ctor_set(v___x_6172_, 0, v___x_6187_);
v___x_6189_ = v___x_6172_;
goto v_reusejp_6188_;
}
else
{
lean_object* v_reuseFailAlloc_6193_; 
v_reuseFailAlloc_6193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6187_);
v___x_6189_ = v_reuseFailAlloc_6193_;
goto v_reusejp_6188_;
}
v_reusejp_6188_:
{
lean_object* v___x_6191_; 
if (v_isShared_6168_ == 0)
{
lean_ctor_set(v___x_6167_, 0, v___x_6189_);
v___x_6191_ = v___x_6167_;
goto v_reusejp_6190_;
}
else
{
lean_object* v_reuseFailAlloc_6192_; 
v_reuseFailAlloc_6192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6192_, 0, v___x_6189_);
v___x_6191_ = v_reuseFailAlloc_6192_;
goto v_reusejp_6190_;
}
v_reusejp_6190_:
{
return v___x_6191_;
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
lean_object* v___x_6203_; lean_object* v___x_6205_; 
lean_dec(v_a_6165_);
lean_dec(v_val_6163_);
lean_dec_ref(v_ctorVal_6152_);
lean_dec(v_thmName_6151_);
v___x_6203_ = lean_box(0);
if (v_isShared_6168_ == 0)
{
lean_ctor_set(v___x_6167_, 0, v___x_6203_);
v___x_6205_ = v___x_6167_;
goto v_reusejp_6204_;
}
else
{
lean_object* v_reuseFailAlloc_6206_; 
v_reuseFailAlloc_6206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6206_, 0, v___x_6203_);
v___x_6205_ = v_reuseFailAlloc_6206_;
goto v_reusejp_6204_;
}
v_reusejp_6204_:
{
return v___x_6205_;
}
}
}
}
else
{
lean_object* v_a_6208_; lean_object* v___x_6210_; uint8_t v_isShared_6211_; uint8_t v_isSharedCheck_6215_; 
lean_dec(v_val_6163_);
lean_dec_ref(v_ctorVal_6152_);
lean_dec(v_thmName_6151_);
v_a_6208_ = lean_ctor_get(v___x_6164_, 0);
v_isSharedCheck_6215_ = !lean_is_exclusive(v___x_6164_);
if (v_isSharedCheck_6215_ == 0)
{
v___x_6210_ = v___x_6164_;
v_isShared_6211_ = v_isSharedCheck_6215_;
goto v_resetjp_6209_;
}
else
{
lean_inc(v_a_6208_);
lean_dec(v___x_6164_);
v___x_6210_ = lean_box(0);
v_isShared_6211_ = v_isSharedCheck_6215_;
goto v_resetjp_6209_;
}
v_resetjp_6209_:
{
lean_object* v___x_6213_; 
if (v_isShared_6211_ == 0)
{
v___x_6213_ = v___x_6210_;
goto v_reusejp_6212_;
}
else
{
lean_object* v_reuseFailAlloc_6214_; 
v_reuseFailAlloc_6214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6214_, 0, v_a_6208_);
v___x_6213_ = v_reuseFailAlloc_6214_;
goto v_reusejp_6212_;
}
v_reusejp_6212_:
{
return v___x_6213_;
}
}
}
}
else
{
lean_object* v___x_6216_; lean_object* v___x_6218_; 
lean_dec(v_a_6159_);
lean_dec_ref(v_ctorVal_6152_);
lean_dec(v_thmName_6151_);
v___x_6216_ = lean_box(0);
if (v_isShared_6162_ == 0)
{
lean_ctor_set(v___x_6161_, 0, v___x_6216_);
v___x_6218_ = v___x_6161_;
goto v_reusejp_6217_;
}
else
{
lean_object* v_reuseFailAlloc_6219_; 
v_reuseFailAlloc_6219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6219_, 0, v___x_6216_);
v___x_6218_ = v_reuseFailAlloc_6219_;
goto v_reusejp_6217_;
}
v_reusejp_6217_:
{
return v___x_6218_;
}
}
}
}
else
{
lean_object* v_a_6221_; lean_object* v___x_6223_; uint8_t v_isShared_6224_; uint8_t v_isSharedCheck_6228_; 
lean_dec_ref(v_ctorVal_6152_);
lean_dec(v_thmName_6151_);
v_a_6221_ = lean_ctor_get(v___x_6158_, 0);
v_isSharedCheck_6228_ = !lean_is_exclusive(v___x_6158_);
if (v_isSharedCheck_6228_ == 0)
{
v___x_6223_ = v___x_6158_;
v_isShared_6224_ = v_isSharedCheck_6228_;
goto v_resetjp_6222_;
}
else
{
lean_inc(v_a_6221_);
lean_dec(v___x_6158_);
v___x_6223_ = lean_box(0);
v_isShared_6224_ = v_isSharedCheck_6228_;
goto v_resetjp_6222_;
}
v_resetjp_6222_:
{
lean_object* v___x_6226_; 
if (v_isShared_6224_ == 0)
{
v___x_6226_ = v___x_6223_;
goto v_reusejp_6225_;
}
else
{
lean_object* v_reuseFailAlloc_6227_; 
v_reuseFailAlloc_6227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6227_, 0, v_a_6221_);
v___x_6226_ = v_reuseFailAlloc_6227_;
goto v_reusejp_6225_;
}
v_reusejp_6225_:
{
return v___x_6226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6229_, lean_object* v_ctorVal_6230_, lean_object* v_a_6231_, lean_object* v_a_6232_, lean_object* v_a_6233_, lean_object* v_a_6234_, lean_object* v_a_6235_){
_start:
{
lean_object* v_res_6236_; 
v_res_6236_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6229_, v_ctorVal_6230_, v_a_6231_, v_a_6232_, v_a_6233_, v_a_6234_);
lean_dec(v_a_6234_);
lean_dec_ref(v_a_6233_);
lean_dec(v_a_6232_);
lean_dec_ref(v_a_6231_);
return v_res_6236_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6237_, lean_object* v_n_6238_){
_start:
{
if (lean_obj_tag(v_n_6238_) == 1)
{
lean_object* v_pre_6239_; lean_object* v_str_6240_; lean_object* v___x_6241_; uint8_t v___x_6242_; 
v_pre_6239_ = lean_ctor_get(v_n_6238_, 0);
lean_inc(v_pre_6239_);
v_str_6240_ = lean_ctor_get(v_n_6238_, 1);
lean_inc_ref(v_str_6240_);
lean_dec_ref_known(v_n_6238_, 2);
v___x_6241_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6242_ = lean_string_dec_eq(v_str_6240_, v___x_6241_);
lean_dec_ref(v_str_6240_);
if (v___x_6242_ == 0)
{
lean_dec(v_pre_6239_);
lean_dec_ref(v_env_6237_);
return v___x_6242_;
}
else
{
uint8_t v___x_6243_; lean_object* v___x_6244_; 
v___x_6243_ = 0;
v___x_6244_ = l_Lean_Environment_find_x3f(v_env_6237_, v_pre_6239_, v___x_6243_);
if (lean_obj_tag(v___x_6244_) == 1)
{
lean_object* v_val_6245_; 
v_val_6245_ = lean_ctor_get(v___x_6244_, 0);
lean_inc(v_val_6245_);
lean_dec_ref_known(v___x_6244_, 1);
if (lean_obj_tag(v_val_6245_) == 6)
{
lean_dec_ref_known(v_val_6245_, 1);
return v___x_6242_;
}
else
{
lean_dec(v_val_6245_);
return v___x_6243_;
}
}
else
{
lean_dec(v___x_6244_);
return v___x_6243_;
}
}
}
else
{
uint8_t v___x_6246_; 
lean_dec(v_n_6238_);
lean_dec_ref(v_env_6237_);
v___x_6246_ = 0;
return v___x_6246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6247_, lean_object* v_n_6248_){
_start:
{
uint8_t v_res_6249_; lean_object* v_r_6250_; 
v_res_6249_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6247_, v_n_6248_);
v_r_6250_ = lean_box(v_res_6249_);
return v_r_6250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6253_; lean_object* v___x_6254_; 
v___f_6253_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6254_ = l_Lean_registerReservedNamePredicate(v___f_6253_);
return v___x_6254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6255_){
_start:
{
lean_object* v_res_6256_; 
v_res_6256_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6256_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6257_, lean_object* v___y_6258_){
_start:
{
lean_object* v___x_6260_; lean_object* v_env_6261_; lean_object* v_toConstantVal_6262_; lean_object* v_value_6263_; lean_object* v_all_6264_; uint8_t v___y_6266_; lean_object* v_type_6274_; uint8_t v___x_6275_; 
v___x_6260_ = lean_st_ref_get(v___y_6258_);
v_env_6261_ = lean_ctor_get(v___x_6260_, 0);
lean_inc_ref_n(v_env_6261_, 2);
lean_dec(v___x_6260_);
v_toConstantVal_6262_ = lean_ctor_get(v_thm_6257_, 0);
v_value_6263_ = lean_ctor_get(v_thm_6257_, 1);
v_all_6264_ = lean_ctor_get(v_thm_6257_, 2);
v_type_6274_ = lean_ctor_get(v_toConstantVal_6262_, 2);
v___x_6275_ = l_Lean_Environment_hasUnsafe(v_env_6261_, v_type_6274_);
if (v___x_6275_ == 0)
{
uint8_t v___x_6276_; 
v___x_6276_ = l_Lean_Environment_hasUnsafe(v_env_6261_, v_value_6263_);
v___y_6266_ = v___x_6276_;
goto v___jp_6265_;
}
else
{
lean_dec_ref(v_env_6261_);
v___y_6266_ = v___x_6275_;
goto v___jp_6265_;
}
v___jp_6265_:
{
if (v___y_6266_ == 0)
{
lean_object* v___x_6267_; lean_object* v___x_6268_; 
v___x_6267_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6267_, 0, v_thm_6257_);
v___x_6268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6268_, 0, v___x_6267_);
return v___x_6268_;
}
else
{
lean_object* v___x_6269_; uint8_t v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; 
lean_inc(v_all_6264_);
lean_inc_ref(v_value_6263_);
lean_inc_ref(v_toConstantVal_6262_);
lean_dec_ref(v_thm_6257_);
v___x_6269_ = lean_box(0);
v___x_6270_ = 0;
v___x_6271_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6271_, 0, v_toConstantVal_6262_);
lean_ctor_set(v___x_6271_, 1, v_value_6263_);
lean_ctor_set(v___x_6271_, 2, v___x_6269_);
lean_ctor_set(v___x_6271_, 3, v_all_6264_);
lean_ctor_set_uint8(v___x_6271_, sizeof(void*)*4, v___x_6270_);
v___x_6272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6272_, 0, v___x_6271_);
v___x_6273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6273_, 0, v___x_6272_);
return v___x_6273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_){
_start:
{
lean_object* v_res_6280_; 
v_res_6280_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6277_, v___y_6278_);
lean_dec(v___y_6278_);
return v_res_6280_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
lean_object* v___x_6287_; 
v___x_6287_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6281_, v___y_6285_);
return v___x_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_){
_start:
{
lean_object* v_res_6294_; 
v_res_6294_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6288_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_);
lean_dec(v___y_6292_);
lean_dec_ref(v___y_6291_);
lean_dec(v___y_6290_);
lean_dec_ref(v___y_6289_);
return v_res_6294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6295_, uint8_t v___x_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_){
_start:
{
lean_object* v___x_6302_; lean_object* v_a_6303_; lean_object* v___x_6304_; 
v___x_6302_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6295_, v___y_6300_);
v_a_6303_ = lean_ctor_get(v___x_6302_, 0);
lean_inc(v_a_6303_);
lean_dec_ref(v___x_6302_);
v___x_6304_ = l_Lean_addDecl(v_a_6303_, v___x_6296_, v___y_6299_, v___y_6300_);
return v___x_6304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6305_, lean_object* v___x_6306_, lean_object* v___y_6307_, lean_object* v___y_6308_, lean_object* v___y_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_){
_start:
{
uint8_t v___x_2144__boxed_6312_; lean_object* v_res_6313_; 
v___x_2144__boxed_6312_ = lean_unbox(v___x_6306_);
v_res_6313_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6305_, v___x_2144__boxed_6312_, v___y_6307_, v___y_6308_, v___y_6309_, v___y_6310_);
lean_dec(v___y_6310_);
lean_dec_ref(v___y_6309_);
lean_dec(v___y_6308_);
lean_dec_ref(v___y_6307_);
return v_res_6313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; 
v___x_6316_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6317_ = lean_unsigned_to_nat(0u);
v___x_6318_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6318_, 0, v___x_6317_);
lean_ctor_set(v___x_6318_, 1, v___x_6317_);
lean_ctor_set(v___x_6318_, 2, v___x_6317_);
lean_ctor_set(v___x_6318_, 3, v___x_6317_);
lean_ctor_set(v___x_6318_, 4, v___x_6316_);
lean_ctor_set(v___x_6318_, 5, v___x_6316_);
lean_ctor_set(v___x_6318_, 6, v___x_6316_);
lean_ctor_set(v___x_6318_, 7, v___x_6316_);
lean_ctor_set(v___x_6318_, 8, v___x_6316_);
lean_ctor_set(v___x_6318_, 9, v___x_6316_);
lean_ctor_set(v___x_6318_, 10, v___x_6316_);
return v___x_6318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6319_; lean_object* v___x_6320_; 
v___x_6319_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6320_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6320_, 0, v___x_6319_);
lean_ctor_set(v___x_6320_, 1, v___x_6319_);
lean_ctor_set(v___x_6320_, 2, v___x_6319_);
lean_ctor_set(v___x_6320_, 3, v___x_6319_);
lean_ctor_set(v___x_6320_, 4, v___x_6319_);
lean_ctor_set(v___x_6320_, 5, v___x_6319_);
return v___x_6320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6321_; lean_object* v___x_6322_; 
v___x_6321_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6322_, 0, v___x_6321_);
lean_ctor_set(v___x_6322_, 1, v___x_6321_);
lean_ctor_set(v___x_6322_, 2, v___x_6321_);
lean_ctor_set(v___x_6322_, 3, v___x_6321_);
lean_ctor_set(v___x_6322_, 4, v___x_6321_);
return v___x_6322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6323_, lean_object* v_name_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_){
_start:
{
if (lean_obj_tag(v_name_6324_) == 1)
{
lean_object* v_pre_6336_; lean_object* v_str_6337_; lean_object* v___x_6338_; uint8_t v___x_6339_; 
v_pre_6336_ = lean_ctor_get(v_name_6324_, 0);
lean_inc(v_pre_6336_);
v_str_6337_ = lean_ctor_get(v_name_6324_, 1);
v___x_6338_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6339_ = lean_string_dec_eq(v_str_6337_, v___x_6338_);
if (v___x_6339_ == 0)
{
lean_dec_ref_known(v_name_6324_, 2);
lean_dec(v_pre_6336_);
lean_dec(v___x_6323_);
goto v___jp_6332_;
}
else
{
lean_object* v___x_6340_; lean_object* v_env_6341_; uint8_t v___x_6342_; lean_object* v___x_6343_; 
v___x_6340_ = lean_st_ref_get(v___y_6326_);
v_env_6341_ = lean_ctor_get(v___x_6340_, 0);
lean_inc_ref(v_env_6341_);
lean_dec(v___x_6340_);
v___x_6342_ = 0;
lean_inc(v_pre_6336_);
v___x_6343_ = l_Lean_Environment_find_x3f(v_env_6341_, v_pre_6336_, v___x_6342_);
if (lean_obj_tag(v___x_6343_) == 1)
{
lean_object* v_val_6344_; 
v_val_6344_ = lean_ctor_get(v___x_6343_, 0);
lean_inc(v_val_6344_);
lean_dec_ref_known(v___x_6343_, 1);
if (lean_obj_tag(v_val_6344_) == 6)
{
lean_object* v_val_6345_; lean_object* v___x_6347_; uint8_t v_isShared_6348_; uint8_t v_isSharedCheck_6395_; 
v_val_6345_ = lean_ctor_get(v_val_6344_, 0);
v_isSharedCheck_6395_ = !lean_is_exclusive(v_val_6344_);
if (v_isSharedCheck_6395_ == 0)
{
v___x_6347_ = v_val_6344_;
v_isShared_6348_ = v_isSharedCheck_6395_;
goto v_resetjp_6346_;
}
else
{
lean_inc(v_val_6345_);
lean_dec(v_val_6344_);
v___x_6347_ = lean_box(0);
v_isShared_6348_ = v_isSharedCheck_6395_;
goto v_resetjp_6346_;
}
v_resetjp_6346_:
{
uint8_t v___x_6349_; uint8_t v___x_6350_; uint8_t v___x_6351_; lean_object* v___x_6352_; uint64_t v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; uint8_t v_a_6367_; lean_object* v___x_6373_; 
v___x_6349_ = 1;
v___x_6350_ = 0;
v___x_6351_ = 2;
v___x_6352_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_6352_, 0, v___x_6342_);
lean_ctor_set_uint8(v___x_6352_, 1, v___x_6342_);
lean_ctor_set_uint8(v___x_6352_, 2, v___x_6342_);
lean_ctor_set_uint8(v___x_6352_, 3, v___x_6342_);
lean_ctor_set_uint8(v___x_6352_, 4, v___x_6342_);
lean_ctor_set_uint8(v___x_6352_, 5, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 6, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 7, v___x_6342_);
lean_ctor_set_uint8(v___x_6352_, 8, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 9, v___x_6349_);
lean_ctor_set_uint8(v___x_6352_, 10, v___x_6350_);
lean_ctor_set_uint8(v___x_6352_, 11, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 12, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 13, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 14, v___x_6351_);
lean_ctor_set_uint8(v___x_6352_, 15, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 16, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 17, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 18, v___x_6339_);
lean_ctor_set_uint8(v___x_6352_, 19, v___x_6342_);
v___x_6353_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6352_);
v___x_6354_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6354_, 0, v___x_6352_);
lean_ctor_set_uint64(v___x_6354_, sizeof(void*)*1, v___x_6353_);
v___x_6355_ = lean_unsigned_to_nat(0u);
v___x_6356_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6357_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6358_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6359_ = lean_box(0);
lean_inc(v___x_6323_);
v___x_6360_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6360_, 0, v___x_6354_);
lean_ctor_set(v___x_6360_, 1, v___x_6323_);
lean_ctor_set(v___x_6360_, 2, v___x_6357_);
lean_ctor_set(v___x_6360_, 3, v___x_6358_);
lean_ctor_set(v___x_6360_, 4, v___x_6359_);
lean_ctor_set(v___x_6360_, 5, v___x_6355_);
lean_ctor_set(v___x_6360_, 6, v___x_6359_);
lean_ctor_set_uint8(v___x_6360_, sizeof(void*)*7, v___x_6342_);
lean_ctor_set_uint8(v___x_6360_, sizeof(void*)*7 + 1, v___x_6342_);
lean_ctor_set_uint8(v___x_6360_, sizeof(void*)*7 + 2, v___x_6342_);
lean_ctor_set_uint8(v___x_6360_, sizeof(void*)*7 + 3, v___x_6339_);
v___x_6361_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6362_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6363_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6364_, 0, v___x_6361_);
lean_ctor_set(v___x_6364_, 1, v___x_6362_);
lean_ctor_set(v___x_6364_, 2, v___x_6323_);
lean_ctor_set(v___x_6364_, 3, v___x_6356_);
lean_ctor_set(v___x_6364_, 4, v___x_6363_);
v___x_6365_ = lean_st_mk_ref(v___x_6364_);
lean_inc_ref(v_name_6324_);
v___x_6373_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6324_, v_val_6345_, v___x_6360_, v___x_6365_, v___y_6325_, v___y_6326_);
if (lean_obj_tag(v___x_6373_) == 0)
{
lean_object* v_a_6374_; 
v_a_6374_ = lean_ctor_get(v___x_6373_, 0);
lean_inc(v_a_6374_);
lean_dec_ref_known(v___x_6373_, 1);
if (lean_obj_tag(v_a_6374_) == 1)
{
lean_object* v_val_6375_; lean_object* v___x_6376_; lean_object* v___f_6377_; lean_object* v___x_6378_; 
v_val_6375_ = lean_ctor_get(v_a_6374_, 0);
lean_inc(v_val_6375_);
lean_dec_ref_known(v_a_6374_, 1);
v___x_6376_ = lean_box(v___x_6342_);
v___f_6377_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6377_, 0, v_val_6375_);
lean_closure_set(v___f_6377_, 1, v___x_6376_);
v___x_6378_ = l_Lean_Meta_realizeConst(v_pre_6336_, v_name_6324_, v___f_6377_, v___x_6360_, v___x_6365_, v___y_6325_, v___y_6326_);
lean_dec_ref_known(v___x_6360_, 7);
if (lean_obj_tag(v___x_6378_) == 0)
{
lean_dec_ref_known(v___x_6378_, 1);
v_a_6367_ = v___x_6339_;
goto v___jp_6366_;
}
else
{
lean_object* v_a_6379_; lean_object* v___x_6381_; uint8_t v_isShared_6382_; uint8_t v_isSharedCheck_6386_; 
lean_dec(v___x_6365_);
lean_del_object(v___x_6347_);
v_a_6379_ = lean_ctor_get(v___x_6378_, 0);
v_isSharedCheck_6386_ = !lean_is_exclusive(v___x_6378_);
if (v_isSharedCheck_6386_ == 0)
{
v___x_6381_ = v___x_6378_;
v_isShared_6382_ = v_isSharedCheck_6386_;
goto v_resetjp_6380_;
}
else
{
lean_inc(v_a_6379_);
lean_dec(v___x_6378_);
v___x_6381_ = lean_box(0);
v_isShared_6382_ = v_isSharedCheck_6386_;
goto v_resetjp_6380_;
}
v_resetjp_6380_:
{
lean_object* v___x_6384_; 
if (v_isShared_6382_ == 0)
{
v___x_6384_ = v___x_6381_;
goto v_reusejp_6383_;
}
else
{
lean_object* v_reuseFailAlloc_6385_; 
v_reuseFailAlloc_6385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6385_, 0, v_a_6379_);
v___x_6384_ = v_reuseFailAlloc_6385_;
goto v_reusejp_6383_;
}
v_reusejp_6383_:
{
return v___x_6384_;
}
}
}
}
else
{
lean_dec(v_a_6374_);
lean_dec_ref_known(v___x_6360_, 7);
lean_dec(v_pre_6336_);
lean_dec_ref_known(v_name_6324_, 2);
v_a_6367_ = v___x_6342_;
goto v___jp_6366_;
}
}
else
{
lean_object* v_a_6387_; lean_object* v___x_6389_; uint8_t v_isShared_6390_; uint8_t v_isSharedCheck_6394_; 
lean_dec(v___x_6365_);
lean_dec_ref_known(v___x_6360_, 7);
lean_del_object(v___x_6347_);
lean_dec_ref_known(v_name_6324_, 2);
lean_dec(v_pre_6336_);
v_a_6387_ = lean_ctor_get(v___x_6373_, 0);
v_isSharedCheck_6394_ = !lean_is_exclusive(v___x_6373_);
if (v_isSharedCheck_6394_ == 0)
{
v___x_6389_ = v___x_6373_;
v_isShared_6390_ = v_isSharedCheck_6394_;
goto v_resetjp_6388_;
}
else
{
lean_inc(v_a_6387_);
lean_dec(v___x_6373_);
v___x_6389_ = lean_box(0);
v_isShared_6390_ = v_isSharedCheck_6394_;
goto v_resetjp_6388_;
}
v_resetjp_6388_:
{
lean_object* v___x_6392_; 
if (v_isShared_6390_ == 0)
{
v___x_6392_ = v___x_6389_;
goto v_reusejp_6391_;
}
else
{
lean_object* v_reuseFailAlloc_6393_; 
v_reuseFailAlloc_6393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6393_, 0, v_a_6387_);
v___x_6392_ = v_reuseFailAlloc_6393_;
goto v_reusejp_6391_;
}
v_reusejp_6391_:
{
return v___x_6392_;
}
}
}
v___jp_6366_:
{
lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6371_; 
v___x_6368_ = lean_st_ref_get(v___x_6365_);
lean_dec(v___x_6365_);
lean_dec(v___x_6368_);
v___x_6369_ = lean_box(v_a_6367_);
if (v_isShared_6348_ == 0)
{
lean_ctor_set_tag(v___x_6347_, 0);
lean_ctor_set(v___x_6347_, 0, v___x_6369_);
v___x_6371_ = v___x_6347_;
goto v_reusejp_6370_;
}
else
{
lean_object* v_reuseFailAlloc_6372_; 
v_reuseFailAlloc_6372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6372_, 0, v___x_6369_);
v___x_6371_ = v_reuseFailAlloc_6372_;
goto v_reusejp_6370_;
}
v_reusejp_6370_:
{
return v___x_6371_;
}
}
}
}
else
{
lean_dec(v_val_6344_);
lean_dec_ref_known(v_name_6324_, 2);
lean_dec(v_pre_6336_);
lean_dec(v___x_6323_);
goto v___jp_6328_;
}
}
else
{
lean_dec(v___x_6343_);
lean_dec_ref_known(v_name_6324_, 2);
lean_dec(v_pre_6336_);
lean_dec(v___x_6323_);
goto v___jp_6328_;
}
}
}
else
{
lean_dec(v_name_6324_);
lean_dec(v___x_6323_);
goto v___jp_6332_;
}
v___jp_6328_:
{
uint8_t v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = 0;
v___x_6330_ = lean_box(v___x_6329_);
v___x_6331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6331_, 0, v___x_6330_);
return v___x_6331_;
}
v___jp_6332_:
{
uint8_t v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6333_ = 0;
v___x_6334_ = lean_box(v___x_6333_);
v___x_6335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6335_, 0, v___x_6334_);
return v___x_6335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6396_, lean_object* v_name_6397_, lean_object* v___y_6398_, lean_object* v___y_6399_, lean_object* v___y_6400_){
_start:
{
lean_object* v_res_6401_; 
v_res_6401_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6396_, v_name_6397_, v___y_6398_, v___y_6399_);
lean_dec(v___y_6399_);
lean_dec_ref(v___y_6398_);
return v_res_6401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6405_; lean_object* v___x_6406_; 
v___f_6405_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6406_ = l_Lean_registerReservedNameAction(v___f_6405_);
return v___x_6406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6407_){
_start:
{
lean_object* v_res_6408_; 
v_res_6408_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6408_;
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
