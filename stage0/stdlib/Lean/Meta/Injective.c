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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
size_t lean_usize_add(size_t, size_t);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
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
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "injEq_helper"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(167, 111, 180, 146, 132, 58, 155, 57)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "unexpected number of goals after applying `Lean.and_imp`"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 101, 109, 194, 24, 99, 201, 78)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(74, 76, 255, 124, 31, 108, 47, 16)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 106, 16, 37, 3, 60, 11, 157)}};
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 151, 10, 103, 183, 199, 62, 165)}};
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
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_nbuckets_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_123_ = lean_array_get_size(v_data_122_);
v___x_124_ = lean_unsigned_to_nat(2u);
v_nbuckets_125_ = lean_nat_mul(v___x_123_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_box(0);
v___x_128_ = lean_mk_array(v_nbuckets_125_, v___x_127_);
v___x_129_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_126_, v_data_122_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_130_, lean_object* v_b_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_dec(v_b_131_);
lean_dec_ref(v_a_130_);
return v_x_132_;
}
else
{
lean_object* v_key_133_; lean_object* v_value_134_; lean_object* v_tail_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_147_; 
v_key_133_ = lean_ctor_get(v_x_132_, 0);
v_value_134_ = lean_ctor_get(v_x_132_, 1);
v_tail_135_ = lean_ctor_get(v_x_132_, 2);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_132_);
if (v_isSharedCheck_147_ == 0)
{
v___x_137_ = v_x_132_;
v_isShared_138_ = v_isSharedCheck_147_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_tail_135_);
lean_inc(v_value_134_);
lean_inc(v_key_133_);
lean_dec(v_x_132_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_147_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
uint8_t v___x_139_; 
v___x_139_ = l_Lean_ExprStructEq_beq(v_key_133_, v_a_130_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_130_, v_b_131_, v_tail_135_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 2, v___x_140_);
v___x_142_ = v___x_137_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_key_133_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_value_134_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
else
{
lean_object* v___x_145_; 
lean_dec(v_value_134_);
lean_dec(v_key_133_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v_b_131_);
lean_ctor_set(v___x_137_, 0, v_a_130_);
v___x_145_ = v___x_137_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_130_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_b_131_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_tail_135_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
else
{
lean_object* v_key_151_; lean_object* v_tail_152_; uint8_t v___x_153_; 
v_key_151_ = lean_ctor_get(v_x_149_, 0);
v_tail_152_ = lean_ctor_get(v_x_149_, 2);
v___x_153_ = l_Lean_ExprStructEq_beq(v_key_151_, v_a_148_);
if (v___x_153_ == 0)
{
v_x_149_ = v_tail_152_;
goto _start;
}
else
{
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_155_, lean_object* v_x_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_155_, v_x_156_);
lean_dec(v_x_156_);
lean_dec_ref(v_a_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object* v_m_159_, lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
lean_object* v_size_162_; lean_object* v_buckets_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_206_; 
v_size_162_ = lean_ctor_get(v_m_159_, 0);
v_buckets_163_ = lean_ctor_get(v_m_159_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_m_159_);
if (v_isSharedCheck_206_ == 0)
{
v___x_165_ = v_m_159_;
v_isShared_166_ = v_isSharedCheck_206_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_buckets_163_);
lean_inc(v_size_162_);
lean_dec(v_m_159_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_206_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v_fold_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; lean_object* v_bkt_180_; uint8_t v___x_181_; 
v___x_167_ = lean_array_get_size(v_buckets_163_);
v___x_168_ = l_Lean_ExprStructEq_hash(v_a_160_);
v___x_169_ = 32ULL;
v___x_170_ = lean_uint64_shift_right(v___x_168_, v___x_169_);
v_fold_171_ = lean_uint64_xor(v___x_168_, v___x_170_);
v___x_172_ = 16ULL;
v___x_173_ = lean_uint64_shift_right(v_fold_171_, v___x_172_);
v___x_174_ = lean_uint64_xor(v_fold_171_, v___x_173_);
v___x_175_ = lean_uint64_to_usize(v___x_174_);
v___x_176_ = lean_usize_of_nat(v___x_167_);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_sub(v___x_176_, v___x_177_);
v___x_179_ = lean_usize_land(v___x_175_, v___x_178_);
v_bkt_180_ = lean_array_uget_borrowed(v_buckets_163_, v___x_179_);
v___x_181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_160_, v_bkt_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v_size_x27_183_; lean_object* v___x_184_; lean_object* v_buckets_x27_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v_size_x27_183_ = lean_nat_add(v_size_162_, v___x_182_);
lean_dec(v_size_162_);
lean_inc(v_bkt_180_);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v_a_160_);
lean_ctor_set(v___x_184_, 1, v_b_161_);
lean_ctor_set(v___x_184_, 2, v_bkt_180_);
v_buckets_x27_185_ = lean_array_uset(v_buckets_163_, v___x_179_, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(4u);
v___x_187_ = lean_nat_mul(v_size_x27_183_, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(3u);
v___x_189_ = lean_nat_div(v___x_187_, v___x_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_array_get_size(v_buckets_x27_185_);
v___x_191_ = lean_nat_dec_le(v___x_189_, v___x_190_);
lean_dec(v___x_189_);
if (v___x_191_ == 0)
{
lean_object* v_val_192_; lean_object* v___x_194_; 
v_val_192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_185_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v_val_192_);
lean_ctor_set(v___x_165_, 0, v_size_x27_183_);
v___x_194_ = v___x_165_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_size_x27_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_val_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
else
{
lean_object* v___x_197_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v_buckets_x27_185_);
lean_ctor_set(v___x_165_, 0, v_size_x27_183_);
v___x_197_ = v___x_165_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_size_x27_183_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_buckets_x27_185_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_object* v___x_199_; lean_object* v_buckets_x27_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
lean_inc(v_bkt_180_);
v___x_199_ = lean_box(0);
v_buckets_x27_200_ = lean_array_uset(v_buckets_163_, v___x_179_, v___x_199_);
v___x_201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_160_, v_b_161_, v_bkt_180_);
v___x_202_ = lean_array_uset(v_buckets_x27_200_, v___x_179_, v___x_201_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_202_);
v___x_204_ = v___x_165_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_size_162_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(lean_object* v_a_207_, lean_object* v_e_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_211_ = lean_st_ref_take(v_a_207_);
v___x_212_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v___x_211_, v_e_208_, v_a_209_);
v___x_213_ = lean_st_ref_set(v_a_207_, v___x_212_);
v___x_214_ = lean_box(0);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed(lean_object* v_a_215_, lean_object* v_e_216_, lean_object* v_a_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(v_a_215_, v_e_216_, v_a_217_);
lean_dec(v_a_215_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_box(0);
v___x_221_ = l_Lean_interruptExceptionId;
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_227_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = l_Lean_maxRecDepthErrorMessage;
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_236_ = l_Lean_MessageData_ofFormat(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_238_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_239_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_240_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_ref_240_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(lean_object* v_x_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___y_254_; uint8_t v___y_264_; uint8_t v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v_fileName_284_; lean_object* v_fileMap_285_; lean_object* v_options_286_; lean_object* v_currRecDepth_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ref_289_; lean_object* v_currNamespace_290_; lean_object* v_openDecls_291_; lean_object* v_initHeartbeats_292_; lean_object* v_maxHeartbeats_293_; lean_object* v_quotContext_294_; lean_object* v_currMacroScope_295_; uint8_t v_diag_296_; lean_object* v_cancelTk_x3f_297_; uint8_t v_suppressElabErrors_298_; lean_object* v_inheritedTraceOptions_299_; 
v_fileName_284_ = lean_ctor_get(v___y_250_, 0);
v_fileMap_285_ = lean_ctor_get(v___y_250_, 1);
v_options_286_ = lean_ctor_get(v___y_250_, 2);
v_currRecDepth_287_ = lean_ctor_get(v___y_250_, 3);
v_maxRecDepth_288_ = lean_ctor_get(v___y_250_, 4);
v_ref_289_ = lean_ctor_get(v___y_250_, 5);
v_currNamespace_290_ = lean_ctor_get(v___y_250_, 6);
v_openDecls_291_ = lean_ctor_get(v___y_250_, 7);
v_initHeartbeats_292_ = lean_ctor_get(v___y_250_, 8);
v_maxHeartbeats_293_ = lean_ctor_get(v___y_250_, 9);
v_quotContext_294_ = lean_ctor_get(v___y_250_, 10);
v_currMacroScope_295_ = lean_ctor_get(v___y_250_, 11);
v_diag_296_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*14);
v_cancelTk_x3f_297_ = lean_ctor_get(v___y_250_, 12);
v_suppressElabErrors_298_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_299_ = lean_ctor_get(v___y_250_, 13);
if (lean_obj_tag(v_cancelTk_x3f_297_) == 1)
{
lean_object* v_val_305_; uint8_t v___x_306_; 
v_val_305_ = lean_ctor_get(v_cancelTk_x3f_297_, 0);
v___x_306_ = l_IO_CancelToken_isSet(v_val_305_);
if (v___x_306_ == 0)
{
goto v___jp_300_;
}
else
{
lean_object* v___x_307_; lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_x_248_);
v___x_307_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
goto v___jp_300_;
}
v___jp_253_:
{
if (lean_obj_tag(v___y_254_) == 0)
{
return v___y_254_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___y_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___y_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___y_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___y_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
v___jp_263_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v___y_273_, v___x_280_);
lean_inc_ref(v___y_276_);
lean_inc(v___y_269_);
lean_inc(v___y_271_);
lean_inc(v___y_267_);
lean_inc(v___y_279_);
lean_inc(v___y_275_);
lean_inc(v___y_270_);
lean_inc(v___y_268_);
lean_inc(v___y_277_);
lean_inc_ref(v___y_266_);
lean_inc_ref(v___y_272_);
lean_inc_ref(v___y_274_);
v___x_282_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_282_, 0, v___y_274_);
lean_ctor_set(v___x_282_, 1, v___y_272_);
lean_ctor_set(v___x_282_, 2, v___y_266_);
lean_ctor_set(v___x_282_, 3, v___x_281_);
lean_ctor_set(v___x_282_, 4, v___y_277_);
lean_ctor_set(v___x_282_, 5, v___y_278_);
lean_ctor_set(v___x_282_, 6, v___y_268_);
lean_ctor_set(v___x_282_, 7, v___y_270_);
lean_ctor_set(v___x_282_, 8, v___y_275_);
lean_ctor_set(v___x_282_, 9, v___y_279_);
lean_ctor_set(v___x_282_, 10, v___y_267_);
lean_ctor_set(v___x_282_, 11, v___y_271_);
lean_ctor_set(v___x_282_, 12, v___y_269_);
lean_ctor_set(v___x_282_, 13, v___y_276_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14, v___y_265_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14 + 1, v___y_264_);
lean_inc(v___y_251_);
lean_inc(v___y_249_);
v___x_283_ = lean_apply_4(v_x_248_, v___y_249_, v___x_282_, v___y_251_, lean_box(0));
v___y_254_ = v___x_283_;
goto v___jp_253_;
}
v___jp_300_:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_nat_dec_eq(v_maxRecDepth_288_, v___x_301_);
if (v___x_302_ == 0)
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_eq(v_currRecDepth_287_, v_maxRecDepth_288_);
if (v___x_303_ == 0)
{
lean_inc(v_ref_289_);
v___y_264_ = v_suppressElabErrors_298_;
v___y_265_ = v_diag_296_;
v___y_266_ = v_options_286_;
v___y_267_ = v_quotContext_294_;
v___y_268_ = v_currNamespace_290_;
v___y_269_ = v_cancelTk_x3f_297_;
v___y_270_ = v_openDecls_291_;
v___y_271_ = v_currMacroScope_295_;
v___y_272_ = v_fileMap_285_;
v___y_273_ = v_currRecDepth_287_;
v___y_274_ = v_fileName_284_;
v___y_275_ = v_initHeartbeats_292_;
v___y_276_ = v_inheritedTraceOptions_299_;
v___y_277_ = v_maxRecDepth_288_;
v___y_278_ = v_ref_289_;
v___y_279_ = v_maxHeartbeats_293_;
goto v___jp_263_;
}
else
{
lean_object* v___x_304_; 
lean_dec_ref(v_x_248_);
lean_inc(v_ref_289_);
v___x_304_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_289_);
v___y_254_ = v___x_304_;
goto v___jp_253_;
}
}
else
{
lean_inc(v_ref_289_);
v___y_264_ = v_suppressElabErrors_298_;
v___y_265_ = v_diag_296_;
v___y_266_ = v_options_286_;
v___y_267_ = v_quotContext_294_;
v___y_268_ = v_currNamespace_290_;
v___y_269_ = v_cancelTk_x3f_297_;
v___y_270_ = v_openDecls_291_;
v___y_271_ = v_currMacroScope_295_;
v___y_272_ = v_fileMap_285_;
v___y_273_ = v_currRecDepth_287_;
v___y_274_ = v_fileName_284_;
v___y_275_ = v_initHeartbeats_292_;
v___y_276_ = v_inheritedTraceOptions_299_;
v___y_277_ = v_maxRecDepth_288_;
v___y_278_ = v_ref_289_;
v___y_279_ = v_maxHeartbeats_293_;
goto v___jp_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_322_, lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_apply_1(v_x_323_, lean_box(0));
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_329_, lean_object* v_x_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_329_, v_x_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_335_, lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_box(0);
return v___x_337_;
}
else
{
lean_object* v_key_338_; lean_object* v_value_339_; lean_object* v_tail_340_; uint8_t v___x_341_; 
v_key_338_ = lean_ctor_get(v_x_336_, 0);
v_value_339_ = lean_ctor_get(v_x_336_, 1);
v_tail_340_ = lean_ctor_get(v_x_336_, 2);
v___x_341_ = l_Lean_ExprStructEq_beq(v_key_338_, v_a_335_);
if (v___x_341_ == 0)
{
v_x_336_ = v_tail_340_;
goto _start;
}
else
{
lean_object* v___x_343_; 
lean_inc(v_value_339_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v_value_339_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_344_, v_x_345_);
lean_dec(v_x_345_);
lean_dec_ref(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_buckets_349_; lean_object* v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v_fold_354_; uint64_t v___x_355_; uint64_t v___x_356_; uint64_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_buckets_349_ = lean_ctor_get(v_m_347_, 1);
v___x_350_ = lean_array_get_size(v_buckets_349_);
v___x_351_ = l_Lean_ExprStructEq_hash(v_a_348_);
v___x_352_ = 32ULL;
v___x_353_ = lean_uint64_shift_right(v___x_351_, v___x_352_);
v_fold_354_ = lean_uint64_xor(v___x_351_, v___x_353_);
v___x_355_ = 16ULL;
v___x_356_ = lean_uint64_shift_right(v_fold_354_, v___x_355_);
v___x_357_ = lean_uint64_xor(v_fold_354_, v___x_356_);
v___x_358_ = lean_uint64_to_usize(v___x_357_);
v___x_359_ = lean_usize_of_nat(v___x_350_);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_sub(v___x_359_, v___x_360_);
v___x_362_ = lean_usize_land(v___x_358_, v___x_361_);
v___x_363_ = lean_array_uget_borrowed(v_buckets_349_, v___x_362_);
v___x_364_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_348_, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_365_, v_a_366_);
lean_dec_ref(v_a_366_);
lean_dec_ref(v_m_365_);
return v_res_367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v_dummy_370_; 
v___x_369_ = lean_box(0);
v_dummy_370_ = l_Lean_Expr_sort___override(v___x_369_);
return v_dummy_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_371_, lean_object* v_post_372_, size_t v_sz_373_, size_t v_i_374_, lean_object* v_bs_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = lean_usize_dec_lt(v_i_374_, v_sz_373_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec_ref(v_post_372_);
lean_dec_ref(v_pre_371_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v_bs_375_);
return v___x_381_;
}
else
{
lean_object* v_v_382_; lean_object* v___x_383_; 
v_v_382_ = lean_array_uget_borrowed(v_bs_375_, v_i_374_);
lean_inc(v_v_382_);
lean_inc_ref(v_post_372_);
lean_inc_ref(v_pre_371_);
v___x_383_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_371_, v_post_372_, v_v_382_, v___y_376_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_385_; lean_object* v_bs_x27_386_; size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref(v___x_383_);
v___x_385_ = lean_unsigned_to_nat(0u);
v_bs_x27_386_ = lean_array_uset(v_bs_375_, v_i_374_, v___x_385_);
v___x_387_ = ((size_t)1ULL);
v___x_388_ = lean_usize_add(v_i_374_, v___x_387_);
v___x_389_ = lean_array_uset(v_bs_x27_386_, v_i_374_, v_a_384_);
v_i_374_ = v___x_388_;
v_bs_375_ = v___x_389_;
goto _start;
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v_bs_375_);
lean_dec_ref(v_post_372_);
lean_dec_ref(v_pre_371_);
v_a_391_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_383_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_383_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_399_, lean_object* v_post_400_, lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
if (lean_obj_tag(v_x_401_) == 5)
{
lean_object* v_fn_408_; lean_object* v_arg_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_fn_408_ = lean_ctor_get(v_x_401_, 0);
lean_inc_ref(v_fn_408_);
v_arg_409_ = lean_ctor_get(v_x_401_, 1);
lean_inc_ref(v_arg_409_);
lean_dec_ref(v_x_401_);
v___x_410_ = lean_array_set(v_x_402_, v_x_403_, v_arg_409_);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_sub(v_x_403_, v___x_411_);
lean_dec(v_x_403_);
v_x_401_ = v_fn_408_;
v_x_402_ = v___x_410_;
v_x_403_ = v___x_412_;
goto _start;
}
else
{
lean_object* v___x_414_; 
lean_dec(v_x_403_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_399_);
v___x_414_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_399_, v_post_400_, v_x_401_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; size_t v_sz_416_; size_t v___x_417_; lean_object* v___x_418_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v___x_414_);
v_sz_416_ = lean_array_size(v_x_402_);
v___x_417_ = ((size_t)0ULL);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_399_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_399_, v_post_400_, v_sz_416_, v___x_417_, v_x_402_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_418_);
v___x_420_ = l_Lean_mkAppN(v_a_415_, v_a_419_);
lean_dec(v_a_419_);
v___x_421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_399_, v_post_400_, v___x_420_, v___y_404_, v___y_405_, v___y_406_);
return v___x_421_;
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_415_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_399_);
v_a_422_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_418_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_dec_ref(v_x_402_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_399_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_430_, lean_object* v_pre_431_, lean_object* v_e_432_, lean_object* v_post_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___y_439_; lean_object* v___y_440_; uint8_t v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; uint8_t v___y_446_; lean_object* v___y_456_; uint8_t v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; uint8_t v___y_461_; lean_object* v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; uint8_t v___y_474_; lean_object* v___x_481_; 
v___x_481_ = l_Lean_Core_checkSystem(v___x_430_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
lean_dec_ref(v___x_481_);
lean_inc_ref(v_pre_431_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc_ref(v_e_432_);
v___x_482_ = lean_apply_4(v_pre_431_, v_e_432_, v___y_435_, v___y_436_, lean_box(0));
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_572_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_572_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_572_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_572_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___y_488_; 
switch(lean_obj_tag(v_a_483_))
{
case 0:
{
lean_object* v_e_562_; lean_object* v___x_564_; 
lean_dec_ref(v_post_433_);
lean_dec_ref(v_e_432_);
lean_dec_ref(v_pre_431_);
v_e_562_ = lean_ctor_get(v_a_483_, 0);
lean_inc_ref(v_e_562_);
lean_dec_ref(v_a_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v_e_562_);
v___x_564_ = v___x_485_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_e_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
case 1:
{
lean_object* v_e_566_; lean_object* v___x_567_; 
lean_del_object(v___x_485_);
lean_dec_ref(v_e_432_);
v_e_566_ = lean_ctor_get(v_a_483_, 0);
lean_inc_ref(v_e_566_);
lean_dec_ref(v_a_483_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_567_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_e_566_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref(v___x_567_);
v___x_569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v_a_568_, v___y_434_, v___y_435_, v___y_436_);
return v___x_569_;
}
else
{
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_567_;
}
}
default: 
{
lean_object* v_e_x3f_570_; 
lean_del_object(v___x_485_);
v_e_x3f_570_ = lean_ctor_get(v_a_483_, 0);
lean_inc(v_e_x3f_570_);
lean_dec_ref(v_a_483_);
if (lean_obj_tag(v_e_x3f_570_) == 0)
{
v___y_488_ = v_e_432_;
goto v___jp_487_;
}
else
{
lean_object* v_val_571_; 
lean_dec_ref(v_e_432_);
v_val_571_ = lean_ctor_get(v_e_x3f_570_, 0);
lean_inc(v_val_571_);
lean_dec_ref(v_e_x3f_570_);
v___y_488_ = v_val_571_;
goto v___jp_487_;
}
}
}
v___jp_487_:
{
switch(lean_obj_tag(v___y_488_))
{
case 7:
{
lean_object* v_binderName_489_; lean_object* v_binderType_490_; lean_object* v_body_491_; uint8_t v_binderInfo_492_; lean_object* v___x_493_; 
v_binderName_489_ = lean_ctor_get(v___y_488_, 0);
lean_inc(v_binderName_489_);
v_binderType_490_ = lean_ctor_get(v___y_488_, 1);
v_body_491_ = lean_ctor_get(v___y_488_, 2);
v_binderInfo_492_ = lean_ctor_get_uint8(v___y_488_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_490_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_binderType_490_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref(v___x_493_);
lean_inc_ref(v_body_491_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_491_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; size_t v___x_497_; size_t v___x_498_; uint8_t v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
v___x_497_ = lean_ptr_addr(v_binderType_490_);
v___x_498_ = lean_ptr_addr(v_a_494_);
v___x_499_ = lean_usize_dec_eq(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
v___y_469_ = v_a_496_;
v___y_470_ = v_binderName_489_;
v___y_471_ = v_binderInfo_492_;
v___y_472_ = v___y_488_;
v___y_473_ = v_a_494_;
v___y_474_ = v___x_499_;
goto v___jp_468_;
}
else
{
size_t v___x_500_; size_t v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_ptr_addr(v_body_491_);
v___x_501_ = lean_ptr_addr(v_a_496_);
v___x_502_ = lean_usize_dec_eq(v___x_500_, v___x_501_);
v___y_469_ = v_a_496_;
v___y_470_ = v_binderName_489_;
v___y_471_ = v_binderInfo_492_;
v___y_472_ = v___y_488_;
v___y_473_ = v_a_494_;
v___y_474_ = v___x_502_;
goto v___jp_468_;
}
}
else
{
lean_dec(v_a_494_);
lean_dec_ref(v___y_488_);
lean_dec(v_binderName_489_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_495_;
}
}
else
{
lean_dec_ref(v___y_488_);
lean_dec(v_binderName_489_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_493_;
}
}
case 6:
{
lean_object* v_binderName_503_; lean_object* v_binderType_504_; lean_object* v_body_505_; uint8_t v_binderInfo_506_; lean_object* v___x_507_; 
v_binderName_503_ = lean_ctor_get(v___y_488_, 0);
lean_inc(v_binderName_503_);
v_binderType_504_ = lean_ctor_get(v___y_488_, 1);
v_body_505_ = lean_ctor_get(v___y_488_, 2);
v_binderInfo_506_ = lean_ctor_get_uint8(v___y_488_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_504_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_binderType_504_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_507_);
lean_inc_ref(v_body_505_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_505_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; size_t v___x_511_; size_t v___x_512_; uint8_t v___x_513_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref(v___x_509_);
v___x_511_ = lean_ptr_addr(v_binderType_504_);
v___x_512_ = lean_ptr_addr(v_a_508_);
v___x_513_ = lean_usize_dec_eq(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
v___y_456_ = v_a_510_;
v___y_457_ = v_binderInfo_506_;
v___y_458_ = v_a_508_;
v___y_459_ = v___y_488_;
v___y_460_ = v_binderName_503_;
v___y_461_ = v___x_513_;
goto v___jp_455_;
}
else
{
size_t v___x_514_; size_t v___x_515_; uint8_t v___x_516_; 
v___x_514_ = lean_ptr_addr(v_body_505_);
v___x_515_ = lean_ptr_addr(v_a_510_);
v___x_516_ = lean_usize_dec_eq(v___x_514_, v___x_515_);
v___y_456_ = v_a_510_;
v___y_457_ = v_binderInfo_506_;
v___y_458_ = v_a_508_;
v___y_459_ = v___y_488_;
v___y_460_ = v_binderName_503_;
v___y_461_ = v___x_516_;
goto v___jp_455_;
}
}
else
{
lean_dec(v_a_508_);
lean_dec(v_binderName_503_);
lean_dec_ref(v___y_488_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_509_;
}
}
else
{
lean_dec_ref(v___y_488_);
lean_dec(v_binderName_503_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_507_;
}
}
case 8:
{
lean_object* v_declName_517_; lean_object* v_type_518_; lean_object* v_value_519_; lean_object* v_body_520_; uint8_t v_nondep_521_; lean_object* v___x_522_; 
v_declName_517_ = lean_ctor_get(v___y_488_, 0);
lean_inc(v_declName_517_);
v_type_518_ = lean_ctor_get(v___y_488_, 1);
v_value_519_ = lean_ctor_get(v___y_488_, 2);
v_body_520_ = lean_ctor_get(v___y_488_, 3);
lean_inc_ref(v_body_520_);
v_nondep_521_ = lean_ctor_get_uint8(v___y_488_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_518_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_type_518_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
lean_inc_ref(v_value_519_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_value_519_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref(v___x_524_);
lean_inc_ref(v_body_520_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_520_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; size_t v___x_528_; size_t v___x_529_; uint8_t v___x_530_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_526_);
v___x_528_ = lean_ptr_addr(v_type_518_);
v___x_529_ = lean_ptr_addr(v_a_523_);
v___x_530_ = lean_usize_dec_eq(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
v___y_439_ = v_a_527_;
v___y_440_ = v_declName_517_;
v___y_441_ = v_nondep_521_;
v___y_442_ = v_a_523_;
v___y_443_ = v___y_488_;
v___y_444_ = v_body_520_;
v___y_445_ = v_a_525_;
v___y_446_ = v___x_530_;
goto v___jp_438_;
}
else
{
size_t v___x_531_; size_t v___x_532_; uint8_t v___x_533_; 
v___x_531_ = lean_ptr_addr(v_value_519_);
v___x_532_ = lean_ptr_addr(v_a_525_);
v___x_533_ = lean_usize_dec_eq(v___x_531_, v___x_532_);
v___y_439_ = v_a_527_;
v___y_440_ = v_declName_517_;
v___y_441_ = v_nondep_521_;
v___y_442_ = v_a_523_;
v___y_443_ = v___y_488_;
v___y_444_ = v_body_520_;
v___y_445_ = v_a_525_;
v___y_446_ = v___x_533_;
goto v___jp_438_;
}
}
else
{
lean_dec(v_a_525_);
lean_dec(v_a_523_);
lean_dec_ref(v_body_520_);
lean_dec_ref(v___y_488_);
lean_dec(v_declName_517_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_526_;
}
}
else
{
lean_dec(v_a_523_);
lean_dec_ref(v_body_520_);
lean_dec_ref(v___y_488_);
lean_dec(v_declName_517_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_524_;
}
}
else
{
lean_dec_ref(v_body_520_);
lean_dec_ref(v___y_488_);
lean_dec(v_declName_517_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_522_;
}
}
case 5:
{
lean_object* v_dummy_534_; lean_object* v_nargs_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_dummy_534_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_535_ = l_Lean_Expr_getAppNumArgs(v___y_488_);
lean_inc(v_nargs_535_);
v___x_536_ = lean_mk_array(v_nargs_535_, v_dummy_534_);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_sub(v_nargs_535_, v___x_537_);
lean_dec(v_nargs_535_);
v___x_539_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_431_, v_post_433_, v___y_488_, v___x_536_, v___x_538_, v___y_434_, v___y_435_, v___y_436_);
return v___x_539_;
}
case 10:
{
lean_object* v_data_540_; lean_object* v_expr_541_; lean_object* v___x_542_; 
v_data_540_ = lean_ctor_get(v___y_488_, 0);
v_expr_541_ = lean_ctor_get(v___y_488_, 1);
lean_inc_ref(v_expr_541_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_expr_541_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; size_t v___x_544_; size_t v___x_545_; uint8_t v___x_546_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_ptr_addr(v_expr_541_);
v___x_545_ = lean_ptr_addr(v_a_543_);
v___x_546_ = lean_usize_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_inc(v_data_540_);
lean_dec_ref(v___y_488_);
v___x_547_ = l_Lean_Expr_mdata___override(v_data_540_, v_a_543_);
v___x_548_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_547_, v___y_434_, v___y_435_, v___y_436_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; 
lean_dec(v_a_543_);
v___x_549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_488_, v___y_434_, v___y_435_, v___y_436_);
return v___x_549_;
}
}
else
{
lean_dec_ref(v___y_488_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_542_;
}
}
case 11:
{
lean_object* v_typeName_550_; lean_object* v_idx_551_; lean_object* v_struct_552_; lean_object* v___x_553_; 
v_typeName_550_ = lean_ctor_get(v___y_488_, 0);
v_idx_551_ = lean_ctor_get(v___y_488_, 1);
v_struct_552_ = lean_ctor_get(v___y_488_, 2);
lean_inc_ref(v_struct_552_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_553_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_struct_552_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; size_t v___x_555_; size_t v___x_556_; uint8_t v___x_557_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref(v___x_553_);
v___x_555_ = lean_ptr_addr(v_struct_552_);
v___x_556_ = lean_ptr_addr(v_a_554_);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_inc(v_idx_551_);
lean_inc(v_typeName_550_);
lean_dec_ref(v___y_488_);
v___x_558_ = l_Lean_Expr_proj___override(v_typeName_550_, v_idx_551_, v_a_554_);
v___x_559_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_558_, v___y_434_, v___y_435_, v___y_436_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; 
lean_dec(v_a_554_);
v___x_560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_488_, v___y_434_, v___y_435_, v___y_436_);
return v___x_560_;
}
}
else
{
lean_dec_ref(v___y_488_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_553_;
}
}
default: 
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_488_, v___y_434_, v___y_435_, v___y_436_);
return v___x_561_;
}
}
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref(v_post_433_);
lean_dec_ref(v_e_432_);
lean_dec_ref(v_pre_431_);
v_a_573_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_482_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_482_);
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
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_post_433_);
lean_dec_ref(v_e_432_);
lean_dec_ref(v_pre_431_);
v_a_581_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_481_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_481_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
v___jp_438_:
{
if (v___y_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec_ref(v___y_444_);
lean_dec_ref(v___y_443_);
v___x_447_ = l_Lean_Expr_letE___override(v___y_440_, v___y_442_, v___y_445_, v___y_439_, v___y_441_);
v___x_448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_447_, v___y_434_, v___y_435_, v___y_436_);
return v___x_448_;
}
else
{
size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_ptr_addr(v___y_444_);
lean_dec_ref(v___y_444_);
v___x_450_ = lean_ptr_addr(v___y_439_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec_ref(v___y_443_);
v___x_452_ = l_Lean_Expr_letE___override(v___y_440_, v___y_442_, v___y_445_, v___y_439_, v___y_441_);
v___x_453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_452_, v___y_434_, v___y_435_, v___y_436_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; 
lean_dec_ref(v___y_445_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
v___x_454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_443_, v___y_434_, v___y_435_, v___y_436_);
return v___x_454_;
}
}
}
v___jp_455_:
{
if (v___y_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref(v___y_459_);
v___x_462_ = l_Lean_Expr_lam___override(v___y_460_, v___y_458_, v___y_456_, v___y_457_);
v___x_463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_462_, v___y_434_, v___y_435_, v___y_436_);
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = l_Lean_instBEqBinderInfo_beq(v___y_457_, v___y_457_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v___y_459_);
v___x_465_ = l_Lean_Expr_lam___override(v___y_460_, v___y_458_, v___y_456_, v___y_457_);
v___x_466_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_465_, v___y_434_, v___y_435_, v___y_436_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; 
lean_dec(v___y_460_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v___y_456_);
v___x_467_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_459_, v___y_434_, v___y_435_, v___y_436_);
return v___x_467_;
}
}
}
v___jp_468_:
{
if (v___y_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec_ref(v___y_472_);
v___x_475_ = l_Lean_Expr_forallE___override(v___y_470_, v___y_473_, v___y_469_, v___y_471_);
v___x_476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_475_, v___y_434_, v___y_435_, v___y_436_);
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = l_Lean_instBEqBinderInfo_beq(v___y_471_, v___y_471_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v___y_472_);
v___x_478_ = l_Lean_Expr_forallE___override(v___y_470_, v___y_473_, v___y_469_, v___y_471_);
v___x_479_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_478_, v___y_434_, v___y_435_, v___y_436_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; 
lean_dec_ref(v___y_473_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_472_, v___y_434_, v___y_435_, v___y_436_);
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_589_, lean_object* v_pre_590_, lean_object* v_e_591_, lean_object* v_post_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_589_, v_pre_590_, v_e_591_, v_post_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_598_, lean_object* v_post_599_, lean_object* v_e_600_, lean_object* v_a_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_inc(v_a_601_);
v___x_605_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_605_, 0, lean_box(0));
lean_closure_set(v___x_605_, 1, lean_box(0));
lean_closure_set(v___x_605_, 2, v_a_601_);
v___x_606_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_605_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_638_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_638_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_638_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_638_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_607_, v_e_600_);
lean_dec(v_a_607_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___x_614_; 
lean_del_object(v___x_609_);
v___x_612_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_600_);
v___f_613_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_613_, 0, v___x_612_);
lean_closure_set(v___f_613_, 1, v_pre_598_);
lean_closure_set(v___f_613_, 2, v_e_600_);
lean_closure_set(v___f_613_, 3, v_post_599_);
v___x_614_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_613_, v_a_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___f_616_; lean_object* v___x_617_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_n(v_a_615_, 2);
lean_dec_ref(v___x_614_);
lean_inc(v_a_601_);
v___f_616_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_616_, 0, v_a_601_);
lean_closure_set(v___f_616_, 1, v_e_600_);
lean_closure_set(v___f_616_, 2, v_a_615_);
v___x_617_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_616_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_625_);
v___x_619_ = v___x_617_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_dec(v___x_617_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v_a_615_);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_615_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_a_615_);
v_a_626_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_617_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_617_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_dec_ref(v_e_600_);
return v___x_614_;
}
}
else
{
lean_object* v_val_634_; lean_object* v___x_636_; 
lean_dec_ref(v_e_600_);
lean_dec_ref(v_post_599_);
lean_dec_ref(v_pre_598_);
v_val_634_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_val_634_);
lean_dec_ref(v___x_611_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_val_634_);
v___x_636_ = v___x_609_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_val_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_e_600_);
lean_dec_ref(v_post_599_);
lean_dec_ref(v_pre_598_);
v_a_639_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_606_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_606_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_647_, lean_object* v_post_648_, lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; 
lean_inc_ref(v_post_648_);
lean_inc(v___y_652_);
lean_inc_ref(v___y_651_);
lean_inc_ref(v_e_649_);
v___x_654_ = lean_apply_4(v_post_648_, v_e_649_, v___y_651_, v___y_652_, lean_box(0));
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_673_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_673_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_673_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_673_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
switch(lean_obj_tag(v_a_655_))
{
case 0:
{
lean_object* v_e_659_; lean_object* v___x_661_; 
lean_dec_ref(v_e_649_);
lean_dec_ref(v_post_648_);
lean_dec_ref(v_pre_647_);
v_e_659_ = lean_ctor_get(v_a_655_, 0);
lean_inc_ref(v_e_659_);
lean_dec_ref(v_a_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_e_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_e_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
case 1:
{
lean_object* v_e_663_; lean_object* v___x_664_; 
lean_del_object(v___x_657_);
lean_dec_ref(v_e_649_);
v_e_663_ = lean_ctor_get(v_a_655_, 0);
lean_inc_ref(v_e_663_);
lean_dec_ref(v_a_655_);
v___x_664_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_647_, v_post_648_, v_e_663_, v_a_650_, v___y_651_, v___y_652_);
return v___x_664_;
}
default: 
{
lean_object* v_e_x3f_665_; 
lean_dec_ref(v_post_648_);
lean_dec_ref(v_pre_647_);
v_e_x3f_665_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_e_x3f_665_);
lean_dec_ref(v_a_655_);
if (lean_obj_tag(v_e_x3f_665_) == 0)
{
lean_object* v___x_667_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_e_649_);
v___x_667_ = v___x_657_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_e_649_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v_val_669_; lean_object* v___x_671_; 
lean_dec_ref(v_e_649_);
v_val_669_ = lean_ctor_get(v_e_x3f_665_, 0);
lean_inc(v_val_669_);
lean_dec_ref(v_e_x3f_665_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_val_669_);
v___x_671_ = v___x_657_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_val_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_e_649_);
lean_dec_ref(v_post_648_);
lean_dec_ref(v_pre_647_);
v_a_674_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_654_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_654_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_682_, lean_object* v_post_683_, lean_object* v_e_684_, lean_object* v_a_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_682_, v_post_683_, v_e_684_, v_a_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v_a_685_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_690_, lean_object* v_post_691_, lean_object* v_sz_692_, lean_object* v_i_693_, lean_object* v_bs_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
size_t v_sz_boxed_699_; size_t v_i_boxed_700_; lean_object* v_res_701_; 
v_sz_boxed_699_ = lean_unbox_usize(v_sz_692_);
lean_dec(v_sz_692_);
v_i_boxed_700_ = lean_unbox_usize(v_i_693_);
lean_dec(v_i_693_);
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_690_, v_post_691_, v_sz_boxed_699_, v_i_boxed_700_, v_bs_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_702_, lean_object* v_post_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_702_, v_post_703_, v_x_704_, v_x_705_, v_x_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_712_, lean_object* v_post_713_, lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_712_, v_post_713_, v_e_714_, v_a_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_a_715_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_720_, lean_object* v_x_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_apply_1(v_x_721_, lean_box(0));
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_727_, lean_object* v_x_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_727_, v_x_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_732_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_box(0);
v___x_734_ = lean_unsigned_to_nat(16u);
v___x_735_ = lean_mk_array(v___x_734_, v___x_733_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_740_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_740_, 0, lean_box(0));
lean_closure_set(v___x_740_, 1, lean_box(0));
lean_closure_set(v___x_740_, 2, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_741_, lean_object* v_pre_742_, lean_object* v_post_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_a_749_; lean_object* v___x_750_; 
v___x_747_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_748_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_747_, v___y_744_, v___y_745_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_742_, v_post_743_, v_input_741_, v_a_749_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref(v___x_750_);
v___x_752_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_752_, 0, lean_box(0));
lean_closure_set(v___x_752_, 1, lean_box(0));
lean_closure_set(v___x_752_, 2, v_a_749_);
v___x_753_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_752_, v___y_744_, v___y_745_);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v___x_753_, 0);
lean_dec(v_unused_761_);
v___x_755_ = v___x_753_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_dec(v___x_753_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_a_751_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_751_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_dec(v_a_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_762_, lean_object* v_pre_763_, lean_object* v_post_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_762_, v_pre_763_, v_post_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v___f_775_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_776_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_777_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_771_, v___f_775_, v___f_776_, v_a_772_, v_a_773_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_elimOptParam(v_type_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_783_, lean_object* v_m_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_784_, v_a_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_787_, lean_object* v_m_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_787_, v_m_788_, v_a_789_);
lean_dec_ref(v_a_789_);
lean_dec_ref(v_m_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_791_, lean_object* v_ref_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_792_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_797_, lean_object* v_ref_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_797_, v_ref_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_813_, lean_object* v_x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_820_, lean_object* v_x_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_820_, v_x_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_827_, lean_object* v_m_828_, lean_object* v_a_829_, lean_object* v_b_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_828_, v_a_829_, v_b_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_833_, v_x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_836_, lean_object* v_a_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_836_, v_a_837_, v_x_838_);
lean_dec(v_x_838_);
lean_dec_ref(v_a_837_);
return v_res_839_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_840_, lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_841_, v_x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_844_, lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_844_, v_a_845_, v_x_846_);
lean_dec(v_x_846_);
lean_dec_ref(v_a_845_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_849_, lean_object* v_data_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_852_, lean_object* v_a_853_, lean_object* v_b_854_, lean_object* v_x_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_853_, v_b_854_, v_x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_857_, lean_object* v_i_858_, lean_object* v_source_859_, lean_object* v_target_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_858_, v_source_859_, v_target_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_866_, lean_object* v_as_867_, size_t v_sz_868_, size_t v_i_869_, lean_object* v_b_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_a_877_; uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_lt(v_i_869_, v_sz_868_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v_b_870_);
return v___x_882_;
}
else
{
lean_object* v_snd_883_; lean_object* v_fst_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_962_; 
v_snd_883_ = lean_ctor_get(v_b_870_, 1);
v_fst_884_ = lean_ctor_get(v_b_870_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_b_870_);
if (v_isSharedCheck_962_ == 0)
{
v___x_886_ = v_b_870_;
v_isShared_887_ = v_isSharedCheck_962_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_snd_883_);
lean_inc(v_fst_884_);
lean_dec(v_b_870_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_962_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_array_888_; lean_object* v_start_889_; lean_object* v_stop_890_; uint8_t v___x_891_; 
v_array_888_ = lean_ctor_get(v_snd_883_, 0);
v_start_889_ = lean_ctor_get(v_snd_883_, 1);
v_stop_890_ = lean_ctor_get(v_snd_883_, 2);
v___x_891_ = lean_nat_dec_lt(v_start_889_, v_stop_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_893_; 
if (v_isShared_887_ == 0)
{
v___x_893_ = v___x_886_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_fst_884_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_snd_883_);
v___x_893_ = v_reuseFailAlloc_895_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
else
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_958_; 
lean_inc(v_stop_890_);
lean_inc(v_start_889_);
lean_inc_ref(v_array_888_);
v_isSharedCheck_958_ = !lean_is_exclusive(v_snd_883_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; lean_object* v_unused_961_; 
v_unused_959_ = lean_ctor_get(v_snd_883_, 2);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_snd_883_, 1);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_snd_883_, 0);
lean_dec(v_unused_961_);
v___x_897_ = v_snd_883_;
v_isShared_898_ = v_isSharedCheck_958_;
goto v_resetjp_896_;
}
else
{
lean_dec(v_snd_883_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_958_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_array_uget_borrowed(v_as_867_, v_i_869_);
lean_inc(v___y_874_);
lean_inc_ref(v___y_873_);
lean_inc(v___y_872_);
lean_inc_ref(v___y_871_);
lean_inc(v_a_899_);
v___x_900_ = lean_infer_type(v_a_899_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref(v___x_900_);
v___x_902_ = lean_array_fget(v_array_888_, v_start_889_);
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_add(v_start_889_, v___x_903_);
lean_dec(v_start_889_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_904_);
v___x_906_ = v___x_897_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_array_888_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_stop_890_);
v___x_906_ = v_reuseFailAlloc_949_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
if (v_skipIfPropOrEq_866_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v_a_901_);
lean_inc(v_a_899_);
v___x_907_ = l_Lean_Meta_mkEqHEq(v_a_899_, v___x_902_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v___x_909_ = lean_array_push(v_fst_884_, v_a_908_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v___x_906_);
lean_ctor_set(v___x_886_, 0, v___x_909_);
v___x_911_ = v___x_886_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
v_a_877_ = v___x_911_;
goto v___jp_876_;
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v___x_906_);
lean_del_object(v___x_886_);
lean_dec(v_fst_884_);
v_a_913_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_907_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_907_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Meta_isProp(v_a_901_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; uint8_t v___x_927_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
v___x_927_ = lean_unbox(v_a_922_);
lean_dec(v_a_922_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; 
v___x_928_ = lean_expr_eqv(v_a_899_, v___x_902_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_del_object(v___x_886_);
lean_inc(v_a_899_);
v___x_929_ = l_Lean_Meta_mkEqHEq(v_a_899_, v___x_902_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref(v___x_929_);
v___x_931_ = lean_array_push(v_fst_884_, v_a_930_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_906_);
v_a_877_ = v___x_932_;
goto v___jp_876_;
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v___x_906_);
lean_dec(v_fst_884_);
v_a_933_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_929_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_929_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_dec(v___x_902_);
goto v___jp_923_;
}
}
else
{
lean_dec(v___x_902_);
goto v___jp_923_;
}
v___jp_923_:
{
lean_object* v___x_925_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v___x_906_);
v___x_925_ = v___x_886_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_fst_884_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_906_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
v_a_877_ = v___x_925_;
goto v___jp_876_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v___x_906_);
lean_dec(v___x_902_);
lean_del_object(v___x_886_);
lean_dec(v_fst_884_);
v_a_941_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_921_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_921_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_del_object(v___x_897_);
lean_dec(v_stop_890_);
lean_dec(v_start_889_);
lean_dec_ref(v_array_888_);
lean_del_object(v___x_886_);
lean_dec(v_fst_884_);
v_a_950_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_900_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_900_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
}
v___jp_876_:
{
size_t v___x_878_; size_t v___x_879_; 
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_add(v_i_869_, v___x_878_);
v_i_869_ = v___x_879_;
v_b_870_ = v_a_877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_963_, lean_object* v_as_964_, lean_object* v_sz_965_, lean_object* v_i_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_973_; size_t v_sz_boxed_974_; size_t v_i_boxed_975_; lean_object* v_res_976_; 
v_skipIfPropOrEq_boxed_973_ = lean_unbox(v_skipIfPropOrEq_963_);
v_sz_boxed_974_ = lean_unbox_usize(v_sz_965_);
lean_dec(v_sz_965_);
v_i_boxed_975_ = lean_unbox_usize(v_i_966_);
lean_dec(v_i_966_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_973_, v_as_964_, v_sz_boxed_974_, v_i_boxed_975_, v_b_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v_as_964_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_979_, lean_object* v_args2_980_, uint8_t v_skipIfPropOrEq_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; lean_object* v_eqs_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; size_t v_sz_992_; size_t v___x_993_; lean_object* v___x_994_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v_eqs_988_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_989_ = lean_array_get_size(v_args2_980_);
v___x_990_ = l_Array_toSubarray___redArg(v_args2_980_, v___x_987_, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_eqs_988_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v_sz_992_ = lean_array_size(v_args1_979_);
v___x_993_ = ((size_t)0ULL);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_981_, v_args1_979_, v_sz_992_, v___x_993_, v___x_991_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_fst_999_; lean_object* v___x_1001_; 
v_fst_999_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_fst_999_);
lean_dec(v_a_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_fst_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_a_1004_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_994_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_994_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_1012_, lean_object* v_args2_1013_, lean_object* v_skipIfPropOrEq_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_1020_; lean_object* v_res_1021_; 
v_skipIfPropOrEq_boxed_1020_ = lean_unbox(v_skipIfPropOrEq_1014_);
v_res_1021_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1012_, v_args2_1013_, v_skipIfPropOrEq_boxed_1020_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec_ref(v_args1_1012_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1024_);
v___x_1029_ = lean_apply_6(v_k_1022_, v_b_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, lean_box(0));
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_1030_, v_b_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1038_, uint8_t v_bi_1039_, lean_object* v_type_1040_, lean_object* v_k_1041_, uint8_t v_kind_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___f_1048_; lean_object* v___x_1049_; 
v___f_1048_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1048_, 0, v_k_1041_);
v___x_1049_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1038_, v_bi_1039_, v_type_1040_, v___f_1048_, v_kind_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_a_1058_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1049_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1049_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1066_, lean_object* v_bi_1067_, lean_object* v_type_1068_, lean_object* v_k_1069_, lean_object* v_kind_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v_bi_boxed_1076_; uint8_t v_kind_boxed_1077_; lean_object* v_res_1078_; 
v_bi_boxed_1076_ = lean_unbox(v_bi_1067_);
v_kind_boxed_1077_ = lean_unbox(v_kind_1070_);
v_res_1078_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1066_, v_bi_boxed_1076_, v_type_1068_, v_k_1069_, v_kind_boxed_1077_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1079_, lean_object* v_name_1080_, uint8_t v_bi_1081_, lean_object* v_type_1082_, lean_object* v_k_1083_, uint8_t v_kind_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1080_, v_bi_1081_, v_type_1082_, v_k_1083_, v_kind_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1091_, lean_object* v_name_1092_, lean_object* v_bi_1093_, lean_object* v_type_1094_, lean_object* v_k_1095_, lean_object* v_kind_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v_bi_boxed_1102_; uint8_t v_kind_boxed_1103_; lean_object* v_res_1104_; 
v_bi_boxed_1102_ = lean_unbox(v_bi_1093_);
v_kind_boxed_1103_ = lean_unbox(v_kind_1096_);
v_res_1104_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1091_, v_name_1092_, v_bi_boxed_1102_, v_type_1094_, v_k_1095_, v_kind_boxed_1103_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; lean_object* v___x_1113_; lean_object* v_mctx_1114_; lean_object* v_lctx_1115_; lean_object* v_options_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1111_ = lean_st_ref_get(v___y_1109_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = lean_st_ref_get(v___y_1107_);
v_mctx_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_mctx_1114_);
lean_dec(v___x_1113_);
v_lctx_1115_ = lean_ctor_get(v___y_1106_, 2);
v_options_1116_ = lean_ctor_get(v___y_1108_, 2);
lean_inc_ref(v_options_1116_);
lean_inc_ref(v_lctx_1115_);
v___x_1117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1117_, 0, v_env_1112_);
lean_ctor_set(v___x_1117_, 1, v_mctx_1114_);
lean_ctor_set(v___x_1117_, 2, v_lctx_1115_);
lean_ctor_set(v___x_1117_, 3, v_options_1116_);
v___x_1118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_msgData_1105_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_ref_1133_; lean_object* v___x_1134_; lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_ref_1133_ = lean_ctor_get(v___y_1130_, 5);
v___x_1134_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
lean_inc(v_ref_1133_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_ref_1133_);
lean_ctor_set(v___x_1139_, 1, v_a_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 1);
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1151_, lean_object* v_body_1152_, lean_object* v_args2_1153_, lean_object* v_args2New_1154_, lean_object* v_ctorVal_1155_, lean_object* v_useEq_1156_, lean_object* v_args1_1157_, lean_object* v_resultType_1158_, lean_object* v_k_1159_, lean_object* v_arg2_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_useEq_boxed_1166_; lean_object* v_res_1167_; 
v_useEq_boxed_1166_ = lean_unbox(v_useEq_1156_);
v_res_1167_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1151_, v_body_1152_, v_args2_1153_, v_args2New_1154_, v_ctorVal_1155_, v_useEq_boxed_1166_, v_args1_1157_, v_resultType_1158_, v_k_1159_, v_arg2_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v_body_1152_);
lean_dec(v_i_1151_);
return v_res_1167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1174_, uint8_t v_useEq_1175_, lean_object* v_args1_1176_, lean_object* v_resultType_1177_, lean_object* v_k_1178_, lean_object* v_i_1179_, lean_object* v_type_1180_, lean_object* v_args2_1181_, lean_object* v_args2New_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_array_get_size(v_args1_1176_);
v___x_1189_ = lean_nat_dec_lt(v_i_1179_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref(v_type_1180_);
lean_dec(v_i_1179_);
lean_dec_ref(v_resultType_1177_);
lean_dec_ref(v_args1_1176_);
lean_dec_ref(v_ctorVal_1174_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
lean_inc_ref(v_a_1183_);
v___x_1190_ = lean_apply_7(v_k_1178_, v_args2_1181_, v_args2New_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; 
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
lean_inc_ref(v_a_1183_);
v___x_1191_ = lean_whnf(v_type_1180_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1191_);
if (lean_obj_tag(v_a_1192_) == 7)
{
lean_object* v_binderName_1193_; lean_object* v_binderType_1194_; lean_object* v_body_1195_; lean_object* v_lctx_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_binderName_1193_ = lean_ctor_get(v_a_1192_, 0);
lean_inc(v_binderName_1193_);
v_binderType_1194_ = lean_ctor_get(v_a_1192_, 1);
lean_inc_ref(v_binderType_1194_);
v_body_1195_ = lean_ctor_get(v_a_1192_, 2);
lean_inc_ref(v_body_1195_);
lean_dec_ref(v_a_1192_);
v_lctx_1196_ = lean_ctor_get(v_a_1183_, 2);
v___x_1197_ = lean_array_fget_borrowed(v_args1_1176_, v_i_1179_);
lean_inc(v___x_1197_);
lean_inc_ref(v_lctx_1196_);
v___x_1198_ = l_Lean_Meta_occursOrInType(v_lctx_1196_, v___x_1197_, v_resultType_1177_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___f_1200_; uint8_t v___y_1202_; 
v___x_1199_ = lean_box(v_useEq_1175_);
v___f_1200_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1200_, 0, v_i_1179_);
lean_closure_set(v___f_1200_, 1, v_body_1195_);
lean_closure_set(v___f_1200_, 2, v_args2_1181_);
lean_closure_set(v___f_1200_, 3, v_args2New_1182_);
lean_closure_set(v___f_1200_, 4, v_ctorVal_1174_);
lean_closure_set(v___f_1200_, 5, v___x_1199_);
lean_closure_set(v___f_1200_, 6, v_args1_1176_);
lean_closure_set(v___f_1200_, 7, v_resultType_1177_);
lean_closure_set(v___f_1200_, 8, v_k_1178_);
if (v_useEq_1175_ == 0)
{
uint8_t v___x_1205_; 
v___x_1205_ = 1;
v___y_1202_ = v___x_1205_;
goto v___jp_1201_;
}
else
{
uint8_t v___x_1206_; 
v___x_1206_ = 0;
v___y_1202_ = v___x_1206_;
goto v___jp_1201_;
}
v___jp_1201_:
{
uint8_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = 0;
v___x_1204_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1193_, v___y_1202_, v_binderType_1194_, v___f_1200_, v___x_1203_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1204_;
}
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref(v_binderType_1194_);
lean_dec(v_binderName_1193_);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_i_1179_, v___x_1207_);
lean_dec(v_i_1179_);
v___x_1209_ = lean_expr_instantiate1(v_body_1195_, v___x_1197_);
lean_dec_ref(v_body_1195_);
lean_inc(v___x_1197_);
v___x_1210_ = lean_array_push(v_args2_1181_, v___x_1197_);
v_i_1179_ = v___x_1208_;
v_type_1180_ = v___x_1209_;
v_args2_1181_ = v___x_1210_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1212_; lean_object* v_name_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v_a_1192_);
lean_dec_ref(v_args2New_1182_);
lean_dec_ref(v_args2_1181_);
lean_dec(v_i_1179_);
lean_dec_ref(v_k_1178_);
lean_dec_ref(v_resultType_1177_);
lean_dec_ref(v_args1_1176_);
v_toConstantVal_1212_ = lean_ctor_get(v_ctorVal_1174_, 0);
lean_inc_ref(v_toConstantVal_1212_);
lean_dec_ref(v_ctorVal_1174_);
v_name_1213_ = lean_ctor_get(v_toConstantVal_1212_, 0);
lean_inc(v_name_1213_);
lean_dec_ref(v_toConstantVal_1212_);
v___x_1214_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1215_ = l_Lean_MessageData_ofName(v_name_1213_);
v___x_1216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1218_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1219_;
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_args2New_1182_);
lean_dec_ref(v_args2_1181_);
lean_dec(v_i_1179_);
lean_dec_ref(v_k_1178_);
lean_dec_ref(v_resultType_1177_);
lean_dec_ref(v_args1_1176_);
lean_dec_ref(v_ctorVal_1174_);
v_a_1220_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1191_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1191_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1228_, lean_object* v_body_1229_, lean_object* v_args2_1230_, lean_object* v_args2New_1231_, lean_object* v_ctorVal_1232_, uint8_t v_useEq_1233_, lean_object* v_args1_1234_, lean_object* v_resultType_1235_, lean_object* v_k_1236_, lean_object* v_arg2_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_i_1228_, v___x_1243_);
v___x_1245_ = lean_expr_instantiate1(v_body_1229_, v_arg2_1237_);
lean_inc_ref(v_arg2_1237_);
v___x_1246_ = lean_array_push(v_args2_1230_, v_arg2_1237_);
v___x_1247_ = lean_array_push(v_args2New_1231_, v_arg2_1237_);
v___x_1248_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1232_, v_useEq_1233_, v_args1_1234_, v_resultType_1235_, v_k_1236_, v___x_1244_, v___x_1245_, v___x_1246_, v___x_1247_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1249_, lean_object* v_useEq_1250_, lean_object* v_args1_1251_, lean_object* v_resultType_1252_, lean_object* v_k_1253_, lean_object* v_i_1254_, lean_object* v_type_1255_, lean_object* v_args2_1256_, lean_object* v_args2New_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
uint8_t v_useEq_boxed_1263_; lean_object* v_res_1264_; 
v_useEq_boxed_1263_ = lean_unbox(v_useEq_1250_);
v_res_1264_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1249_, v_useEq_boxed_1263_, v_args1_1251_, v_resultType_1252_, v_k_1253_, v_i_1254_, v_type_1255_, v_args2_1256_, v_args2New_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1265_, lean_object* v_msg_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1273_, lean_object* v_msg_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1273_, v_msg_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1281_, lean_object* v_h__1_1282_, lean_object* v_h__2_1283_){
_start:
{
if (lean_obj_tag(v_____x_1281_) == 7)
{
lean_object* v_binderName_1284_; lean_object* v_binderType_1285_; lean_object* v_body_1286_; uint8_t v_binderInfo_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec(v_h__2_1283_);
v_binderName_1284_ = lean_ctor_get(v_____x_1281_, 0);
lean_inc(v_binderName_1284_);
v_binderType_1285_ = lean_ctor_get(v_____x_1281_, 1);
lean_inc_ref(v_binderType_1285_);
v_body_1286_ = lean_ctor_get(v_____x_1281_, 2);
lean_inc_ref(v_body_1286_);
v_binderInfo_1287_ = lean_ctor_get_uint8(v_____x_1281_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1281_);
v___x_1288_ = lean_box(v_binderInfo_1287_);
v___x_1289_ = lean_apply_4(v_h__1_1282_, v_binderName_1284_, v_binderType_1285_, v_body_1286_, v___x_1288_);
return v___x_1289_;
}
else
{
lean_object* v___x_1290_; 
lean_dec(v_h__1_1282_);
v___x_1290_ = lean_apply_2(v_h__2_1283_, v_____x_1281_, lean_box(0));
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1291_, lean_object* v_____x_1292_, lean_object* v_h__1_1293_, lean_object* v_h__2_1294_){
_start:
{
if (lean_obj_tag(v_____x_1292_) == 7)
{
lean_object* v_binderName_1295_; lean_object* v_binderType_1296_; lean_object* v_body_1297_; uint8_t v_binderInfo_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v_h__2_1294_);
v_binderName_1295_ = lean_ctor_get(v_____x_1292_, 0);
lean_inc(v_binderName_1295_);
v_binderType_1296_ = lean_ctor_get(v_____x_1292_, 1);
lean_inc_ref(v_binderType_1296_);
v_body_1297_ = lean_ctor_get(v_____x_1292_, 2);
lean_inc_ref(v_body_1297_);
v_binderInfo_1298_ = lean_ctor_get_uint8(v_____x_1292_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1292_);
v___x_1299_ = lean_box(v_binderInfo_1298_);
v___x_1300_ = lean_apply_4(v_h__1_1293_, v_binderName_1295_, v_binderType_1296_, v_body_1297_, v___x_1299_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; 
lean_dec(v_h__1_1293_);
v___x_1301_ = lean_apply_2(v_h__2_1294_, v_____x_1292_, lean_box(0));
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1302_, lean_object* v_b_1303_, lean_object* v_c_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; 
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
v___x_1310_ = lean_apply_7(v_k_1302_, v_b_1303_, v_c_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, lean_box(0));
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1311_, lean_object* v_b_1312_, lean_object* v_c_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1311_, v_b_1312_, v_c_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1320_, lean_object* v_k_1321_, uint8_t v_cleanupAnnotations_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___f_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___f_1328_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1328_, 0, v_k_1321_);
v___x_1329_ = 0;
v___x_1330_ = lean_box(0);
v___x_1331_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1329_, v___x_1330_, v_type_1320_, v___f_1328_, v_cleanupAnnotations_1322_, v___x_1329_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1331_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1331_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1348_, lean_object* v_k_1349_, lean_object* v_cleanupAnnotations_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1356_; lean_object* v_res_1357_; 
v_cleanupAnnotations_boxed_1356_ = lean_unbox(v_cleanupAnnotations_1350_);
v_res_1357_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1348_, v_k_1349_, v_cleanupAnnotations_boxed_1356_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1358_, lean_object* v_type_1359_, lean_object* v_k_1360_, uint8_t v_cleanupAnnotations_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1359_, v_k_1360_, v_cleanupAnnotations_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1368_, lean_object* v_type_1369_, lean_object* v_k_1370_, lean_object* v_cleanupAnnotations_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1377_; lean_object* v_res_1378_; 
v_cleanupAnnotations_boxed_1377_ = lean_unbox(v_cleanupAnnotations_1371_);
v_res_1378_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1368_, v_type_1369_, v_k_1370_, v_cleanupAnnotations_boxed_1377_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1379_, lean_object* v_maxFVars_x3f_1380_, lean_object* v_k_1381_, uint8_t v_cleanupAnnotations_1382_, uint8_t v_whnfType_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___f_1389_; lean_object* v___x_1390_; 
v___f_1389_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1389_, 0, v_k_1381_);
v___x_1390_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1379_, v_maxFVars_x3f_1380_, v___f_1389_, v_cleanupAnnotations_1382_, v_whnfType_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1399_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1390_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1407_, lean_object* v_maxFVars_x3f_1408_, lean_object* v_k_1409_, lean_object* v_cleanupAnnotations_1410_, lean_object* v_whnfType_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1417_; uint8_t v_whnfType_boxed_1418_; lean_object* v_res_1419_; 
v_cleanupAnnotations_boxed_1417_ = lean_unbox(v_cleanupAnnotations_1410_);
v_whnfType_boxed_1418_ = lean_unbox(v_whnfType_1411_);
v_res_1419_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1407_, v_maxFVars_x3f_1408_, v_k_1409_, v_cleanupAnnotations_boxed_1417_, v_whnfType_boxed_1418_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1420_, lean_object* v_type_1421_, lean_object* v_maxFVars_x3f_1422_, lean_object* v_k_1423_, uint8_t v_cleanupAnnotations_1424_, uint8_t v_whnfType_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1421_, v_maxFVars_x3f_1422_, v_k_1423_, v_cleanupAnnotations_1424_, v_whnfType_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1432_, lean_object* v_type_1433_, lean_object* v_maxFVars_x3f_1434_, lean_object* v_k_1435_, lean_object* v_cleanupAnnotations_1436_, lean_object* v_whnfType_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1443_; uint8_t v_whnfType_boxed_1444_; lean_object* v_res_1445_; 
v_cleanupAnnotations_boxed_1443_ = lean_unbox(v_cleanupAnnotations_1436_);
v_whnfType_boxed_1444_ = lean_unbox(v_whnfType_1437_);
v_res_1445_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1432_, v_type_1433_, v_maxFVars_x3f_1434_, v_k_1435_, v_cleanupAnnotations_boxed_1443_, v_whnfType_boxed_1444_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1446_, lean_object* v_us_1447_, lean_object* v_params_1448_, lean_object* v_args1_1449_, uint8_t v_useEq_1450_, lean_object* v_args2_1451_, lean_object* v_args2New_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1458_ = l_Lean_mkConst(v_name_1446_, v_us_1447_);
v___x_1459_ = l_Lean_mkAppN(v___x_1458_, v_params_1448_);
lean_inc_ref(v___x_1459_);
v___x_1460_ = l_Lean_mkAppN(v___x_1459_, v_args1_1449_);
v___x_1461_ = l_Lean_mkAppN(v___x_1459_, v_args2_1451_);
v___x_1462_ = l_Lean_Meta_mkEq(v___x_1460_, v___x_1461_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; uint8_t v___x_1464_; lean_object* v_result_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___x_1511_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = 1;
v___x_1511_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1449_, v_args2_1451_, v___x_1464_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1543_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1543_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1543_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1512_);
if (lean_obj_tag(v___x_1516_) == 1)
{
lean_del_object(v___x_1514_);
if (v_useEq_1450_ == 0)
{
lean_object* v_val_1517_; lean_object* v___x_1518_; 
v_val_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = l_Lean_mkArrow(v_a_1463_, v_val_1517_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v___x_1518_);
v_result_1466_ = v_a_1519_;
v___y_1467_ = v___y_1453_;
v___y_1468_ = v___y_1454_;
v___y_1469_ = v___y_1455_;
v___y_1470_ = v___y_1456_;
goto v___jp_1465_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_a_1520_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1518_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
else
{
lean_object* v_val_1528_; lean_object* v___x_1529_; 
v_val_1528_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1528_);
lean_dec_ref(v___x_1516_);
v___x_1529_ = l_Lean_Meta_mkEq(v_a_1463_, v_val_1528_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v_result_1466_ = v_a_1530_;
v___y_1467_ = v___y_1453_;
v___y_1468_ = v___y_1454_;
v___y_1469_ = v___y_1455_;
v___y_1470_ = v___y_1456_;
goto v___jp_1465_;
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
v_a_1531_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1529_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1529_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
lean_dec(v___x_1516_);
lean_dec(v_a_1463_);
v___x_1539_ = lean_box(0);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1539_);
v___x_1541_ = v___x_1514_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_a_1463_);
v_a_1544_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1511_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1511_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
v___jp_1465_:
{
uint8_t v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = 0;
v___x_1472_ = 1;
v___x_1473_ = l_Lean_Meta_mkForallFVars(v_args2New_1452_, v_result_1466_, v___x_1471_, v___x_1464_, v___x_1464_, v___x_1472_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1473_);
v___x_1475_ = l_Lean_Meta_mkForallFVars(v_args1_1449_, v_a_1474_, v___x_1471_, v___x_1464_, v___x_1464_, v___x_1472_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1475_);
v___x_1477_ = l_Lean_Meta_mkForallFVars(v_params_1448_, v_a_1476_, v___x_1471_, v___x_1464_, v___x_1464_, v___x_1472_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1477_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1477_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1475_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1475_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1473_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1473_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v_args2_1451_);
v_a_1552_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1462_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1462_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1560_, lean_object* v_us_1561_, lean_object* v_params_1562_, lean_object* v_args1_1563_, lean_object* v_useEq_1564_, lean_object* v_args2_1565_, lean_object* v_args2New_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v_useEq_boxed_1572_; lean_object* v_res_1573_; 
v_useEq_boxed_1572_ = lean_unbox(v_useEq_1564_);
v_res_1573_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1560_, v_us_1561_, v_params_1562_, v_args1_1563_, v_useEq_boxed_1572_, v_args2_1565_, v_args2New_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_args2New_1566_);
lean_dec_ref(v_args1_1563_);
lean_dec_ref(v_params_1562_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1574_, size_t v_i_1575_, lean_object* v_bs_1576_){
_start:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_usize_dec_lt(v_i_1575_, v_sz_1574_);
if (v___x_1577_ == 0)
{
return v_bs_1576_;
}
else
{
lean_object* v_v_1578_; lean_object* v___x_1579_; lean_object* v_bs_x27_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; size_t v___x_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v_v_1578_ = lean_array_uget(v_bs_1576_, v_i_1575_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v_bs_x27_1580_ = lean_array_uset(v_bs_1576_, v_i_1575_, v___x_1579_);
v___x_1581_ = l_Lean_Expr_fvarId_x21(v_v_1578_);
lean_dec(v_v_1578_);
v___x_1582_ = 1;
v___x_1583_ = lean_box(v___x_1582_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1581_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = ((size_t)1ULL);
v___x_1586_ = lean_usize_add(v_i_1575_, v___x_1585_);
v___x_1587_ = lean_array_uset(v_bs_x27_1580_, v_i_1575_, v___x_1584_);
v_i_1575_ = v___x_1586_;
v_bs_1576_ = v___x_1587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1589_, lean_object* v_i_1590_, lean_object* v_bs_1591_){
_start:
{
size_t v_sz_boxed_1592_; size_t v_i_boxed_1593_; lean_object* v_res_1594_; 
v_sz_boxed_1592_ = lean_unbox_usize(v_sz_1589_);
lean_dec(v_sz_1589_);
v_i_boxed_1593_ = lean_unbox_usize(v_i_1590_);
lean_dec(v_i_1590_);
v_res_1594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1592_, v_i_boxed_1593_, v_bs_1591_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1595_, lean_object* v_k_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1595_, v_k_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1602_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1602_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1619_, lean_object* v_k_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1619_, v_k_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v_bs_1619_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1627_, lean_object* v_k_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
size_t v_sz_1634_; size_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_sz_1634_ = lean_array_size(v_bs_1627_);
v___x_1635_ = ((size_t)0ULL);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1634_, v___x_1635_, v_bs_1627_);
v___x_1637_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1636_, v_k_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec_ref(v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1638_, lean_object* v_k_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1638_, v_k_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1646_, lean_object* v_us_1647_, lean_object* v_params_1648_, uint8_t v_useEq_1649_, lean_object* v_ctorVal_1650_, lean_object* v_type_1651_, lean_object* v_args1_1652_, lean_object* v_resultType_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v___f_1660_; 
v___x_1659_ = lean_box(v_useEq_1649_);
lean_inc_ref(v_args1_1652_);
lean_inc_ref(v_params_1648_);
v___f_1660_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1660_, 0, v_name_1646_);
lean_closure_set(v___f_1660_, 1, v_us_1647_);
lean_closure_set(v___f_1660_, 2, v_params_1648_);
lean_closure_set(v___f_1660_, 3, v_args1_1652_);
lean_closure_set(v___f_1660_, 4, v___x_1659_);
if (v_useEq_1649_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1661_ = l_Array_append___redArg(v_params_1648_, v_args1_1652_);
v___x_1662_ = lean_unsigned_to_nat(0u);
v___x_1663_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1664_ = lean_box(v_useEq_1649_);
v___x_1665_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1665_, 0, v_ctorVal_1650_);
lean_closure_set(v___x_1665_, 1, v___x_1664_);
lean_closure_set(v___x_1665_, 2, v_args1_1652_);
lean_closure_set(v___x_1665_, 3, v_resultType_1653_);
lean_closure_set(v___x_1665_, 4, v___f_1660_);
lean_closure_set(v___x_1665_, 5, v___x_1662_);
lean_closure_set(v___x_1665_, 6, v_type_1651_);
lean_closure_set(v___x_1665_, 7, v___x_1663_);
lean_closure_set(v___x_1665_, 8, v___x_1663_);
v___x_1666_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1661_, v___x_1665_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1666_;
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v_params_1648_);
v___x_1667_ = lean_unsigned_to_nat(0u);
v___x_1668_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1669_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1650_, v_useEq_1649_, v_args1_1652_, v_resultType_1653_, v___f_1660_, v___x_1667_, v_type_1651_, v___x_1668_, v___x_1668_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1670_, lean_object* v_us_1671_, lean_object* v_params_1672_, lean_object* v_useEq_1673_, lean_object* v_ctorVal_1674_, lean_object* v_type_1675_, lean_object* v_args1_1676_, lean_object* v_resultType_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_useEq_boxed_1683_; lean_object* v_res_1684_; 
v_useEq_boxed_1683_ = lean_unbox(v_useEq_1673_);
v_res_1684_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1670_, v_us_1671_, v_params_1672_, v_useEq_boxed_1683_, v_ctorVal_1674_, v_type_1675_, v_args1_1676_, v_resultType_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1685_, lean_object* v_us_1686_, uint8_t v_useEq_1687_, lean_object* v_ctorVal_1688_, lean_object* v_params_1689_, lean_object* v_type_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; lean_object* v___f_1697_; uint8_t v___x_1698_; lean_object* v___x_1699_; 
v___x_1696_ = lean_box(v_useEq_1687_);
lean_inc_ref(v_type_1690_);
v___f_1697_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1697_, 0, v_name_1685_);
lean_closure_set(v___f_1697_, 1, v_us_1686_);
lean_closure_set(v___f_1697_, 2, v_params_1689_);
lean_closure_set(v___f_1697_, 3, v___x_1696_);
lean_closure_set(v___f_1697_, 4, v_ctorVal_1688_);
lean_closure_set(v___f_1697_, 5, v_type_1690_);
v___x_1698_ = 0;
v___x_1699_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1690_, v___f_1697_, v___x_1698_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1700_, lean_object* v_us_1701_, lean_object* v_useEq_1702_, lean_object* v_ctorVal_1703_, lean_object* v_params_1704_, lean_object* v_type_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
uint8_t v_useEq_boxed_1711_; lean_object* v_res_1712_; 
v_useEq_boxed_1711_ = lean_unbox(v_useEq_1702_);
v_res_1712_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1700_, v_us_1701_, v_useEq_boxed_1711_, v_ctorVal_1703_, v_params_1704_, v_type_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
if (lean_obj_tag(v_a_1713_) == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = l_List_reverse___redArg(v_a_1714_);
return v___x_1715_;
}
else
{
lean_object* v_head_1716_; lean_object* v_tail_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1726_; 
v_head_1716_ = lean_ctor_get(v_a_1713_, 0);
v_tail_1717_ = lean_ctor_get(v_a_1713_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_a_1713_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1719_ = v_a_1713_;
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_tail_1717_);
lean_inc(v_head_1716_);
lean_dec(v_a_1713_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = l_Lean_mkLevelParam(v_head_1716_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v_a_1714_);
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_a_1714_);
v___x_1723_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
v_a_1713_ = v_tail_1717_;
v_a_1714_ = v___x_1723_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1727_, uint8_t v_useEq_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_toConstantVal_1734_; lean_object* v_numParams_1735_; lean_object* v_name_1736_; lean_object* v_levelParams_1737_; lean_object* v_type_1738_; lean_object* v___x_1739_; 
v_toConstantVal_1734_ = lean_ctor_get(v_ctorVal_1727_, 0);
v_numParams_1735_ = lean_ctor_get(v_ctorVal_1727_, 3);
lean_inc(v_numParams_1735_);
v_name_1736_ = lean_ctor_get(v_toConstantVal_1734_, 0);
lean_inc(v_name_1736_);
v_levelParams_1737_ = lean_ctor_get(v_toConstantVal_1734_, 1);
v_type_1738_ = lean_ctor_get(v_toConstantVal_1734_, 2);
lean_inc_ref(v_type_1738_);
v___x_1739_ = l_Lean_Meta_elimOptParam(v_type_1738_, v_a_1731_, v_a_1732_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v_us_1742_; lean_object* v___x_1743_; lean_object* v___f_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = lean_box(0);
lean_inc(v_levelParams_1737_);
v_us_1742_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1737_, v___x_1741_);
v___x_1743_ = lean_box(v_useEq_1728_);
v___f_1744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1744_, 0, v_name_1736_);
lean_closure_set(v___f_1744_, 1, v_us_1742_);
lean_closure_set(v___f_1744_, 2, v___x_1743_);
lean_closure_set(v___f_1744_, 3, v_ctorVal_1727_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_numParams_1735_);
v___x_1746_ = 0;
v___x_1747_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1740_, v___x_1745_, v___f_1744_, v___x_1746_, v___x_1746_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
return v___x_1747_;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_name_1736_);
lean_dec(v_numParams_1735_);
lean_dec_ref(v_ctorVal_1727_);
v_a_1748_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1739_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1739_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1756_, lean_object* v_useEq_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
uint8_t v_useEq_boxed_1763_; lean_object* v_res_1764_; 
v_useEq_boxed_1763_ = lean_unbox(v_useEq_1757_);
v_res_1764_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1756_, v_useEq_boxed_1763_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1765_, lean_object* v_bs_1766_, lean_object* v_k_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1766_, v_k_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_bs_1775_, lean_object* v_k_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1774_, v_bs_1775_, v_k_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v_bs_1775_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1783_, lean_object* v_bs_1784_, lean_object* v_k_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1784_, v_k_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1792_, lean_object* v_bs_1793_, lean_object* v_k_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1792_, v_bs_1793_, v_k_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
uint8_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = 0;
v___x_1808_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1801_, v___x_1807_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
return v_res_1815_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1822_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1823_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1824_ = l_Lean_MessageData_ofName(v_ctorName_1822_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1828_, lean_object* v_mvarId_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1835_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1828_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_mvarId_1829_);
v___x_1837_ = l_Lean_indentD(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1835_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1838_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1840_, lean_object* v_mvarId_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1840_, v_mvarId_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1848_, lean_object* v_ctorName_1849_, lean_object* v_mvarId_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1849_, v_mvarId_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1857_, lean_object* v_ctorName_1858_, lean_object* v_mvarId_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1857_, v_ctorName_1858_, v_mvarId_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1866_, lean_object* v_as_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
if (lean_obj_tag(v_as_1867_) == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec(v_ctorName_1866_);
v___x_1873_ = lean_box(0);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
else
{
lean_object* v_head_1875_; lean_object* v_tail_1876_; lean_object* v___x_1877_; 
v_head_1875_ = lean_ctor_get(v_as_1867_, 0);
lean_inc_n(v_head_1875_, 2);
v_tail_1876_ = lean_ctor_get(v_as_1867_, 1);
lean_inc(v_tail_1876_);
lean_dec_ref(v_as_1867_);
v___x_1877_ = l_Lean_MVarId_assumptionCore(v_head_1875_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; uint8_t v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = lean_unbox(v_a_1878_);
lean_dec(v_a_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_dec(v_tail_1876_);
v___x_1880_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1866_, v_head_1875_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
return v___x_1880_;
}
else
{
lean_dec(v_head_1875_);
v_as_1867_ = v_tail_1876_;
goto _start;
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_tail_1876_);
lean_dec(v_head_1875_);
lean_dec(v_ctorName_1866_);
v_a_1882_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1877_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1877_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1890_, lean_object* v_as_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1890_, v_as_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1898_, lean_object* v_ctorName_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_MVarId_splitAndCore(v_mvarId_1898_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1899_, v_a_1906_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
return v___x_1907_;
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_ctorName_1899_);
v_a_1908_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1905_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1905_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1916_, lean_object* v_ctorName_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1916_, v_ctorName_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___f_1931_; lean_object* v___x_1015__overap_1932_; lean_object* v___x_1933_; 
v___f_1931_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_1015__overap_1932_ = lean_panic_fn_borrowed(v___f_1931_, v_msg_1925_);
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1926_);
v___x_1933_ = lean_apply_5(v___x_1015__overap_1932_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, lean_box(0));
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1940_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1941_; double v___x_1942_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_float_of_nat(v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1946_, lean_object* v_msg_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_ref_1953_; lean_object* v___x_1954_; lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1999_; 
v_ref_1953_ = lean_ctor_get(v___y_1950_, 5);
v___x_1954_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1999_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1999_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v_traceState_1960_; lean_object* v_env_1961_; lean_object* v_nextMacroScope_1962_; lean_object* v_ngen_1963_; lean_object* v_auxDeclNGen_1964_; lean_object* v_cache_1965_; lean_object* v_messages_1966_; lean_object* v_infoState_1967_; lean_object* v_snapshotTasks_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1998_; 
v___x_1959_ = lean_st_ref_take(v___y_1951_);
v_traceState_1960_ = lean_ctor_get(v___x_1959_, 4);
v_env_1961_ = lean_ctor_get(v___x_1959_, 0);
v_nextMacroScope_1962_ = lean_ctor_get(v___x_1959_, 1);
v_ngen_1963_ = lean_ctor_get(v___x_1959_, 2);
v_auxDeclNGen_1964_ = lean_ctor_get(v___x_1959_, 3);
v_cache_1965_ = lean_ctor_get(v___x_1959_, 5);
v_messages_1966_ = lean_ctor_get(v___x_1959_, 6);
v_infoState_1967_ = lean_ctor_get(v___x_1959_, 7);
v_snapshotTasks_1968_ = lean_ctor_get(v___x_1959_, 8);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1970_ = v___x_1959_;
v_isShared_1971_ = v_isSharedCheck_1998_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_snapshotTasks_1968_);
lean_inc(v_infoState_1967_);
lean_inc(v_messages_1966_);
lean_inc(v_cache_1965_);
lean_inc(v_traceState_1960_);
lean_inc(v_auxDeclNGen_1964_);
lean_inc(v_ngen_1963_);
lean_inc(v_nextMacroScope_1962_);
lean_inc(v_env_1961_);
lean_dec(v___x_1959_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1998_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
uint64_t v_tid_1972_; lean_object* v_traces_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1997_; 
v_tid_1972_ = lean_ctor_get_uint64(v_traceState_1960_, sizeof(void*)*1);
v_traces_1973_ = lean_ctor_get(v_traceState_1960_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_traceState_1960_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1975_ = v_traceState_1960_;
v_isShared_1976_ = v_isSharedCheck_1997_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_traces_1973_);
lean_dec(v_traceState_1960_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1997_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; double v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1979_ = 0;
v___x_1980_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1981_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1981_, 0, v_cls_1946_);
lean_ctor_set(v___x_1981_, 1, v___x_1977_);
lean_ctor_set(v___x_1981_, 2, v___x_1980_);
lean_ctor_set_float(v___x_1981_, sizeof(void*)*3, v___x_1978_);
lean_ctor_set_float(v___x_1981_, sizeof(void*)*3 + 8, v___x_1978_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*3 + 16, v___x_1979_);
v___x_1982_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1983_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v_a_1955_);
lean_ctor_set(v___x_1983_, 2, v___x_1982_);
lean_inc(v_ref_1953_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_ref_1953_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_PersistentArray_push___redArg(v_traces_1973_, v___x_1984_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1985_);
v___x_1987_ = v___x_1975_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1985_);
lean_ctor_set_uint64(v_reuseFailAlloc_1996_, sizeof(void*)*1, v_tid_1972_);
v___x_1987_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v___x_1987_);
v___x_1989_ = v___x_1970_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_env_1961_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_nextMacroScope_1962_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_ngen_1963_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_auxDeclNGen_1964_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1995_, 5, v_cache_1965_);
lean_ctor_set(v_reuseFailAlloc_1995_, 6, v_messages_1966_);
lean_ctor_set(v_reuseFailAlloc_1995_, 7, v_infoState_1967_);
lean_ctor_set(v_reuseFailAlloc_1995_, 8, v_snapshotTasks_1968_);
v___x_1989_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1990_ = lean_st_ref_set(v___y_1951_, v___x_1989_);
v___x_1991_ = lean_box(0);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1991_);
v___x_1993_ = v___x_1957_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_2000_, lean_object* v_msg_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2000_, v_msg_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2011_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_2012_ = lean_unsigned_to_nat(30u);
v___x_2013_ = lean_unsigned_to_nat(96u);
v___x_2014_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_2016_ = l_mkPanicMessageWithDecl(v___x_2015_, v___x_2014_, v___x_2013_, v___x_2012_, v___x_2011_);
return v___x_2016_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_cls_2025_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2026_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_2027_ = l_Lean_Name_append(v___x_2026_, v_cls_2025_);
return v___x_2027_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_2030_ = l_Lean_stringToMessageData(v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2036_ = l_Lean_stringToMessageData(v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2037_, lean_object* v_mvarId_2038_, lean_object* v_h_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v_options_2065_; uint8_t v_hasTrace_2066_; 
v_options_2065_ = lean_ctor_get(v_a_2042_, 2);
v_hasTrace_2066_ = lean_ctor_get_uint8(v_options_2065_, sizeof(void*)*1);
if (v_hasTrace_2066_ == 0)
{
v___y_2046_ = v_a_2040_;
v___y_2047_ = v_a_2041_;
v___y_2048_ = v_a_2042_;
v___y_2049_ = v_a_2043_;
goto v___jp_2045_;
}
else
{
lean_object* v_inheritedTraceOptions_2067_; lean_object* v_cls_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v_inheritedTraceOptions_2067_ = lean_ctor_get(v_a_2042_, 13);
v_cls_2068_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2069_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2067_, v_options_2065_, v___x_2069_);
if (v___x_2070_ == 0)
{
v___y_2046_ = v_a_2040_;
v___y_2047_ = v_a_2041_;
v___y_2048_ = v_a_2042_;
v___y_2049_ = v_a_2043_;
goto v___jp_2045_;
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2071_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2037_);
v___x_2072_ = l_Lean_MessageData_ofName(v_ctorName_2037_);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
lean_inc(v_h_2039_);
v___x_2076_ = l_Lean_mkFVar(v_h_2039_);
v___x_2077_ = l_Lean_MessageData_ofExpr(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2075_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
lean_inc(v_mvarId_2038_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_mvarId_2038_);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2068_, v___x_2082_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_dec_ref(v___x_2083_);
v___y_2046_ = v_a_2040_;
v___y_2047_ = v_a_2041_;
v___y_2048_ = v_a_2042_;
v___y_2049_ = v_a_2043_;
goto v___jp_2045_;
}
else
{
lean_dec(v_h_2039_);
lean_dec(v_mvarId_2038_);
lean_dec(v_ctorName_2037_);
return v___x_2083_;
}
}
}
v___jp_2045_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_box(0);
v___x_2051_ = l_Lean_Meta_injection(v_mvarId_2038_, v_h_2039_, v___x_2050_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
if (lean_obj_tag(v_a_2052_) == 0)
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_dec(v_ctorName_2037_);
v___x_2053_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2054_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2053_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
return v___x_2054_;
}
else
{
lean_object* v_mvarId_2055_; lean_object* v___x_2056_; 
v_mvarId_2055_ = lean_ctor_get(v_a_2052_, 0);
lean_inc(v_mvarId_2055_);
lean_dec_ref(v_a_2052_);
v___x_2056_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2055_, v_ctorName_2037_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
return v___x_2056_;
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_ctorName_2037_);
v_a_2057_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2051_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2051_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2084_, lean_object* v_mvarId_2085_, lean_object* v_h_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2084_, v_mvarId_2085_, v_h_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2093_, lean_object* v_k_2094_, uint8_t v_cleanupAnnotations_2095_, uint8_t v_whnfType_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___f_2102_; lean_object* v___x_2103_; 
v___f_2102_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2102_, 0, v_k_2094_);
v___x_2103_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2093_, v___f_2102_, v_cleanupAnnotations_2095_, v_whnfType_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2103_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2103_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2120_, lean_object* v_k_2121_, lean_object* v_cleanupAnnotations_2122_, lean_object* v_whnfType_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2129_; uint8_t v_whnfType_boxed_2130_; lean_object* v_res_2131_; 
v_cleanupAnnotations_boxed_2129_ = lean_unbox(v_cleanupAnnotations_2122_);
v_whnfType_boxed_2130_ = lean_unbox(v_whnfType_2123_);
v_res_2131_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2120_, v_k_2121_, v_cleanupAnnotations_boxed_2129_, v_whnfType_boxed_2130_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2132_, lean_object* v_type_2133_, lean_object* v_k_2134_, uint8_t v_cleanupAnnotations_2135_, uint8_t v_whnfType_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2133_, v_k_2134_, v_cleanupAnnotations_2135_, v_whnfType_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2143_, lean_object* v_type_2144_, lean_object* v_k_2145_, lean_object* v_cleanupAnnotations_2146_, lean_object* v_whnfType_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2153_; uint8_t v_whnfType_boxed_2154_; lean_object* v_res_2155_; 
v_cleanupAnnotations_boxed_2153_ = lean_unbox(v_cleanupAnnotations_2146_);
v_whnfType_boxed_2154_ = lean_unbox(v_whnfType_2147_);
v_res_2155_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2143_, v_type_2144_, v_k_2145_, v_cleanupAnnotations_boxed_2153_, v_whnfType_boxed_2154_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2156_, lean_object* v_ctorName_2157_, lean_object* v_xs_2158_, lean_object* v_type_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2159_, v___x_2165_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v___x_2166_);
v___x_2168_ = l_Lean_Expr_mvarId_x21(v_a_2167_);
v___x_2169_ = lean_array_get_size(v_xs_2158_);
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = lean_nat_sub(v___x_2169_, v___x_2170_);
v___x_2172_ = lean_array_get_borrowed(v___x_2156_, v_xs_2158_, v___x_2171_);
lean_dec(v___x_2171_);
v___x_2173_ = l_Lean_Expr_fvarId_x21(v___x_2172_);
v___x_2174_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2157_, v___x_2168_, v___x_2173_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2174_) == 0)
{
uint8_t v___x_2175_; uint8_t v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref(v___x_2174_);
v___x_2175_ = 0;
v___x_2176_ = 1;
v___x_2177_ = 1;
v___x_2178_ = l_Lean_Meta_mkLambdaFVars(v_xs_2158_, v_a_2167_, v___x_2175_, v___x_2176_, v___x_2175_, v___x_2176_, v___x_2177_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
return v___x_2178_;
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_a_2167_);
v_a_2179_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2174_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2174_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
lean_dec(v_ctorName_2157_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2187_, lean_object* v_ctorName_2188_, lean_object* v_xs_2189_, lean_object* v_type_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2187_, v_ctorName_2188_, v_xs_2189_, v_type_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_xs_2189_);
lean_dec_ref(v___x_2187_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2197_, lean_object* v_targetType_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v___x_2204_; lean_object* v___f_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; 
v___x_2204_ = l_Lean_instInhabitedExpr;
v___f_2205_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2205_, 0, v___x_2204_);
lean_closure_set(v___f_2205_, 1, v_ctorName_2197_);
v___x_2206_ = 0;
v___x_2207_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2198_, v___f_2205_, v___x_2206_, v___x_2206_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2208_, lean_object* v_targetType_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2208_, v_targetType_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2219_){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2221_ = l_Lean_Name_append(v_ctorName_2219_, v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2222_, lean_object* v___y_2223_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = l_Lean_Expr_hasMVar(v_e_2222_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_e_2222_);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; lean_object* v_mctx_2228_; lean_object* v___x_2229_; lean_object* v_fst_2230_; lean_object* v_snd_2231_; lean_object* v___x_2232_; lean_object* v_cache_2233_; lean_object* v_zetaDeltaFVarIds_2234_; lean_object* v_postponed_2235_; lean_object* v_diag_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2245_; 
v___x_2227_ = lean_st_ref_get(v___y_2223_);
v_mctx_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc_ref(v_mctx_2228_);
lean_dec(v___x_2227_);
v___x_2229_ = l_Lean_instantiateMVarsCore(v_mctx_2228_, v_e_2222_);
v_fst_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_fst_2230_);
v_snd_2231_ = lean_ctor_get(v___x_2229_, 1);
lean_inc(v_snd_2231_);
lean_dec_ref(v___x_2229_);
v___x_2232_ = lean_st_ref_take(v___y_2223_);
v_cache_2233_ = lean_ctor_get(v___x_2232_, 1);
v_zetaDeltaFVarIds_2234_ = lean_ctor_get(v___x_2232_, 2);
v_postponed_2235_ = lean_ctor_get(v___x_2232_, 3);
v_diag_2236_ = lean_ctor_get(v___x_2232_, 4);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; 
v_unused_2246_ = lean_ctor_get(v___x_2232_, 0);
lean_dec(v_unused_2246_);
v___x_2238_ = v___x_2232_;
v_isShared_2239_ = v_isSharedCheck_2245_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_diag_2236_);
lean_inc(v_postponed_2235_);
lean_inc(v_zetaDeltaFVarIds_2234_);
lean_inc(v_cache_2233_);
lean_dec(v___x_2232_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2245_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v_snd_2231_);
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_snd_2231_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_cache_2233_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_zetaDeltaFVarIds_2234_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_postponed_2235_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_diag_2236_);
v___x_2241_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = lean_st_ref_set(v___y_2223_, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v_fst_2230_);
return v___x_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2247_, v___y_2248_);
lean_dec(v___y_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2251_, v___y_2253_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2264_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2265_ = lean_unsigned_to_nat(32u);
v___x_2266_ = lean_mk_empty_array_with_capacity(v___x_2265_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2268_ = ((size_t)5ULL);
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = lean_unsigned_to_nat(32u);
v___x_2271_ = lean_mk_empty_array_with_capacity(v___x_2270_);
v___x_2272_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2273_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___x_2271_);
lean_ctor_set(v___x_2273_, 2, v___x_2269_);
lean_ctor_set(v___x_2273_, 3, v___x_2269_);
lean_ctor_set_usize(v___x_2273_, 4, v___x_2268_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; lean_object* v_traceState_2277_; lean_object* v_traces_2278_; lean_object* v___x_2279_; lean_object* v_traceState_2280_; lean_object* v_env_2281_; lean_object* v_nextMacroScope_2282_; lean_object* v_ngen_2283_; lean_object* v_auxDeclNGen_2284_; lean_object* v_cache_2285_; lean_object* v_messages_2286_; lean_object* v_infoState_2287_; lean_object* v_snapshotTasks_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2307_; 
v___x_2276_ = lean_st_ref_get(v___y_2274_);
v_traceState_2277_ = lean_ctor_get(v___x_2276_, 4);
lean_inc_ref(v_traceState_2277_);
lean_dec(v___x_2276_);
v_traces_2278_ = lean_ctor_get(v_traceState_2277_, 0);
lean_inc_ref(v_traces_2278_);
lean_dec_ref(v_traceState_2277_);
v___x_2279_ = lean_st_ref_take(v___y_2274_);
v_traceState_2280_ = lean_ctor_get(v___x_2279_, 4);
v_env_2281_ = lean_ctor_get(v___x_2279_, 0);
v_nextMacroScope_2282_ = lean_ctor_get(v___x_2279_, 1);
v_ngen_2283_ = lean_ctor_get(v___x_2279_, 2);
v_auxDeclNGen_2284_ = lean_ctor_get(v___x_2279_, 3);
v_cache_2285_ = lean_ctor_get(v___x_2279_, 5);
v_messages_2286_ = lean_ctor_get(v___x_2279_, 6);
v_infoState_2287_ = lean_ctor_get(v___x_2279_, 7);
v_snapshotTasks_2288_ = lean_ctor_get(v___x_2279_, 8);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2290_ = v___x_2279_;
v_isShared_2291_ = v_isSharedCheck_2307_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_snapshotTasks_2288_);
lean_inc(v_infoState_2287_);
lean_inc(v_messages_2286_);
lean_inc(v_cache_2285_);
lean_inc(v_traceState_2280_);
lean_inc(v_auxDeclNGen_2284_);
lean_inc(v_ngen_2283_);
lean_inc(v_nextMacroScope_2282_);
lean_inc(v_env_2281_);
lean_dec(v___x_2279_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2307_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
uint64_t v_tid_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2305_; 
v_tid_2292_ = lean_ctor_get_uint64(v_traceState_2280_, sizeof(void*)*1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_traceState_2280_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; 
v_unused_2306_ = lean_ctor_get(v_traceState_2280_, 0);
lean_dec(v_unused_2306_);
v___x_2294_ = v_traceState_2280_;
v_isShared_2295_ = v_isSharedCheck_2305_;
goto v_resetjp_2293_;
}
else
{
lean_dec(v_traceState_2280_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2305_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2296_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2296_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2296_);
lean_ctor_set_uint64(v_reuseFailAlloc_2304_, sizeof(void*)*1, v_tid_2292_);
v___x_2298_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2300_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 4, v___x_2298_);
v___x_2300_ = v___x_2290_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_env_2281_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_nextMacroScope_2282_);
lean_ctor_set(v_reuseFailAlloc_2303_, 2, v_ngen_2283_);
lean_ctor_set(v_reuseFailAlloc_2303_, 3, v_auxDeclNGen_2284_);
lean_ctor_set(v_reuseFailAlloc_2303_, 4, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2303_, 5, v_cache_2285_);
lean_ctor_set(v_reuseFailAlloc_2303_, 6, v_messages_2286_);
lean_ctor_set(v_reuseFailAlloc_2303_, 7, v_infoState_2287_);
lean_ctor_set(v_reuseFailAlloc_2303_, 8, v_snapshotTasks_2288_);
v___x_2300_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = lean_st_ref_set(v___y_2274_, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2302_, 0, v_traces_2278_);
return v___x_2302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2308_);
lean_dec(v___y_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2314_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2322_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2323_, lean_object* v_opt_2324_){
_start:
{
lean_object* v_name_2325_; lean_object* v_defValue_2326_; lean_object* v_map_2327_; lean_object* v___x_2328_; 
v_name_2325_ = lean_ctor_get(v_opt_2324_, 0);
v_defValue_2326_ = lean_ctor_get(v_opt_2324_, 1);
v_map_2327_ = lean_ctor_get(v_opts_2323_, 0);
v___x_2328_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2327_, v_name_2325_);
if (lean_obj_tag(v___x_2328_) == 0)
{
uint8_t v___x_2329_; 
v___x_2329_ = lean_unbox(v_defValue_2326_);
return v___x_2329_;
}
else
{
lean_object* v_val_2330_; 
v_val_2330_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_val_2330_);
lean_dec_ref(v___x_2328_);
if (lean_obj_tag(v_val_2330_) == 1)
{
uint8_t v_v_2331_; 
v_v_2331_ = lean_ctor_get_uint8(v_val_2330_, 0);
lean_dec_ref(v_val_2330_);
return v_v_2331_;
}
else
{
uint8_t v___x_2332_; 
lean_dec(v_val_2330_);
v___x_2332_ = lean_unbox(v_defValue_2326_);
return v___x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2333_, lean_object* v_opt_2334_){
_start:
{
uint8_t v_res_2335_; lean_object* v_r_2336_; 
v_res_2335_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2333_, v_opt_2334_);
lean_dec_ref(v_opt_2334_);
lean_dec_ref(v_opts_2333_);
v_r_2336_ = lean_box(v_res_2335_);
return v_r_2336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2339_ = l_Lean_stringToMessageData(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2340_, lean_object* v_x_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2347_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2348_ = l_Lean_MessageData_ofName(v_name_2340_);
v___x_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2353_, lean_object* v_x_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2353_, v_x_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec_ref(v_x_2354_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2361_, lean_object* v_val_2362_, lean_object* v_name_2363_, lean_object* v_levelParams_2364_, uint8_t v___x_2365_, lean_object* v_____r_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
lean_inc_ref(v_val_2362_);
v___x_2372_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2361_, v_val_2362_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v___x_2376_; lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2389_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref(v___x_2372_);
v___x_2374_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2362_, v___y_2368_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2373_, v___y_2368_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2389_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2389_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
lean_inc(v_name_2363_);
v___x_2381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2381_, 0, v_name_2363_);
lean_ctor_set(v___x_2381_, 1, v_levelParams_2364_);
lean_ctor_set(v___x_2381_, 2, v_a_2375_);
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_name_2363_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2381_);
lean_ctor_set(v___x_2384_, 1, v_a_2377_);
lean_ctor_set(v___x_2384_, 2, v___x_2383_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set_tag(v___x_2379_, 2);
lean_ctor_set(v___x_2379_, 0, v___x_2384_);
v___x_2386_ = v___x_2379_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_addDecl(v___x_2386_, v___x_2365_, v___y_2369_, v___y_2370_);
return v___x_2387_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_levelParams_2364_);
lean_dec(v_name_2363_);
lean_dec_ref(v_val_2362_);
v_a_2390_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2372_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2372_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2398_, lean_object* v_val_2399_, lean_object* v_name_2400_, lean_object* v_levelParams_2401_, lean_object* v___x_2402_, lean_object* v_____r_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v___x_12939__boxed_2409_; lean_object* v_res_2410_; 
v___x_12939__boxed_2409_ = lean_unbox(v___x_2402_);
v_res_2410_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2398_, v_val_2399_, v_name_2400_, v_levelParams_2401_, v___x_12939__boxed_2409_, v_____r_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2411_, lean_object* v_val_2412_, lean_object* v_name_2413_, lean_object* v_levelParams_2414_, lean_object* v_____r_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; 
lean_inc_ref(v_val_2412_);
v___x_2421_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2411_, v_val_2412_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2423_; lean_object* v_a_2424_; lean_object* v___x_2425_; lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2439_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref(v___x_2421_);
v___x_2423_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2412_, v___y_2417_);
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref(v___x_2423_);
v___x_2425_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2422_, v___y_2417_);
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2439_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2439_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2435_; 
lean_inc(v_name_2413_);
v___x_2430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2430_, 0, v_name_2413_);
lean_ctor_set(v___x_2430_, 1, v_levelParams_2414_);
lean_ctor_set(v___x_2430_, 2, v_a_2424_);
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2432_, 0, v_name_2413_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2430_);
lean_ctor_set(v___x_2433_, 1, v_a_2426_);
lean_ctor_set(v___x_2433_, 2, v___x_2432_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set_tag(v___x_2428_, 2);
lean_ctor_set(v___x_2428_, 0, v___x_2433_);
v___x_2435_ = v___x_2428_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
uint8_t v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = 0;
v___x_2437_ = l_Lean_addDecl(v___x_2435_, v___x_2436_, v___y_2418_, v___y_2419_);
return v___x_2437_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_levelParams_2414_);
lean_dec(v_name_2413_);
lean_dec_ref(v_val_2412_);
v_a_2440_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2421_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2421_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2448_, lean_object* v_val_2449_, lean_object* v_name_2450_, lean_object* v_levelParams_2451_, lean_object* v_____r_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2448_, v_val_2449_, v_name_2450_, v_levelParams_2451_, v_____r_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
return v_res_2458_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_e_2459_){
_start:
{
if (lean_obj_tag(v_e_2459_) == 0)
{
uint8_t v___x_2460_; 
v___x_2460_ = 2;
return v___x_2460_;
}
else
{
uint8_t v___x_2461_; 
v___x_2461_ = 0;
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_e_2462_){
_start:
{
uint8_t v_res_2463_; lean_object* v_r_2464_; 
v_res_2463_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_e_2462_);
lean_dec_ref(v_e_2462_);
v_r_2464_ = lean_box(v_res_2463_);
return v_r_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2465_, lean_object* v_opt_2466_){
_start:
{
lean_object* v_name_2467_; lean_object* v_defValue_2468_; lean_object* v_map_2469_; lean_object* v___x_2470_; 
v_name_2467_ = lean_ctor_get(v_opt_2466_, 0);
v_defValue_2468_ = lean_ctor_get(v_opt_2466_, 1);
v_map_2469_ = lean_ctor_get(v_opts_2465_, 0);
v___x_2470_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2469_, v_name_2467_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_inc(v_defValue_2468_);
return v_defValue_2468_;
}
else
{
lean_object* v_val_2471_; 
v_val_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_val_2471_);
lean_dec_ref(v___x_2470_);
if (lean_obj_tag(v_val_2471_) == 3)
{
lean_object* v_v_2472_; 
v_v_2472_ = lean_ctor_get(v_val_2471_, 0);
lean_inc(v_v_2472_);
lean_dec_ref(v_val_2471_);
return v_v_2472_;
}
else
{
lean_dec(v_val_2471_);
lean_inc(v_defValue_2468_);
return v_defValue_2468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2473_, lean_object* v_opt_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2473_, v_opt_2474_);
lean_dec_ref(v_opt_2474_);
lean_dec_ref(v_opts_2473_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(lean_object* v_x_2476_){
_start:
{
if (lean_obj_tag(v_x_2476_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
v_a_2478_ = lean_ctor_get(v_x_2476_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_x_2476_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v_x_2476_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v_x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 1);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
v_a_2486_ = lean_ctor_get(v_x_2476_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_x_2476_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v_x_2476_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v_x_2476_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 0);
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg___boxed(lean_object* v_x_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2494_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(size_t v_sz_2497_, size_t v_i_2498_, lean_object* v_bs_2499_){
_start:
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_usize_dec_lt(v_i_2498_, v_sz_2497_);
if (v___x_2500_ == 0)
{
return v_bs_2499_;
}
else
{
lean_object* v_v_2501_; lean_object* v_msg_2502_; lean_object* v___x_2503_; lean_object* v_bs_x27_2504_; size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
v_v_2501_ = lean_array_uget_borrowed(v_bs_2499_, v_i_2498_);
v_msg_2502_ = lean_ctor_get(v_v_2501_, 1);
lean_inc_ref(v_msg_2502_);
v___x_2503_ = lean_unsigned_to_nat(0u);
v_bs_x27_2504_ = lean_array_uset(v_bs_2499_, v_i_2498_, v___x_2503_);
v___x_2505_ = ((size_t)1ULL);
v___x_2506_ = lean_usize_add(v_i_2498_, v___x_2505_);
v___x_2507_ = lean_array_uset(v_bs_x27_2504_, v_i_2498_, v_msg_2502_);
v_i_2498_ = v___x_2506_;
v_bs_2499_ = v___x_2507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2509_, lean_object* v_i_2510_, lean_object* v_bs_2511_){
_start:
{
size_t v_sz_boxed_2512_; size_t v_i_boxed_2513_; lean_object* v_res_2514_; 
v_sz_boxed_2512_ = lean_unbox_usize(v_sz_2509_);
lean_dec(v_sz_2509_);
v_i_boxed_2513_ = lean_unbox_usize(v_i_2510_);
lean_dec(v_i_2510_);
v_res_2514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_boxed_2512_, v_i_boxed_2513_, v_bs_2511_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_oldTraces_2515_, lean_object* v_data_2516_, lean_object* v_ref_2517_, lean_object* v_msg_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_fileName_2524_; lean_object* v_fileMap_2525_; lean_object* v_options_2526_; lean_object* v_currRecDepth_2527_; lean_object* v_maxRecDepth_2528_; lean_object* v_ref_2529_; lean_object* v_currNamespace_2530_; lean_object* v_openDecls_2531_; lean_object* v_initHeartbeats_2532_; lean_object* v_maxHeartbeats_2533_; lean_object* v_quotContext_2534_; lean_object* v_currMacroScope_2535_; uint8_t v_diag_2536_; lean_object* v_cancelTk_x3f_2537_; uint8_t v_suppressElabErrors_2538_; lean_object* v_inheritedTraceOptions_2539_; lean_object* v___x_2540_; lean_object* v_traceState_2541_; lean_object* v_traces_2542_; lean_object* v_ref_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; size_t v_sz_2546_; size_t v___x_2547_; lean_object* v___x_2548_; lean_object* v_msg_2549_; lean_object* v___x_2550_; lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2588_; 
v_fileName_2524_ = lean_ctor_get(v___y_2521_, 0);
v_fileMap_2525_ = lean_ctor_get(v___y_2521_, 1);
v_options_2526_ = lean_ctor_get(v___y_2521_, 2);
v_currRecDepth_2527_ = lean_ctor_get(v___y_2521_, 3);
v_maxRecDepth_2528_ = lean_ctor_get(v___y_2521_, 4);
v_ref_2529_ = lean_ctor_get(v___y_2521_, 5);
v_currNamespace_2530_ = lean_ctor_get(v___y_2521_, 6);
v_openDecls_2531_ = lean_ctor_get(v___y_2521_, 7);
v_initHeartbeats_2532_ = lean_ctor_get(v___y_2521_, 8);
v_maxHeartbeats_2533_ = lean_ctor_get(v___y_2521_, 9);
v_quotContext_2534_ = lean_ctor_get(v___y_2521_, 10);
v_currMacroScope_2535_ = lean_ctor_get(v___y_2521_, 11);
v_diag_2536_ = lean_ctor_get_uint8(v___y_2521_, sizeof(void*)*14);
v_cancelTk_x3f_2537_ = lean_ctor_get(v___y_2521_, 12);
v_suppressElabErrors_2538_ = lean_ctor_get_uint8(v___y_2521_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2539_ = lean_ctor_get(v___y_2521_, 13);
v___x_2540_ = lean_st_ref_get(v___y_2522_);
v_traceState_2541_ = lean_ctor_get(v___x_2540_, 4);
lean_inc_ref(v_traceState_2541_);
lean_dec(v___x_2540_);
v_traces_2542_ = lean_ctor_get(v_traceState_2541_, 0);
lean_inc_ref(v_traces_2542_);
lean_dec_ref(v_traceState_2541_);
v_ref_2543_ = l_Lean_replaceRef(v_ref_2517_, v_ref_2529_);
lean_inc_ref(v_inheritedTraceOptions_2539_);
lean_inc(v_cancelTk_x3f_2537_);
lean_inc(v_currMacroScope_2535_);
lean_inc(v_quotContext_2534_);
lean_inc(v_maxHeartbeats_2533_);
lean_inc(v_initHeartbeats_2532_);
lean_inc(v_openDecls_2531_);
lean_inc(v_currNamespace_2530_);
lean_inc(v_maxRecDepth_2528_);
lean_inc(v_currRecDepth_2527_);
lean_inc_ref(v_options_2526_);
lean_inc_ref(v_fileMap_2525_);
lean_inc_ref(v_fileName_2524_);
v___x_2544_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2544_, 0, v_fileName_2524_);
lean_ctor_set(v___x_2544_, 1, v_fileMap_2525_);
lean_ctor_set(v___x_2544_, 2, v_options_2526_);
lean_ctor_set(v___x_2544_, 3, v_currRecDepth_2527_);
lean_ctor_set(v___x_2544_, 4, v_maxRecDepth_2528_);
lean_ctor_set(v___x_2544_, 5, v_ref_2543_);
lean_ctor_set(v___x_2544_, 6, v_currNamespace_2530_);
lean_ctor_set(v___x_2544_, 7, v_openDecls_2531_);
lean_ctor_set(v___x_2544_, 8, v_initHeartbeats_2532_);
lean_ctor_set(v___x_2544_, 9, v_maxHeartbeats_2533_);
lean_ctor_set(v___x_2544_, 10, v_quotContext_2534_);
lean_ctor_set(v___x_2544_, 11, v_currMacroScope_2535_);
lean_ctor_set(v___x_2544_, 12, v_cancelTk_x3f_2537_);
lean_ctor_set(v___x_2544_, 13, v_inheritedTraceOptions_2539_);
lean_ctor_set_uint8(v___x_2544_, sizeof(void*)*14, v_diag_2536_);
lean_ctor_set_uint8(v___x_2544_, sizeof(void*)*14 + 1, v_suppressElabErrors_2538_);
v___x_2545_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2542_);
lean_dec_ref(v_traces_2542_);
v_sz_2546_ = lean_array_size(v___x_2545_);
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_2546_, v___x_2547_, v___x_2545_);
v_msg_2549_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2549_, 0, v_data_2516_);
lean_ctor_set(v_msg_2549_, 1, v_msg_2518_);
lean_ctor_set(v_msg_2549_, 2, v___x_2548_);
v___x_2550_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2549_, v___y_2519_, v___y_2520_, v___x_2544_, v___y_2522_);
lean_dec_ref(v___x_2544_);
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2553_ = v___x_2550_;
v_isShared_2554_ = v_isSharedCheck_2588_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2588_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v_traceState_2556_; lean_object* v_env_2557_; lean_object* v_nextMacroScope_2558_; lean_object* v_ngen_2559_; lean_object* v_auxDeclNGen_2560_; lean_object* v_cache_2561_; lean_object* v_messages_2562_; lean_object* v_infoState_2563_; lean_object* v_snapshotTasks_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2587_; 
v___x_2555_ = lean_st_ref_take(v___y_2522_);
v_traceState_2556_ = lean_ctor_get(v___x_2555_, 4);
v_env_2557_ = lean_ctor_get(v___x_2555_, 0);
v_nextMacroScope_2558_ = lean_ctor_get(v___x_2555_, 1);
v_ngen_2559_ = lean_ctor_get(v___x_2555_, 2);
v_auxDeclNGen_2560_ = lean_ctor_get(v___x_2555_, 3);
v_cache_2561_ = lean_ctor_get(v___x_2555_, 5);
v_messages_2562_ = lean_ctor_get(v___x_2555_, 6);
v_infoState_2563_ = lean_ctor_get(v___x_2555_, 7);
v_snapshotTasks_2564_ = lean_ctor_get(v___x_2555_, 8);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2566_ = v___x_2555_;
v_isShared_2567_ = v_isSharedCheck_2587_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_snapshotTasks_2564_);
lean_inc(v_infoState_2563_);
lean_inc(v_messages_2562_);
lean_inc(v_cache_2561_);
lean_inc(v_traceState_2556_);
lean_inc(v_auxDeclNGen_2560_);
lean_inc(v_ngen_2559_);
lean_inc(v_nextMacroScope_2558_);
lean_inc(v_env_2557_);
lean_dec(v___x_2555_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2587_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
uint64_t v_tid_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2585_; 
v_tid_2568_ = lean_ctor_get_uint64(v_traceState_2556_, sizeof(void*)*1);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_traceState_2556_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v_traceState_2556_, 0);
lean_dec(v_unused_2586_);
v___x_2570_ = v_traceState_2556_;
v_isShared_2571_ = v_isSharedCheck_2585_;
goto v_resetjp_2569_;
}
else
{
lean_dec(v_traceState_2556_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2585_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_ref_2517_);
lean_ctor_set(v___x_2572_, 1, v_a_2551_);
v___x_2573_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2515_, v___x_2572_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2573_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2573_);
lean_ctor_set_uint64(v_reuseFailAlloc_2584_, sizeof(void*)*1, v_tid_2568_);
v___x_2575_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 4, v___x_2575_);
v___x_2577_ = v___x_2566_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_env_2557_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_nextMacroScope_2558_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_ngen_2559_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v_auxDeclNGen_2560_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2583_, 5, v_cache_2561_);
lean_ctor_set(v_reuseFailAlloc_2583_, 6, v_messages_2562_);
lean_ctor_set(v_reuseFailAlloc_2583_, 7, v_infoState_2563_);
lean_ctor_set(v_reuseFailAlloc_2583_, 8, v_snapshotTasks_2564_);
v___x_2577_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2578_ = lean_st_ref_set(v___y_2522_, v___x_2577_);
v___x_2579_ = lean_box(0);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___x_2579_);
v___x_2581_ = v___x_2553_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_oldTraces_2589_, lean_object* v_data_2590_, lean_object* v_ref_2591_, lean_object* v_msg_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2589_, v_data_2590_, v_ref_2591_, v_msg_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
return v_res_2598_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2601_ = l_Lean_stringToMessageData(v___x_2600_);
return v___x_2601_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2));
v___x_2604_ = l_Lean_stringToMessageData(v___x_2603_);
return v___x_2604_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2605_; double v___x_2606_; 
v___x_2605_ = lean_unsigned_to_nat(1000u);
v___x_2606_ = lean_float_of_nat(v___x_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2607_, uint8_t v_collapsed_2608_, lean_object* v_tag_2609_, lean_object* v_opts_2610_, uint8_t v_clsEnabled_2611_, lean_object* v_oldTraces_2612_, lean_object* v_msg_2613_, lean_object* v_resStartStop_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_fst_2620_; lean_object* v_snd_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2711_; 
v_fst_2620_ = lean_ctor_get(v_resStartStop_2614_, 0);
v_snd_2621_ = lean_ctor_get(v_resStartStop_2614_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_resStartStop_2614_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2623_ = v_resStartStop_2614_;
v_isShared_2624_ = v_isSharedCheck_2711_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_snd_2621_);
lean_inc(v_fst_2620_);
lean_dec(v_resStartStop_2614_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2711_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v_data_2628_; lean_object* v_fst_2631_; lean_object* v_snd_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2710_; 
v_fst_2631_ = lean_ctor_get(v_snd_2621_, 0);
v_snd_2632_ = lean_ctor_get(v_snd_2621_, 1);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_snd_2621_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2634_ = v_snd_2621_;
v_isShared_2635_ = v_isSharedCheck_2710_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_snd_2632_);
lean_inc(v_fst_2631_);
lean_dec(v_snd_2621_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2710_;
goto v_resetjp_2633_;
}
v___jp_2625_:
{
lean_object* v___x_2629_; 
lean_inc(v___y_2626_);
v___x_2629_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2612_, v_data_2628_, v___y_2626_, v___y_2627_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v___x_2630_; 
lean_dec_ref(v___x_2629_);
v___x_2630_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2620_);
return v___x_2630_;
}
else
{
lean_dec(v_fst_2620_);
return v___x_2629_;
}
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; uint8_t v___x_2637_; lean_object* v___y_2639_; lean_object* v_a_2640_; uint8_t v___y_2664_; double v___y_2695_; 
v___x_2636_ = l_Lean_trace_profiler;
v___x_2637_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2610_, v___x_2636_);
if (v___x_2637_ == 0)
{
v___y_2664_ = v___x_2637_;
goto v___jp_2663_;
}
else
{
lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2701_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2610_, v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; double v___x_2704_; double v___x_2705_; double v___x_2706_; 
v___x_2702_ = l_Lean_trace_profiler_threshold;
v___x_2703_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2610_, v___x_2702_);
v___x_2704_ = lean_float_of_nat(v___x_2703_);
v___x_2705_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4);
v___x_2706_ = lean_float_div(v___x_2704_, v___x_2705_);
v___y_2695_ = v___x_2706_;
goto v___jp_2694_;
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; double v___x_2709_; 
v___x_2707_ = l_Lean_trace_profiler_threshold;
v___x_2708_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2610_, v___x_2707_);
v___x_2709_ = lean_float_of_nat(v___x_2708_);
v___y_2695_ = v___x_2709_;
goto v___jp_2694_;
}
}
v___jp_2638_:
{
uint8_t v_result_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v_result_2641_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_fst_2620_);
v___x_2642_ = l_Lean_TraceResult_toEmoji(v_result_2641_);
v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
v___x_2644_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 7);
lean_ctor_set(v___x_2634_, 1, v___x_2644_);
lean_ctor_set(v___x_2634_, 0, v___x_2643_);
v___x_2646_ = v___x_2634_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v_m_2648_; 
if (v_isShared_2624_ == 0)
{
lean_ctor_set_tag(v___x_2623_, 7);
lean_ctor_set(v___x_2623_, 1, v_a_2640_);
lean_ctor_set(v___x_2623_, 0, v___x_2646_);
v_m_2648_ = v___x_2623_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_a_2640_);
v_m_2648_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; double v___x_2651_; lean_object* v_data_2652_; 
v___x_2649_ = lean_box(v_result_2641_);
v___x_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
v___x_2651_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2609_);
lean_inc_ref(v___x_2650_);
lean_inc(v_cls_2607_);
v_data_2652_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2652_, 0, v_cls_2607_);
lean_ctor_set(v_data_2652_, 1, v___x_2650_);
lean_ctor_set(v_data_2652_, 2, v_tag_2609_);
lean_ctor_set_float(v_data_2652_, sizeof(void*)*3, v___x_2651_);
lean_ctor_set_float(v_data_2652_, sizeof(void*)*3 + 8, v___x_2651_);
lean_ctor_set_uint8(v_data_2652_, sizeof(void*)*3 + 16, v_collapsed_2608_);
if (v___x_2637_ == 0)
{
lean_dec_ref(v___x_2650_);
lean_dec(v_snd_2632_);
lean_dec(v_fst_2631_);
lean_dec_ref(v_tag_2609_);
lean_dec(v_cls_2607_);
v___y_2626_ = v___y_2639_;
v___y_2627_ = v_m_2648_;
v_data_2628_ = v_data_2652_;
goto v___jp_2625_;
}
else
{
lean_object* v_data_2653_; double v___x_2654_; double v___x_2655_; 
lean_dec_ref(v_data_2652_);
v_data_2653_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2653_, 0, v_cls_2607_);
lean_ctor_set(v_data_2653_, 1, v___x_2650_);
lean_ctor_set(v_data_2653_, 2, v_tag_2609_);
v___x_2654_ = lean_unbox_float(v_fst_2631_);
lean_dec(v_fst_2631_);
lean_ctor_set_float(v_data_2653_, sizeof(void*)*3, v___x_2654_);
v___x_2655_ = lean_unbox_float(v_snd_2632_);
lean_dec(v_snd_2632_);
lean_ctor_set_float(v_data_2653_, sizeof(void*)*3 + 8, v___x_2655_);
lean_ctor_set_uint8(v_data_2653_, sizeof(void*)*3 + 16, v_collapsed_2608_);
v___y_2626_ = v___y_2639_;
v___y_2627_ = v_m_2648_;
v_data_2628_ = v_data_2653_;
goto v___jp_2625_;
}
}
}
}
v___jp_2658_:
{
lean_object* v_ref_2659_; lean_object* v___x_2660_; 
v_ref_2659_ = lean_ctor_get(v___y_2617_, 5);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc(v___y_2616_);
lean_inc_ref(v___y_2615_);
lean_inc(v_fst_2620_);
v___x_2660_ = lean_apply_6(v_msg_2613_, v_fst_2620_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, lean_box(0));
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2660_);
v___y_2639_ = v_ref_2659_;
v_a_2640_ = v_a_2661_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2662_; 
lean_dec_ref(v___x_2660_);
v___x_2662_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3);
v___y_2639_ = v_ref_2659_;
v_a_2640_ = v___x_2662_;
goto v___jp_2638_;
}
}
v___jp_2663_:
{
if (v_clsEnabled_2611_ == 0)
{
if (v___y_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v_traceState_2666_; lean_object* v_env_2667_; lean_object* v_nextMacroScope_2668_; lean_object* v_ngen_2669_; lean_object* v_auxDeclNGen_2670_; lean_object* v_cache_2671_; lean_object* v_messages_2672_; lean_object* v_infoState_2673_; lean_object* v_snapshotTasks_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2693_; 
lean_del_object(v___x_2634_);
lean_dec(v_snd_2632_);
lean_dec(v_fst_2631_);
lean_del_object(v___x_2623_);
lean_dec_ref(v_msg_2613_);
lean_dec_ref(v_tag_2609_);
lean_dec(v_cls_2607_);
v___x_2665_ = lean_st_ref_take(v___y_2618_);
v_traceState_2666_ = lean_ctor_get(v___x_2665_, 4);
v_env_2667_ = lean_ctor_get(v___x_2665_, 0);
v_nextMacroScope_2668_ = lean_ctor_get(v___x_2665_, 1);
v_ngen_2669_ = lean_ctor_get(v___x_2665_, 2);
v_auxDeclNGen_2670_ = lean_ctor_get(v___x_2665_, 3);
v_cache_2671_ = lean_ctor_get(v___x_2665_, 5);
v_messages_2672_ = lean_ctor_get(v___x_2665_, 6);
v_infoState_2673_ = lean_ctor_get(v___x_2665_, 7);
v_snapshotTasks_2674_ = lean_ctor_get(v___x_2665_, 8);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2676_ = v___x_2665_;
v_isShared_2677_ = v_isSharedCheck_2693_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_snapshotTasks_2674_);
lean_inc(v_infoState_2673_);
lean_inc(v_messages_2672_);
lean_inc(v_cache_2671_);
lean_inc(v_traceState_2666_);
lean_inc(v_auxDeclNGen_2670_);
lean_inc(v_ngen_2669_);
lean_inc(v_nextMacroScope_2668_);
lean_inc(v_env_2667_);
lean_dec(v___x_2665_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2693_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
uint64_t v_tid_2678_; lean_object* v_traces_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2692_; 
v_tid_2678_ = lean_ctor_get_uint64(v_traceState_2666_, sizeof(void*)*1);
v_traces_2679_ = lean_ctor_get(v_traceState_2666_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_traceState_2666_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2681_ = v_traceState_2666_;
v_isShared_2682_ = v_isSharedCheck_2692_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_traces_2679_);
lean_dec(v_traceState_2666_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2692_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2683_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2612_, v_traces_2679_);
lean_dec_ref(v_traces_2679_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2683_);
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2683_);
lean_ctor_set_uint64(v_reuseFailAlloc_2691_, sizeof(void*)*1, v_tid_2678_);
v___x_2685_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2687_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 4, v___x_2685_);
v___x_2687_ = v___x_2676_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_env_2667_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_nextMacroScope_2668_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_ngen_2669_);
lean_ctor_set(v_reuseFailAlloc_2690_, 3, v_auxDeclNGen_2670_);
lean_ctor_set(v_reuseFailAlloc_2690_, 4, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2690_, 5, v_cache_2671_);
lean_ctor_set(v_reuseFailAlloc_2690_, 6, v_messages_2672_);
lean_ctor_set(v_reuseFailAlloc_2690_, 7, v_infoState_2673_);
lean_ctor_set(v_reuseFailAlloc_2690_, 8, v_snapshotTasks_2674_);
v___x_2687_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_st_ref_set(v___y_2618_, v___x_2687_);
v___x_2689_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2620_);
return v___x_2689_;
}
}
}
}
}
else
{
goto v___jp_2658_;
}
}
else
{
goto v___jp_2658_;
}
}
v___jp_2694_:
{
double v___x_2696_; double v___x_2697_; double v___x_2698_; uint8_t v___x_2699_; 
v___x_2696_ = lean_unbox_float(v_snd_2632_);
v___x_2697_ = lean_unbox_float(v_fst_2631_);
v___x_2698_ = lean_float_sub(v___x_2696_, v___x_2697_);
v___x_2699_ = lean_float_decLt(v___y_2695_, v___x_2698_);
v___y_2664_ = v___x_2699_;
goto v___jp_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2712_, lean_object* v_collapsed_2713_, lean_object* v_tag_2714_, lean_object* v_opts_2715_, lean_object* v_clsEnabled_2716_, lean_object* v_oldTraces_2717_, lean_object* v_msg_2718_, lean_object* v_resStartStop_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
uint8_t v_collapsed_boxed_2725_; uint8_t v_clsEnabled_boxed_2726_; lean_object* v_res_2727_; 
v_collapsed_boxed_2725_ = lean_unbox(v_collapsed_2713_);
v_clsEnabled_boxed_2726_ = lean_unbox(v_clsEnabled_2716_);
v_res_2727_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2712_, v_collapsed_boxed_2725_, v_tag_2714_, v_opts_2715_, v_clsEnabled_boxed_2726_, v_oldTraces_2717_, v_msg_2718_, v_resStartStop_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec_ref(v_opts_2715_);
return v_res_2727_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2728_; double v___x_2729_; 
v___x_2728_ = lean_unsigned_to_nat(1000000000u);
v___x_2729_ = lean_float_of_nat(v___x_2728_);
return v___x_2729_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2732_ = l_Lean_stringToMessageData(v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_toConstantVal_2739_; lean_object* v_options_2740_; lean_object* v_name_2741_; lean_object* v_levelParams_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2953_; 
v_toConstantVal_2739_ = lean_ctor_get(v_ctorVal_2733_, 0);
lean_inc_ref(v_toConstantVal_2739_);
v_options_2740_ = lean_ctor_get(v_a_2736_, 2);
v_name_2741_ = lean_ctor_get(v_toConstantVal_2739_, 0);
v_levelParams_2742_ = lean_ctor_get(v_toConstantVal_2739_, 1);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_toConstantVal_2739_);
if (v_isSharedCheck_2953_ == 0)
{
lean_object* v_unused_2954_; 
v_unused_2954_ = lean_ctor_get(v_toConstantVal_2739_, 2);
lean_dec(v_unused_2954_);
v___x_2744_ = v_toConstantVal_2739_;
v_isShared_2745_ = v_isSharedCheck_2953_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_levelParams_2742_);
lean_inc(v_name_2741_);
lean_dec(v_toConstantVal_2739_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2953_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v_inheritedTraceOptions_2746_; uint8_t v_hasTrace_2747_; lean_object* v_name_2748_; 
v_inheritedTraceOptions_2746_ = lean_ctor_get(v_a_2736_, 13);
v_hasTrace_2747_ = lean_ctor_get_uint8(v_options_2740_, sizeof(void*)*1);
lean_inc(v_name_2741_);
v_name_2748_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2741_);
if (v_hasTrace_2747_ == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2787_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2787_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2787_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
if (lean_obj_tag(v_a_2750_) == 1)
{
lean_object* v_val_2754_; lean_object* v___x_2755_; 
lean_del_object(v___x_2752_);
v_val_2754_ = lean_ctor_get(v_a_2750_, 0);
lean_inc_n(v_val_2754_, 2);
lean_dec_ref(v_a_2750_);
v___x_2755_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2741_, v_val_2754_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; lean_object* v_a_2758_; lean_object* v___x_2759_; lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2774_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref(v___x_2755_);
v___x_2757_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2754_, v_a_2735_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref(v___x_2757_);
v___x_2759_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2756_, v_a_2735_);
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2774_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2774_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
lean_inc(v_name_2748_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 2, v_a_2758_);
lean_ctor_set(v___x_2744_, 0, v_name_2748_);
v___x_2765_ = v___x_2744_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_name_2748_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_levelParams_2742_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_a_2758_);
v___x_2765_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2766_ = lean_box(0);
v___x_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_name_2748_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2765_);
lean_ctor_set(v___x_2768_, 1, v_a_2760_);
lean_ctor_set(v___x_2768_, 2, v___x_2767_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 2);
lean_ctor_set(v___x_2762_, 0, v___x_2768_);
v___x_2770_ = v___x_2762_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_addDecl(v___x_2770_, v_hasTrace_2747_, v_a_2736_, v_a_2737_);
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_val_2754_);
lean_dec(v_name_2748_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2742_);
v_a_2775_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2755_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2755_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
lean_dec(v_a_2750_);
lean_dec(v_name_2748_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v___x_2783_ = lean_box(0);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2783_);
v___x_2785_ = v___x_2752_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_name_2748_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v_a_2788_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2749_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2749_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
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
else
{
lean_object* v___f_2796_; lean_object* v_cls_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v_a_2804_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v_a_2816_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v_a_2821_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v_a_2832_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v_a_2847_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v_a_2852_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; 
lean_inc(v_name_2748_);
v___f_2796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2796_, 0, v_name_2748_);
v_cls_2797_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2798_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2799_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2800_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2746_, v_options_2740_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = l_Lean_trace_profiler;
v___x_2896_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2740_, v___x_2895_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; 
lean_dec_ref(v___f_2796_);
v___x_2897_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2944_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2944_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2944_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
if (lean_obj_tag(v_a_2898_) == 1)
{
lean_object* v_val_2902_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; 
lean_del_object(v___x_2900_);
v_val_2902_ = lean_ctor_get(v_a_2898_, 0);
lean_inc(v_val_2902_);
lean_dec_ref(v_a_2898_);
if (v___x_2800_ == 0)
{
v___y_2904_ = v_a_2734_;
v___y_2905_ = v_a_2735_;
v___y_2906_ = v_a_2736_;
v___y_2907_ = v_a_2737_;
goto v___jp_2903_;
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2936_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2902_);
v___x_2937_ = l_Lean_MessageData_ofExpr(v_val_2902_);
v___x_2938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2797_, v___x_2938_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_dec_ref(v___x_2939_);
v___y_2904_ = v_a_2734_;
v___y_2905_ = v_a_2735_;
v___y_2906_ = v_a_2736_;
v___y_2907_ = v_a_2737_;
goto v___jp_2903_;
}
else
{
lean_dec(v_val_2902_);
lean_dec(v_name_2748_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
return v___x_2939_;
}
}
v___jp_2903_:
{
lean_object* v___x_2908_; 
lean_inc(v_val_2902_);
v___x_2908_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2741_, v_val_2902_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2910_; lean_object* v_a_2911_; lean_object* v___x_2912_; lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2927_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref(v___x_2908_);
v___x_2910_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2902_, v___y_2905_);
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2910_);
v___x_2912_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2909_, v___y_2905_);
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_2927_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2927_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
lean_inc(v_name_2748_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 2, v_a_2911_);
lean_ctor_set(v___x_2744_, 0, v_name_2748_);
v___x_2918_ = v___x_2744_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_name_2748_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_levelParams_2742_);
lean_ctor_set(v_reuseFailAlloc_2926_, 2, v_a_2911_);
v___x_2918_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2920_, 0, v_name_2748_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2918_);
lean_ctor_set(v___x_2921_, 1, v_a_2913_);
lean_ctor_set(v___x_2921_, 2, v___x_2920_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set_tag(v___x_2915_, 2);
lean_ctor_set(v___x_2915_, 0, v___x_2921_);
v___x_2923_ = v___x_2915_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_addDecl(v___x_2923_, v___x_2896_, v___y_2906_, v___y_2907_);
return v___x_2924_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_val_2902_);
lean_dec(v_name_2748_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2742_);
v_a_2928_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2908_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2908_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_dec(v_a_2898_);
lean_dec(v_name_2748_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v___x_2940_ = lean_box(0);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2940_);
v___x_2942_ = v___x_2900_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec(v_name_2748_);
lean_del_object(v___x_2744_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v_a_2945_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2897_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2897_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_del_object(v___x_2744_);
goto v___jp_2860_;
}
}
else
{
lean_del_object(v___x_2744_);
goto v___jp_2860_;
}
v___jp_2801_:
{
lean_object* v___x_2805_; double v___x_2806_; double v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2805_ = lean_io_get_num_heartbeats();
v___x_2806_ = lean_float_of_nat(v___y_2802_);
v___x_2807_ = lean_float_of_nat(v___x_2805_);
v___x_2808_ = lean_box_float(v___x_2806_);
v___x_2809_ = lean_box_float(v___x_2807_);
v___x_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2804_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2797_, v_hasTrace_2747_, v___x_2798_, v_options_2740_, v___x_2800_, v___y_2803_, v___f_2796_, v___x_2811_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
return v___x_2812_;
}
v___jp_2813_:
{
lean_object* v___x_2817_; 
v___x_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2817_, 0, v_a_2816_);
v___y_2802_ = v___y_2814_;
v___y_2803_ = v___y_2815_;
v_a_2804_ = v___x_2817_;
goto v___jp_2801_;
}
v___jp_2818_:
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2821_);
v___y_2802_ = v___y_2819_;
v___y_2803_ = v___y_2820_;
v_a_2804_ = v___x_2822_;
goto v___jp_2801_;
}
v___jp_2823_:
{
if (lean_obj_tag(v___y_2826_) == 0)
{
lean_object* v_a_2827_; 
v_a_2827_ = lean_ctor_get(v___y_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___y_2826_);
v___y_2819_ = v___y_2824_;
v___y_2820_ = v___y_2825_;
v_a_2821_ = v_a_2827_;
goto v___jp_2818_;
}
else
{
lean_object* v_a_2828_; 
v_a_2828_ = lean_ctor_get(v___y_2826_, 0);
lean_inc(v_a_2828_);
lean_dec_ref(v___y_2826_);
v___y_2814_ = v___y_2824_;
v___y_2815_ = v___y_2825_;
v_a_2816_ = v_a_2828_;
goto v___jp_2813_;
}
}
v___jp_2829_:
{
lean_object* v___x_2833_; double v___x_2834_; double v___x_2835_; double v___x_2836_; double v___x_2837_; double v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2833_ = lean_io_mono_nanos_now();
v___x_2834_ = lean_float_of_nat(v___y_2830_);
v___x_2835_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2836_ = lean_float_div(v___x_2834_, v___x_2835_);
v___x_2837_ = lean_float_of_nat(v___x_2833_);
v___x_2838_ = lean_float_div(v___x_2837_, v___x_2835_);
v___x_2839_ = lean_box_float(v___x_2836_);
v___x_2840_ = lean_box_float(v___x_2838_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v_a_2832_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2797_, v_hasTrace_2747_, v___x_2798_, v_options_2740_, v___x_2800_, v___y_2831_, v___f_2796_, v___x_2842_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
return v___x_2843_;
}
v___jp_2844_:
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_a_2847_);
v___y_2830_ = v___y_2845_;
v___y_2831_ = v___y_2846_;
v_a_2832_ = v___x_2848_;
goto v___jp_2829_;
}
v___jp_2849_:
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_a_2852_);
v___y_2830_ = v___y_2850_;
v___y_2831_ = v___y_2851_;
v_a_2832_ = v___x_2853_;
goto v___jp_2829_;
}
v___jp_2854_:
{
if (lean_obj_tag(v___y_2857_) == 0)
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___y_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___y_2857_);
v___y_2845_ = v___y_2855_;
v___y_2846_ = v___y_2856_;
v_a_2847_ = v_a_2858_;
goto v___jp_2844_;
}
else
{
lean_object* v_a_2859_; 
v_a_2859_ = lean_ctor_get(v___y_2857_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v___y_2857_);
v___y_2850_ = v___y_2855_;
v___y_2851_ = v___y_2856_;
v_a_2852_ = v_a_2859_;
goto v___jp_2849_;
}
}
v___jp_2860_:
{
lean_object* v___x_2861_; lean_object* v_a_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2861_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2737_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2864_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2740_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_io_mono_nanos_now();
v___x_2866_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
if (lean_obj_tag(v_a_2867_) == 1)
{
if (v___x_2800_ == 0)
{
lean_object* v_val_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_val_2868_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_val_2868_);
lean_dec_ref(v_a_2867_);
v___x_2869_ = lean_box(0);
v___x_2870_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2741_, v_val_2868_, v_name_2748_, v_levelParams_2742_, v___x_2864_, v___x_2869_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
v___y_2855_ = v___x_2865_;
v___y_2856_ = v_a_2862_;
v___y_2857_ = v___x_2870_;
goto v___jp_2854_;
}
else
{
lean_object* v_val_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_val_2871_ = lean_ctor_get(v_a_2867_, 0);
lean_inc_n(v_val_2871_, 2);
lean_dec_ref(v_a_2867_);
v___x_2872_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2873_ = l_Lean_MessageData_ofExpr(v_val_2871_);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2797_, v___x_2874_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2741_, v_val_2871_, v_name_2748_, v_levelParams_2742_, v___x_2864_, v_a_2876_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
v___y_2855_ = v___x_2865_;
v___y_2856_ = v_a_2862_;
v___y_2857_ = v___x_2877_;
goto v___jp_2854_;
}
else
{
lean_dec(v_val_2871_);
lean_dec(v_name_2748_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v___y_2855_ = v___x_2865_;
v___y_2856_ = v_a_2862_;
v___y_2857_ = v___x_2875_;
goto v___jp_2854_;
}
}
}
else
{
lean_object* v___x_2878_; 
lean_dec(v_a_2867_);
lean_dec(v_name_2748_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v___x_2878_ = lean_box(0);
v___y_2845_ = v___x_2865_;
v___y_2846_ = v_a_2862_;
v_a_2847_ = v___x_2878_;
goto v___jp_2844_;
}
}
else
{
lean_object* v_a_2879_; 
lean_dec(v_name_2748_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v_a_2879_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2879_);
lean_dec_ref(v___x_2866_);
v___y_2850_ = v___x_2865_;
v___y_2851_ = v_a_2862_;
v_a_2852_ = v_a_2879_;
goto v___jp_2849_;
}
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_io_get_num_heartbeats();
v___x_2881_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref(v___x_2881_);
if (lean_obj_tag(v_a_2882_) == 1)
{
if (v___x_2800_ == 0)
{
lean_object* v_val_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_val_2883_ = lean_ctor_get(v_a_2882_, 0);
lean_inc(v_val_2883_);
lean_dec_ref(v_a_2882_);
v___x_2884_ = lean_box(0);
v___x_2885_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2741_, v_val_2883_, v_name_2748_, v_levelParams_2742_, v___x_2884_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
v___y_2824_ = v___x_2880_;
v___y_2825_ = v_a_2862_;
v___y_2826_ = v___x_2885_;
goto v___jp_2823_;
}
else
{
lean_object* v_val_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_val_2886_ = lean_ctor_get(v_a_2882_, 0);
lean_inc_n(v_val_2886_, 2);
lean_dec_ref(v_a_2882_);
v___x_2887_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2888_ = l_Lean_MessageData_ofExpr(v_val_2886_);
v___x_2889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2797_, v___x_2889_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref(v___x_2890_);
v___x_2892_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2741_, v_val_2886_, v_name_2748_, v_levelParams_2742_, v_a_2891_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
v___y_2824_ = v___x_2880_;
v___y_2825_ = v_a_2862_;
v___y_2826_ = v___x_2892_;
goto v___jp_2823_;
}
else
{
lean_dec(v_val_2886_);
lean_dec(v_name_2748_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v___y_2824_ = v___x_2880_;
v___y_2825_ = v_a_2862_;
v___y_2826_ = v___x_2890_;
goto v___jp_2823_;
}
}
}
else
{
lean_object* v___x_2893_; 
lean_dec(v_a_2882_);
lean_dec(v_name_2748_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v___x_2893_ = lean_box(0);
v___y_2819_ = v___x_2880_;
v___y_2820_ = v_a_2862_;
v_a_2821_ = v___x_2893_;
goto v___jp_2818_;
}
}
else
{
lean_object* v_a_2894_; 
lean_dec(v_name_2748_);
lean_dec(v_levelParams_2742_);
lean_dec(v_name_2741_);
v_a_2894_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2881_);
v___y_2814_ = v___x_2880_;
v___y_2815_ = v_a_2862_;
v_a_2816_ = v_a_2894_;
goto v___jp_2813_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_00_u03b1_2962_, lean_object* v_x_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2963_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2970_, lean_object* v_x_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_00_u03b1_2970_, v_x_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2983_ = l_Lean_Name_append(v_ctorName_2981_, v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
uint8_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = 1;
v___x_2991_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2984_, v___x_2990_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2999_, lean_object* v_t_3000_, lean_object* v_acc_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_3000_, v_a_3002_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3028_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3028_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3028_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3014_ = l_Lean_Expr_cleanupAnnotations(v_a_3005_);
v___x_3015_ = l_Lean_Expr_isApp(v___x_3014_);
if (v___x_3015_ == 0)
{
lean_dec_ref(v___x_3014_);
goto v___jp_3009_;
}
else
{
lean_object* v_arg_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v_arg_3016_ = lean_ctor_get(v___x_3014_, 1);
lean_inc_ref(v_arg_3016_);
v___x_3017_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3014_);
v___x_3018_ = l_Lean_Expr_isApp(v___x_3017_);
if (v___x_3018_ == 0)
{
lean_dec_ref(v___x_3017_);
lean_dec_ref(v_arg_3016_);
goto v___jp_3009_;
}
else
{
lean_object* v_arg_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v_arg_3019_ = lean_ctor_get(v___x_3017_, 1);
lean_inc_ref(v_arg_3019_);
v___x_3020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3017_);
v___x_3021_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3022_ = l_Lean_Expr_isConstOf(v___x_3020_, v___x_3021_);
lean_dec_ref(v___x_3020_);
if (v___x_3022_ == 0)
{
lean_dec_ref(v_arg_3019_);
lean_dec_ref(v_arg_3016_);
goto v___jp_3009_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_del_object(v___x_3007_);
v___x_3023_ = lean_unsigned_to_nat(0u);
v___x_3024_ = l_Lean_mkProj(v___x_3021_, v___x_3023_, v_e_2999_);
lean_inc_ref(v___x_3024_);
v___x_3025_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_3024_, v_arg_3019_, v_acc_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref(v___x_3025_);
v_e_2999_ = v___x_3024_;
v_t_3000_ = v_arg_3016_;
v_acc_3001_ = v_a_3026_;
goto _start;
}
else
{
lean_dec_ref(v___x_3024_);
lean_dec_ref(v_arg_3016_);
return v___x_3025_;
}
}
}
}
v___jp_3009_:
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3010_ = lean_array_push(v_acc_3001_, v_e_2999_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3010_);
v___x_3012_ = v___x_3007_;
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
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v_acc_3001_);
lean_dec_ref(v_e_2999_);
v_a_3029_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3004_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3004_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_3037_, lean_object* v_t_3038_, lean_object* v_acc_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3037_, v_t_3038_, v_acc_3039_, v_a_3040_);
lean_dec(v_a_3040_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_3043_, lean_object* v_t_3044_, lean_object* v_acc_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3043_, v_t_3044_, v_acc_3045_, v_a_3047_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3052_, lean_object* v_t_3053_, lean_object* v_acc_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3052_, v_t_3053_, v_acc_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v___x_3067_; 
lean_inc(v_a_3065_);
lean_inc_ref(v_a_3064_);
lean_inc(v_a_3063_);
lean_inc_ref(v_a_3062_);
lean_inc_ref(v_e_3061_);
v___x_3067_ = lean_infer_type(v_e_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
v___x_3069_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3070_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3061_, v_a_3068_, v___x_3069_, v_a_3063_);
return v___x_3070_;
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v_e_3061_);
v_a_3071_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3067_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3067_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
return v_res_3085_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = lean_box(0);
v___x_3092_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2));
v___x_3093_ = l_Lean_mkConst(v___x_3092_, v___x_3091_);
return v___x_3093_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4));
v___x_3096_ = l_Lean_stringToMessageData(v___x_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_b_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; 
lean_inc(v_b_3097_);
v___x_3103_ = l_Lean_MVarId_getType(v_b_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3184_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3184_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3184_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
if (lean_obj_tag(v_a_3104_) == 7)
{
lean_object* v_binderType_3108_; lean_object* v_body_3109_; uint8_t v___x_3110_; lean_object* v_mvarId_u2082_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; 
v_binderType_3108_ = lean_ctor_get(v_a_3104_, 1);
lean_inc_ref(v_binderType_3108_);
v_body_3109_ = lean_ctor_get(v_a_3104_, 2);
lean_inc_ref(v_body_3109_);
lean_dec_ref(v_a_3104_);
v___x_3110_ = l_Lean_Expr_hasLooseBVars(v_body_3109_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3129_; 
lean_del_object(v___x_3106_);
v___x_3129_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3108_, v___y_3099_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref(v___x_3129_);
v___x_3131_ = l_Lean_Expr_cleanupAnnotations(v_a_3130_);
v___x_3132_ = l_Lean_Expr_isApp(v___x_3131_);
if (v___x_3132_ == 0)
{
lean_dec_ref(v___x_3131_);
lean_dec_ref(v_body_3109_);
v_mvarId_u2082_3112_ = v_b_3097_;
v___y_3113_ = v___y_3098_;
v___y_3114_ = v___y_3099_;
v___y_3115_ = v___y_3100_;
v___y_3116_ = v___y_3101_;
goto v___jp_3111_;
}
else
{
lean_object* v_arg_3133_; lean_object* v___x_3134_; uint8_t v___x_3135_; 
v_arg_3133_ = lean_ctor_get(v___x_3131_, 1);
lean_inc_ref(v_arg_3133_);
v___x_3134_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3131_);
v___x_3135_ = l_Lean_Expr_isApp(v___x_3134_);
if (v___x_3135_ == 0)
{
lean_dec_ref(v___x_3134_);
lean_dec_ref(v_arg_3133_);
lean_dec_ref(v_body_3109_);
v_mvarId_u2082_3112_ = v_b_3097_;
v___y_3113_ = v___y_3098_;
v___y_3114_ = v___y_3099_;
v___y_3115_ = v___y_3100_;
v___y_3116_ = v___y_3101_;
goto v___jp_3111_;
}
else
{
lean_object* v_arg_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v_arg_3136_ = lean_ctor_get(v___x_3134_, 1);
lean_inc_ref(v_arg_3136_);
v___x_3137_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3134_);
v___x_3138_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3139_ = l_Lean_Expr_isConstOf(v___x_3137_, v___x_3138_);
lean_dec_ref(v___x_3137_);
if (v___x_3139_ == 0)
{
lean_dec_ref(v_arg_3136_);
lean_dec_ref(v_arg_3133_);
lean_dec_ref(v_body_3109_);
v_mvarId_u2082_3112_ = v_b_3097_;
v___y_3113_ = v___y_3098_;
v___y_3114_ = v___y_3099_;
v___y_3115_ = v___y_3100_;
v___y_3116_ = v___y_3101_;
goto v___jp_3111_;
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3140_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3);
v___x_3141_ = l_Lean_mkApp3(v___x_3140_, v_arg_3136_, v_arg_3133_, v_body_3109_);
v___x_3142_ = lean_unsigned_to_nat(1u);
lean_inc(v_b_3097_);
v___x_3143_ = l_Lean_MVarId_applyN(v_b_3097_, v___x_3141_, v___x_3142_, v___x_3139_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref(v___x_3143_);
if (lean_obj_tag(v_a_3144_) == 1)
{
lean_object* v_tail_3160_; 
v_tail_3160_ = lean_ctor_get(v_a_3144_, 1);
if (lean_obj_tag(v_tail_3160_) == 0)
{
lean_object* v_head_3161_; 
lean_dec(v_b_3097_);
v_head_3161_ = lean_ctor_get(v_a_3144_, 0);
lean_inc(v_head_3161_);
lean_dec_ref(v_a_3144_);
v_mvarId_u2082_3112_ = v_head_3161_;
v___y_3113_ = v___y_3098_;
v___y_3114_ = v___y_3099_;
v___y_3115_ = v___y_3100_;
v___y_3116_ = v___y_3101_;
goto v___jp_3111_;
}
else
{
lean_dec_ref(v_a_3144_);
v___y_3146_ = v___y_3098_;
v___y_3147_ = v___y_3099_;
v___y_3148_ = v___y_3100_;
v___y_3149_ = v___y_3101_;
goto v___jp_3145_;
}
}
else
{
lean_dec(v_a_3144_);
v___y_3146_ = v___y_3098_;
v___y_3147_ = v___y_3099_;
v___y_3148_ = v___y_3100_;
v___y_3149_ = v___y_3101_;
goto v___jp_3145_;
}
v___jp_3145_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5);
v___x_3151_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3150_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_dec_ref(v___x_3151_);
v_mvarId_u2082_3112_ = v_b_3097_;
v___y_3113_ = v___y_3146_;
v___y_3114_ = v___y_3147_;
v___y_3115_ = v___y_3148_;
v___y_3116_ = v___y_3149_;
goto v___jp_3111_;
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_b_3097_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_b_3097_);
v_a_3162_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3143_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3143_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref(v_body_3109_);
lean_dec(v_b_3097_);
v_a_3170_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3129_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3129_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
lean_object* v___x_3179_; 
lean_dec_ref(v_body_3109_);
lean_dec_ref(v_binderType_3108_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v_b_3097_);
v___x_3179_ = v___x_3106_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_b_3097_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
v___jp_3111_:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3112_, v___x_3110_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v_snd_3119_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref(v___x_3117_);
v_snd_3119_ = lean_ctor_get(v_a_3118_, 1);
lean_inc(v_snd_3119_);
lean_dec(v_a_3118_);
v_b_3097_ = v_snd_3119_;
goto _start;
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
v_a_3121_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3117_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3117_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
else
{
lean_object* v___x_3182_; 
lean_dec(v_a_3104_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v_b_3097_);
v___x_3182_ = v___x_3106_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_b_3097_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v_b_3097_);
v_a_3185_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3103_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3103_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_b_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_b_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3200_, lean_object* v_x_3201_, lean_object* v_x_3202_, lean_object* v_x_3203_){
_start:
{
lean_object* v_ks_3204_; lean_object* v_vs_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3229_; 
v_ks_3204_ = lean_ctor_get(v_x_3200_, 0);
v_vs_3205_ = lean_ctor_get(v_x_3200_, 1);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_x_3200_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3207_ = v_x_3200_;
v_isShared_3208_ = v_isSharedCheck_3229_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_vs_3205_);
lean_inc(v_ks_3204_);
lean_dec(v_x_3200_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3229_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; uint8_t v___x_3210_; 
v___x_3209_ = lean_array_get_size(v_ks_3204_);
v___x_3210_ = lean_nat_dec_lt(v_x_3201_, v___x_3209_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
lean_dec(v_x_3201_);
v___x_3211_ = lean_array_push(v_ks_3204_, v_x_3202_);
v___x_3212_ = lean_array_push(v_vs_3205_, v_x_3203_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3212_);
lean_ctor_set(v___x_3207_, 0, v___x_3211_);
v___x_3214_ = v___x_3207_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
else
{
lean_object* v_k_x27_3216_; uint8_t v___x_3217_; 
v_k_x27_3216_ = lean_array_fget_borrowed(v_ks_3204_, v_x_3201_);
v___x_3217_ = l_Lean_instBEqMVarId_beq(v_x_3202_, v_k_x27_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3219_; 
if (v_isShared_3208_ == 0)
{
v___x_3219_ = v___x_3207_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_ks_3204_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v_vs_3205_);
v___x_3219_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_unsigned_to_nat(1u);
v___x_3221_ = lean_nat_add(v_x_3201_, v___x_3220_);
lean_dec(v_x_3201_);
v_x_3200_ = v___x_3219_;
v_x_3201_ = v___x_3221_;
goto _start;
}
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3224_ = lean_array_fset(v_ks_3204_, v_x_3201_, v_x_3202_);
v___x_3225_ = lean_array_fset(v_vs_3205_, v_x_3201_, v_x_3203_);
lean_dec(v_x_3201_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3225_);
lean_ctor_set(v___x_3207_, 0, v___x_3224_);
v___x_3227_ = v___x_3207_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3230_, lean_object* v_k_3231_, lean_object* v_v_3232_){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3230_, v___x_3233_, v_k_3231_, v_v_3232_);
return v___x_3234_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_3235_; size_t v___x_3236_; size_t v___x_3237_; 
v___x_3235_ = ((size_t)5ULL);
v___x_3236_ = ((size_t)1ULL);
v___x_3237_ = lean_usize_shift_left(v___x_3236_, v___x_3235_);
return v___x_3237_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_3238_; size_t v___x_3239_; size_t v___x_3240_; 
v___x_3238_ = ((size_t)1ULL);
v___x_3239_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3240_ = lean_usize_sub(v___x_3239_, v___x_3238_);
return v___x_3240_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3242_, size_t v_x_3243_, size_t v_x_3244_, lean_object* v_x_3245_, lean_object* v_x_3246_){
_start:
{
if (lean_obj_tag(v_x_3242_) == 0)
{
lean_object* v_es_3247_; size_t v___x_3248_; size_t v___x_3249_; size_t v___x_3250_; size_t v___x_3251_; lean_object* v_j_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v_es_3247_ = lean_ctor_get(v_x_3242_, 0);
v___x_3248_ = ((size_t)5ULL);
v___x_3249_ = ((size_t)1ULL);
v___x_3250_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3251_ = lean_usize_land(v_x_3243_, v___x_3250_);
v_j_3252_ = lean_usize_to_nat(v___x_3251_);
v___x_3253_ = lean_array_get_size(v_es_3247_);
v___x_3254_ = lean_nat_dec_lt(v_j_3252_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_dec(v_j_3252_);
lean_dec(v_x_3246_);
lean_dec(v_x_3245_);
return v_x_3242_;
}
else
{
lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3291_; 
lean_inc_ref(v_es_3247_);
v_isSharedCheck_3291_ = !lean_is_exclusive(v_x_3242_);
if (v_isSharedCheck_3291_ == 0)
{
lean_object* v_unused_3292_; 
v_unused_3292_ = lean_ctor_get(v_x_3242_, 0);
lean_dec(v_unused_3292_);
v___x_3256_ = v_x_3242_;
v_isShared_3257_ = v_isSharedCheck_3291_;
goto v_resetjp_3255_;
}
else
{
lean_dec(v_x_3242_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3291_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v_v_3258_; lean_object* v___x_3259_; lean_object* v_xs_x27_3260_; lean_object* v___y_3262_; 
v_v_3258_ = lean_array_fget(v_es_3247_, v_j_3252_);
v___x_3259_ = lean_box(0);
v_xs_x27_3260_ = lean_array_fset(v_es_3247_, v_j_3252_, v___x_3259_);
switch(lean_obj_tag(v_v_3258_))
{
case 0:
{
lean_object* v_key_3267_; lean_object* v_val_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3278_; 
v_key_3267_ = lean_ctor_get(v_v_3258_, 0);
v_val_3268_ = lean_ctor_get(v_v_3258_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_v_3258_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3270_ = v_v_3258_;
v_isShared_3271_ = v_isSharedCheck_3278_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_val_3268_);
lean_inc(v_key_3267_);
lean_dec(v_v_3258_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3278_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
uint8_t v___x_3272_; 
v___x_3272_ = l_Lean_instBEqMVarId_beq(v_x_3245_, v_key_3267_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_del_object(v___x_3270_);
v___x_3273_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3267_, v_val_3268_, v_x_3245_, v_x_3246_);
v___x_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
v___y_3262_ = v___x_3274_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3276_; 
lean_dec(v_val_3268_);
lean_dec(v_key_3267_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 1, v_x_3246_);
lean_ctor_set(v___x_3270_, 0, v_x_3245_);
v___x_3276_ = v___x_3270_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_x_3245_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_x_3246_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
v___y_3262_ = v___x_3276_;
goto v___jp_3261_;
}
}
}
}
case 1:
{
lean_object* v_node_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3289_; 
v_node_3279_ = lean_ctor_get(v_v_3258_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_v_3258_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3281_ = v_v_3258_;
v_isShared_3282_ = v_isSharedCheck_3289_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_node_3279_);
lean_dec(v_v_3258_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3289_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
size_t v___x_3283_; size_t v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3283_ = lean_usize_shift_right(v_x_3243_, v___x_3248_);
v___x_3284_ = lean_usize_add(v_x_3244_, v___x_3249_);
v___x_3285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3279_, v___x_3283_, v___x_3284_, v_x_3245_, v_x_3246_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v___x_3285_);
v___x_3287_ = v___x_3281_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
v___y_3262_ = v___x_3287_;
goto v___jp_3261_;
}
}
}
default: 
{
lean_object* v___x_3290_; 
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_x_3245_);
lean_ctor_set(v___x_3290_, 1, v_x_3246_);
v___y_3262_ = v___x_3290_;
goto v___jp_3261_;
}
}
v___jp_3261_:
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
v___x_3263_ = lean_array_fset(v_xs_x27_3260_, v_j_3252_, v___y_3262_);
lean_dec(v_j_3252_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3263_);
v___x_3265_ = v___x_3256_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
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
}
else
{
lean_object* v_ks_3293_; lean_object* v_vs_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3314_; 
v_ks_3293_ = lean_ctor_get(v_x_3242_, 0);
v_vs_3294_ = lean_ctor_get(v_x_3242_, 1);
v_isSharedCheck_3314_ = !lean_is_exclusive(v_x_3242_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3296_ = v_x_3242_;
v_isShared_3297_ = v_isSharedCheck_3314_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_vs_3294_);
lean_inc(v_ks_3293_);
lean_dec(v_x_3242_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3314_;
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
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_ks_3293_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_vs_3294_);
v___x_3299_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v_newNode_3300_; uint8_t v___y_3302_; size_t v___x_3308_; uint8_t v___x_3309_; 
v_newNode_3300_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3299_, v_x_3245_, v_x_3246_);
v___x_3308_ = ((size_t)7ULL);
v___x_3309_ = lean_usize_dec_le(v___x_3308_, v_x_3244_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3310_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3300_);
v___x_3311_ = lean_unsigned_to_nat(4u);
v___x_3312_ = lean_nat_dec_lt(v___x_3310_, v___x_3311_);
lean_dec(v___x_3310_);
v___y_3302_ = v___x_3312_;
goto v___jp_3301_;
}
else
{
v___y_3302_ = v___x_3309_;
goto v___jp_3301_;
}
v___jp_3301_:
{
if (v___y_3302_ == 0)
{
lean_object* v_ks_3303_; lean_object* v_vs_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_ks_3303_ = lean_ctor_get(v_newNode_3300_, 0);
lean_inc_ref(v_ks_3303_);
v_vs_3304_ = lean_ctor_get(v_newNode_3300_, 1);
lean_inc_ref(v_vs_3304_);
lean_dec_ref(v_newNode_3300_);
v___x_3305_ = lean_unsigned_to_nat(0u);
v___x_3306_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_3307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3244_, v_ks_3303_, v_vs_3304_, v___x_3305_, v___x_3306_);
lean_dec_ref(v_vs_3304_);
lean_dec_ref(v_ks_3303_);
return v___x_3307_;
}
else
{
return v_newNode_3300_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3315_, lean_object* v_keys_3316_, lean_object* v_vals_3317_, lean_object* v_i_3318_, lean_object* v_entries_3319_){
_start:
{
lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = lean_array_get_size(v_keys_3316_);
v___x_3321_ = lean_nat_dec_lt(v_i_3318_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_dec(v_i_3318_);
return v_entries_3319_;
}
else
{
lean_object* v_k_3322_; lean_object* v_v_3323_; uint64_t v___x_3324_; size_t v_h_3325_; size_t v___x_3326_; lean_object* v___x_3327_; size_t v___x_3328_; size_t v___x_3329_; size_t v___x_3330_; size_t v_h_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_k_3322_ = lean_array_fget_borrowed(v_keys_3316_, v_i_3318_);
v_v_3323_ = lean_array_fget_borrowed(v_vals_3317_, v_i_3318_);
v___x_3324_ = l_Lean_instHashableMVarId_hash(v_k_3322_);
v_h_3325_ = lean_uint64_to_usize(v___x_3324_);
v___x_3326_ = ((size_t)5ULL);
v___x_3327_ = lean_unsigned_to_nat(1u);
v___x_3328_ = ((size_t)1ULL);
v___x_3329_ = lean_usize_sub(v_depth_3315_, v___x_3328_);
v___x_3330_ = lean_usize_mul(v___x_3326_, v___x_3329_);
v_h_3331_ = lean_usize_shift_right(v_h_3325_, v___x_3330_);
v___x_3332_ = lean_nat_add(v_i_3318_, v___x_3327_);
lean_dec(v_i_3318_);
lean_inc(v_v_3323_);
lean_inc(v_k_3322_);
v___x_3333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3319_, v_h_3331_, v_depth_3315_, v_k_3322_, v_v_3323_);
v_i_3318_ = v___x_3332_;
v_entries_3319_ = v___x_3333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3335_, lean_object* v_keys_3336_, lean_object* v_vals_3337_, lean_object* v_i_3338_, lean_object* v_entries_3339_){
_start:
{
size_t v_depth_boxed_3340_; lean_object* v_res_3341_; 
v_depth_boxed_3340_ = lean_unbox_usize(v_depth_3335_);
lean_dec(v_depth_3335_);
v_res_3341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3340_, v_keys_3336_, v_vals_3337_, v_i_3338_, v_entries_3339_);
lean_dec_ref(v_vals_3337_);
lean_dec_ref(v_keys_3336_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3342_, lean_object* v_x_3343_, lean_object* v_x_3344_, lean_object* v_x_3345_, lean_object* v_x_3346_){
_start:
{
size_t v_x_5084__boxed_3347_; size_t v_x_5085__boxed_3348_; lean_object* v_res_3349_; 
v_x_5084__boxed_3347_ = lean_unbox_usize(v_x_3343_);
lean_dec(v_x_3343_);
v_x_5085__boxed_3348_ = lean_unbox_usize(v_x_3344_);
lean_dec(v_x_3344_);
v_res_3349_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3342_, v_x_5084__boxed_3347_, v_x_5085__boxed_3348_, v_x_3345_, v_x_3346_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_){
_start:
{
uint64_t v___x_3353_; size_t v___x_3354_; size_t v___x_3355_; lean_object* v___x_3356_; 
v___x_3353_ = l_Lean_instHashableMVarId_hash(v_x_3351_);
v___x_3354_ = lean_uint64_to_usize(v___x_3353_);
v___x_3355_ = ((size_t)1ULL);
v___x_3356_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3350_, v___x_3354_, v___x_3355_, v_x_3351_, v_x_3352_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3357_, lean_object* v_val_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; lean_object* v_mctx_3362_; lean_object* v_cache_3363_; lean_object* v_zetaDeltaFVarIds_3364_; lean_object* v_postponed_3365_; lean_object* v_diag_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3394_; 
v___x_3361_ = lean_st_ref_take(v___y_3359_);
v_mctx_3362_ = lean_ctor_get(v___x_3361_, 0);
v_cache_3363_ = lean_ctor_get(v___x_3361_, 1);
v_zetaDeltaFVarIds_3364_ = lean_ctor_get(v___x_3361_, 2);
v_postponed_3365_ = lean_ctor_get(v___x_3361_, 3);
v_diag_3366_ = lean_ctor_get(v___x_3361_, 4);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3368_ = v___x_3361_;
v_isShared_3369_ = v_isSharedCheck_3394_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_diag_3366_);
lean_inc(v_postponed_3365_);
lean_inc(v_zetaDeltaFVarIds_3364_);
lean_inc(v_cache_3363_);
lean_inc(v_mctx_3362_);
lean_dec(v___x_3361_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3394_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_depth_3370_; lean_object* v_levelAssignDepth_3371_; lean_object* v_lmvarCounter_3372_; lean_object* v_mvarCounter_3373_; lean_object* v_lDecls_3374_; lean_object* v_decls_3375_; lean_object* v_userNames_3376_; lean_object* v_lAssignment_3377_; lean_object* v_eAssignment_3378_; lean_object* v_dAssignment_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3393_; 
v_depth_3370_ = lean_ctor_get(v_mctx_3362_, 0);
v_levelAssignDepth_3371_ = lean_ctor_get(v_mctx_3362_, 1);
v_lmvarCounter_3372_ = lean_ctor_get(v_mctx_3362_, 2);
v_mvarCounter_3373_ = lean_ctor_get(v_mctx_3362_, 3);
v_lDecls_3374_ = lean_ctor_get(v_mctx_3362_, 4);
v_decls_3375_ = lean_ctor_get(v_mctx_3362_, 5);
v_userNames_3376_ = lean_ctor_get(v_mctx_3362_, 6);
v_lAssignment_3377_ = lean_ctor_get(v_mctx_3362_, 7);
v_eAssignment_3378_ = lean_ctor_get(v_mctx_3362_, 8);
v_dAssignment_3379_ = lean_ctor_get(v_mctx_3362_, 9);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_mctx_3362_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3381_ = v_mctx_3362_;
v_isShared_3382_ = v_isSharedCheck_3393_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_dAssignment_3379_);
lean_inc(v_eAssignment_3378_);
lean_inc(v_lAssignment_3377_);
lean_inc(v_userNames_3376_);
lean_inc(v_decls_3375_);
lean_inc(v_lDecls_3374_);
lean_inc(v_mvarCounter_3373_);
lean_inc(v_lmvarCounter_3372_);
lean_inc(v_levelAssignDepth_3371_);
lean_inc(v_depth_3370_);
lean_dec(v_mctx_3362_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3393_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3383_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3378_, v_mvarId_3357_, v_val_3358_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 8, v___x_3383_);
v___x_3385_ = v___x_3381_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_depth_3370_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_levelAssignDepth_3371_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_lmvarCounter_3372_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_mvarCounter_3373_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_lDecls_3374_);
lean_ctor_set(v_reuseFailAlloc_3392_, 5, v_decls_3375_);
lean_ctor_set(v_reuseFailAlloc_3392_, 6, v_userNames_3376_);
lean_ctor_set(v_reuseFailAlloc_3392_, 7, v_lAssignment_3377_);
lean_ctor_set(v_reuseFailAlloc_3392_, 8, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3392_, 9, v_dAssignment_3379_);
v___x_3385_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3387_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v___x_3385_);
v___x_3387_ = v___x_3368_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_cache_3363_);
lean_ctor_set(v_reuseFailAlloc_3391_, 2, v_zetaDeltaFVarIds_3364_);
lean_ctor_set(v_reuseFailAlloc_3391_, 3, v_postponed_3365_);
lean_ctor_set(v_reuseFailAlloc_3391_, 4, v_diag_3366_);
v___x_3387_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = lean_st_ref_set(v___y_3359_, v___x_3387_);
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3395_, lean_object* v_val_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3395_, v_val_3396_, v___y_3397_);
lean_dec(v___y_3397_);
return v_res_3399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3405_ = lean_box(0);
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3407_ = l_Lean_mkConst(v___x_3406_, v___x_3405_);
return v___x_3407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3415_, lean_object* v_xs_3416_, lean_object* v_type_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_box(0);
v___x_3424_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3417_, v___x_3423_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; uint8_t v___x_3430_; lean_object* v___y_3432_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref(v___x_3424_);
v___x_3426_ = l_Lean_Expr_mvarId_x21(v_a_3425_);
v___x_3427_ = lean_box(0);
v___x_3428_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3429_ = 1;
v___x_3430_ = 0;
v___x_3443_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3444_ = lean_box(0);
v___x_3445_ = l_Lean_MVarId_apply(v___x_3426_, v___x_3428_, v___x_3443_, v___x_3444_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref(v___x_3445_);
if (lean_obj_tag(v_a_3446_) == 1)
{
lean_object* v_tail_3460_; 
v_tail_3460_ = lean_ctor_get(v_a_3446_, 1);
lean_inc(v_tail_3460_);
if (lean_obj_tag(v_tail_3460_) == 1)
{
lean_object* v_tail_3461_; 
v_tail_3461_ = lean_ctor_get(v_tail_3460_, 1);
if (lean_obj_tag(v_tail_3461_) == 0)
{
lean_object* v_toConstantVal_3462_; lean_object* v_head_3463_; lean_object* v_head_3464_; lean_object* v_name_3465_; lean_object* v_levelParams_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v_toConstantVal_3462_ = lean_ctor_get(v_ctorVal_3415_, 0);
lean_inc_ref(v_toConstantVal_3462_);
lean_dec_ref(v_ctorVal_3415_);
v_head_3463_ = lean_ctor_get(v_a_3446_, 0);
lean_inc(v_head_3463_);
lean_dec_ref(v_a_3446_);
v_head_3464_ = lean_ctor_get(v_tail_3460_, 0);
lean_inc(v_head_3464_);
lean_dec_ref(v_tail_3460_);
v_name_3465_ = lean_ctor_get(v_toConstantVal_3462_, 0);
lean_inc_n(v_name_3465_, 2);
v_levelParams_3466_ = lean_ctor_get(v_toConstantVal_3462_, 1);
lean_inc(v_levelParams_3466_);
lean_dec_ref(v_toConstantVal_3462_);
v___x_3467_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3465_);
v___x_3468_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3466_, v___x_3427_);
v___x_3469_ = l_Lean_mkConst(v___x_3467_, v___x_3468_);
v___x_3470_ = l_Lean_mkAppN(v___x_3469_, v_xs_3416_);
v___x_3471_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3463_, v___x_3470_, v___y_3419_);
lean_dec_ref(v___x_3471_);
v___x_3472_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_head_3464_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3474_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref(v___x_3472_);
v___x_3474_ = l_Lean_MVarId_refl(v_a_3473_, v___x_3429_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_dec(v_name_3465_);
v___y_3432_ = v___x_3474_;
goto v___jp_3431_;
}
else
{
lean_object* v_a_3475_; uint8_t v___y_3477_; uint8_t v___x_3480_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
v___x_3480_ = l_Lean_Exception_isInterrupt(v_a_3475_);
if (v___x_3480_ == 0)
{
uint8_t v___x_3481_; 
v___x_3481_ = l_Lean_Exception_isRuntime(v_a_3475_);
v___y_3477_ = v___x_3481_;
goto v___jp_3476_;
}
else
{
lean_dec(v_a_3475_);
v___y_3477_ = v___x_3480_;
goto v___jp_3476_;
}
v___jp_3476_:
{
if (v___y_3477_ == 0)
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_dec_ref(v___x_3474_);
v___x_3478_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3465_);
v___x_3479_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3478_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
v___y_3432_ = v___x_3479_;
goto v___jp_3431_;
}
else
{
lean_dec(v_name_3465_);
v___y_3432_ = v___x_3474_;
goto v___jp_3431_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec(v_name_3465_);
lean_dec(v_a_3425_);
v_a_3482_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3472_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3472_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_dec_ref(v_tail_3460_);
lean_dec_ref(v_a_3446_);
lean_dec(v_a_3425_);
v___y_3448_ = v___y_3418_;
v___y_3449_ = v___y_3419_;
v___y_3450_ = v___y_3420_;
v___y_3451_ = v___y_3421_;
goto v___jp_3447_;
}
}
else
{
lean_dec_ref(v_a_3446_);
lean_dec(v_tail_3460_);
lean_dec(v_a_3425_);
v___y_3448_ = v___y_3418_;
v___y_3449_ = v___y_3419_;
v___y_3450_ = v___y_3420_;
v___y_3451_ = v___y_3421_;
goto v___jp_3447_;
}
}
else
{
lean_dec(v_a_3446_);
lean_dec(v_a_3425_);
v___y_3448_ = v___y_3418_;
v___y_3449_ = v___y_3419_;
v___y_3450_ = v___y_3420_;
v___y_3451_ = v___y_3421_;
goto v___jp_3447_;
}
v___jp_3447_:
{
lean_object* v_toConstantVal_3452_; lean_object* v_name_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_toConstantVal_3452_ = lean_ctor_get(v_ctorVal_3415_, 0);
lean_inc_ref(v_toConstantVal_3452_);
lean_dec_ref(v_ctorVal_3415_);
v_name_3453_ = lean_ctor_get(v_toConstantVal_3452_, 0);
lean_inc(v_name_3453_);
lean_dec_ref(v_toConstantVal_3452_);
v___x_3454_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3455_ = l_Lean_MessageData_ofName(v_name_3453_);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3458_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
return v___x_3459_;
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec(v_a_3425_);
lean_dec_ref(v_ctorVal_3415_);
v_a_3490_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3445_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3445_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
v___jp_3431_:
{
if (lean_obj_tag(v___y_3432_) == 0)
{
uint8_t v___x_3433_; lean_object* v___x_3434_; 
lean_dec_ref(v___y_3432_);
v___x_3433_ = 1;
v___x_3434_ = l_Lean_Meta_mkLambdaFVars(v_xs_3416_, v_a_3425_, v___x_3430_, v___x_3429_, v___x_3430_, v___x_3429_, v___x_3433_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
return v___x_3434_;
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec(v_a_3425_);
v_a_3435_ = lean_ctor_get(v___y_3432_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___y_3432_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___y_3432_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___y_3432_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorVal_3415_);
return v___x_3424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3498_, lean_object* v_xs_3499_, lean_object* v_type_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3498_, v_xs_3499_, v_type_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v_xs_3499_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3507_, lean_object* v_targetType_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_){
_start:
{
lean_object* v___f_3514_; uint8_t v___x_3515_; lean_object* v___x_3516_; 
v___f_3514_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3514_, 0, v_ctorVal_3507_);
v___x_3515_ = 0;
v___x_3516_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3508_, v___f_3514_, v___x_3515_, v___x_3515_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3517_, lean_object* v_targetType_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3517_, v_targetType_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3525_, lean_object* v_val_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3525_, v_val_3526_, v___y_3528_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3533_, lean_object* v_val_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3533_, v_val_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3541_, lean_object* v_x_3542_, lean_object* v_x_3543_, lean_object* v_x_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3542_, v_x_3543_, v_x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3546_, lean_object* v_x_3547_, size_t v_x_3548_, size_t v_x_3549_, lean_object* v_x_3550_, lean_object* v_x_3551_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3547_, v_x_3548_, v_x_3549_, v_x_3550_, v_x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3553_, lean_object* v_x_3554_, lean_object* v_x_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_, lean_object* v_x_3558_){
_start:
{
size_t v_x_5548__boxed_3559_; size_t v_x_5549__boxed_3560_; lean_object* v_res_3561_; 
v_x_5548__boxed_3559_ = lean_unbox_usize(v_x_3555_);
lean_dec(v_x_3555_);
v_x_5549__boxed_3560_ = lean_unbox_usize(v_x_3556_);
lean_dec(v_x_3556_);
v_res_3561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3553_, v_x_3554_, v_x_5548__boxed_3559_, v_x_5549__boxed_3560_, v_x_3557_, v_x_3558_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3562_, lean_object* v_n_3563_, lean_object* v_k_3564_, lean_object* v_v_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3563_, v_k_3564_, v_v_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3567_, size_t v_depth_3568_, lean_object* v_keys_3569_, lean_object* v_vals_3570_, lean_object* v_heq_3571_, lean_object* v_i_3572_, lean_object* v_entries_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3568_, v_keys_3569_, v_vals_3570_, v_i_3572_, v_entries_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3575_, lean_object* v_depth_3576_, lean_object* v_keys_3577_, lean_object* v_vals_3578_, lean_object* v_heq_3579_, lean_object* v_i_3580_, lean_object* v_entries_3581_){
_start:
{
size_t v_depth_boxed_3582_; lean_object* v_res_3583_; 
v_depth_boxed_3582_ = lean_unbox_usize(v_depth_3576_);
lean_dec(v_depth_3576_);
v_res_3583_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3575_, v_depth_boxed_3582_, v_keys_3577_, v_vals_3578_, v_heq_3579_, v_i_3580_, v_entries_3581_);
lean_dec_ref(v_vals_3578_);
lean_dec_ref(v_keys_3577_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3585_, v_x_3586_, v_x_3587_, v_x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3590_, lean_object* v_val_3591_, lean_object* v_name_3592_, lean_object* v_levelParams_3593_, uint8_t v___x_3594_, uint8_t v_hasTrace_3595_, lean_object* v_____r_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; 
lean_inc_ref(v_val_3591_);
v___x_3602_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3590_, v_val_3591_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3604_; lean_object* v_a_3605_; lean_object* v___x_3606_; lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3623_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref(v___x_3602_);
v___x_3604_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3591_, v___y_3598_);
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v___x_3604_);
v___x_3606_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3603_, v___y_3598_);
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3623_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3623_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3616_; 
lean_inc_n(v_name_3592_, 2);
v___x_3611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3611_, 0, v_name_3592_);
lean_ctor_set(v___x_3611_, 1, v_levelParams_3593_);
lean_ctor_set(v___x_3611_, 2, v_a_3605_);
v___x_3612_ = lean_box(0);
v___x_3613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3613_, 0, v_name_3592_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3611_);
lean_ctor_set(v___x_3614_, 1, v_a_3607_);
lean_ctor_set(v___x_3614_, 2, v___x_3613_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 2);
lean_ctor_set(v___x_3609_, 0, v___x_3614_);
v___x_3616_ = v___x_3609_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Lean_addDecl(v___x_3616_, v___x_3594_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
lean_dec_ref(v___x_3617_);
v___x_3618_ = l_Lean_Meta_simpExtension;
v___x_3619_ = 0;
v___x_3620_ = lean_unsigned_to_nat(1000u);
v___x_3621_ = l_Lean_Meta_addSimpTheorem(v___x_3618_, v_name_3592_, v_hasTrace_3595_, v___x_3594_, v___x_3619_, v___x_3620_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v___x_3621_;
}
else
{
lean_dec(v_name_3592_);
return v___x_3617_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v_levelParams_3593_);
lean_dec(v_name_3592_);
lean_dec_ref(v_val_3591_);
v_a_3624_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3602_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3602_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3632_, lean_object* v_val_3633_, lean_object* v_name_3634_, lean_object* v_levelParams_3635_, lean_object* v___x_3636_, lean_object* v_hasTrace_3637_, lean_object* v_____r_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
uint8_t v___x_9095__boxed_3644_; uint8_t v_hasTrace_boxed_3645_; lean_object* v_res_3646_; 
v___x_9095__boxed_3644_ = lean_unbox(v___x_3636_);
v_hasTrace_boxed_3645_ = lean_unbox(v_hasTrace_3637_);
v_res_3646_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3632_, v_val_3633_, v_name_3634_, v_levelParams_3635_, v___x_9095__boxed_3644_, v_hasTrace_boxed_3645_, v_____r_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3647_, lean_object* v_val_3648_, lean_object* v_name_3649_, lean_object* v_levelParams_3650_, uint8_t v___x_3651_, lean_object* v_____r_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v___x_3658_; 
lean_inc_ref(v_val_3648_);
v___x_3658_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3647_, v_val_3648_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3660_; lean_object* v_a_3661_; lean_object* v___x_3662_; lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3680_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref(v___x_3658_);
v___x_3660_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3648_, v___y_3654_);
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v___x_3660_);
v___x_3662_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3659_, v___y_3654_);
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3680_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3680_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
lean_inc_n(v_name_3649_, 2);
v___x_3667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3667_, 0, v_name_3649_);
lean_ctor_set(v___x_3667_, 1, v_levelParams_3650_);
lean_ctor_set(v___x_3667_, 2, v_a_3661_);
v___x_3668_ = lean_box(0);
v___x_3669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3669_, 0, v_name_3649_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3667_);
lean_ctor_set(v___x_3670_, 1, v_a_3663_);
lean_ctor_set(v___x_3670_, 2, v___x_3669_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set_tag(v___x_3665_, 2);
lean_ctor_set(v___x_3665_, 0, v___x_3670_);
v___x_3672_ = v___x_3665_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
uint8_t v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = 0;
v___x_3674_ = l_Lean_addDecl(v___x_3672_, v___x_3673_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v___x_3675_; uint8_t v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
lean_dec_ref(v___x_3674_);
v___x_3675_ = l_Lean_Meta_simpExtension;
v___x_3676_ = 0;
v___x_3677_ = lean_unsigned_to_nat(1000u);
v___x_3678_ = l_Lean_Meta_addSimpTheorem(v___x_3675_, v_name_3649_, v___x_3651_, v___x_3673_, v___x_3676_, v___x_3677_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
return v___x_3678_;
}
else
{
lean_dec(v_name_3649_);
return v___x_3674_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec(v_levelParams_3650_);
lean_dec(v_name_3649_);
lean_dec_ref(v_val_3648_);
v_a_3681_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3658_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3658_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3689_, lean_object* v_val_3690_, lean_object* v_name_3691_, lean_object* v_levelParams_3692_, lean_object* v___x_3693_, lean_object* v_____r_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
uint8_t v___x_9183__boxed_3700_; lean_object* v_res_3701_; 
v___x_9183__boxed_3700_ = lean_unbox(v___x_3693_);
v_res_3701_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3689_, v_val_3690_, v_name_3691_, v_levelParams_3692_, v___x_9183__boxed_3700_, v_____r_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v_toConstantVal_3708_; lean_object* v_options_3709_; lean_object* v_name_3710_; lean_object* v_levelParams_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3931_; 
v_toConstantVal_3708_ = lean_ctor_get(v_ctorVal_3702_, 0);
lean_inc_ref(v_toConstantVal_3708_);
v_options_3709_ = lean_ctor_get(v_a_3705_, 2);
v_name_3710_ = lean_ctor_get(v_toConstantVal_3708_, 0);
v_levelParams_3711_ = lean_ctor_get(v_toConstantVal_3708_, 1);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_toConstantVal_3708_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; 
v_unused_3932_ = lean_ctor_get(v_toConstantVal_3708_, 2);
lean_dec(v_unused_3932_);
v___x_3713_ = v_toConstantVal_3708_;
v_isShared_3714_ = v_isSharedCheck_3931_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_levelParams_3711_);
lean_inc(v_name_3710_);
lean_dec(v_toConstantVal_3708_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3931_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v_inheritedTraceOptions_3715_; uint8_t v_hasTrace_3716_; lean_object* v_name_3717_; 
v_inheritedTraceOptions_3715_ = lean_ctor_get(v_a_3705_, 13);
v_hasTrace_3716_ = lean_ctor_get_uint8(v_options_3709_, sizeof(void*)*1);
v_name_3717_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3710_);
if (v_hasTrace_3716_ == 0)
{
lean_object* v___x_3718_; 
lean_inc_ref(v_ctorVal_3702_);
v___x_3718_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3761_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3721_ = v___x_3718_;
v_isShared_3722_ = v_isSharedCheck_3761_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3718_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3761_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
if (lean_obj_tag(v_a_3719_) == 1)
{
lean_object* v_val_3723_; lean_object* v___x_3724_; 
lean_del_object(v___x_3721_);
v_val_3723_ = lean_ctor_get(v_a_3719_, 0);
lean_inc_n(v_val_3723_, 2);
lean_dec_ref(v_a_3719_);
v___x_3724_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3702_, v_val_3723_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v_a_3727_; lean_object* v___x_3728_; lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3748_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref(v___x_3724_);
v___x_3726_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3723_, v_a_3704_);
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref(v___x_3726_);
v___x_3728_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3725_, v_a_3704_);
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3731_ = v___x_3728_;
v_isShared_3732_ = v_isSharedCheck_3748_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3728_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3748_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
lean_inc(v_name_3717_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 2, v_a_3727_);
lean_ctor_set(v___x_3713_, 0, v_name_3717_);
v___x_3734_ = v___x_3713_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_name_3717_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_levelParams_3711_);
lean_ctor_set(v_reuseFailAlloc_3747_, 2, v_a_3727_);
v___x_3734_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
v___x_3735_ = lean_box(0);
lean_inc(v_name_3717_);
v___x_3736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3736_, 0, v_name_3717_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3734_);
lean_ctor_set(v___x_3737_, 1, v_a_3729_);
lean_ctor_set(v___x_3737_, 2, v___x_3736_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set_tag(v___x_3731_, 2);
lean_ctor_set(v___x_3731_, 0, v___x_3737_);
v___x_3739_ = v___x_3731_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_addDecl(v___x_3739_, v_hasTrace_3716_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v___x_3741_; uint8_t v___x_3742_; uint8_t v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_dec_ref(v___x_3740_);
v___x_3741_ = l_Lean_Meta_simpExtension;
v___x_3742_ = 1;
v___x_3743_ = 0;
v___x_3744_ = lean_unsigned_to_nat(1000u);
v___x_3745_ = l_Lean_Meta_addSimpTheorem(v___x_3741_, v_name_3717_, v___x_3742_, v_hasTrace_3716_, v___x_3743_, v___x_3744_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
return v___x_3745_;
}
else
{
lean_dec(v_name_3717_);
return v___x_3740_;
}
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec(v_val_3723_);
lean_dec(v_name_3717_);
lean_del_object(v___x_3713_);
lean_dec(v_levelParams_3711_);
v_a_3749_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3724_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3724_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3759_; 
lean_dec(v_a_3719_);
lean_dec(v_name_3717_);
lean_del_object(v___x_3713_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v___x_3757_ = lean_box(0);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3757_);
v___x_3759_ = v___x_3721_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec(v_name_3717_);
lean_del_object(v___x_3713_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v_a_3762_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3718_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3718_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_object* v___f_3770_; lean_object* v_cls_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v_a_3778_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v_a_3790_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v_a_3795_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v_a_3806_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v_a_3821_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v_a_3826_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; 
lean_inc(v_name_3717_);
v___f_3770_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3770_, 0, v_name_3717_);
v_cls_3771_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3772_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3773_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3774_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3715_, v_options_3709_, v___x_3773_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3869_ = l_Lean_trace_profiler;
v___x_3870_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3709_, v___x_3869_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
lean_dec_ref(v___f_3770_);
lean_inc_ref(v_ctorVal_3702_);
v___x_3871_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3922_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3922_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3922_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
if (lean_obj_tag(v_a_3872_) == 1)
{
lean_object* v_val_3876_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; 
lean_del_object(v___x_3874_);
v_val_3876_ = lean_ctor_get(v_a_3872_, 0);
lean_inc(v_val_3876_);
lean_dec_ref(v_a_3872_);
if (v___x_3774_ == 0)
{
v___y_3878_ = v_a_3703_;
v___y_3879_ = v_a_3704_;
v___y_3880_ = v_a_3705_;
v___y_3881_ = v_a_3706_;
goto v___jp_3877_;
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3914_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3876_);
v___x_3915_ = l_Lean_MessageData_ofExpr(v_val_3876_);
v___x_3916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3914_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3771_, v___x_3916_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_dec_ref(v___x_3917_);
v___y_3878_ = v_a_3703_;
v___y_3879_ = v_a_3704_;
v___y_3880_ = v_a_3705_;
v___y_3881_ = v_a_3706_;
goto v___jp_3877_;
}
else
{
lean_dec(v_val_3876_);
lean_dec(v_name_3717_);
lean_del_object(v___x_3713_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
return v___x_3917_;
}
}
v___jp_3877_:
{
lean_object* v___x_3882_; 
lean_inc(v_val_3876_);
v___x_3882_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3702_, v_val_3876_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; lean_object* v_a_3885_; lean_object* v___x_3886_; lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3905_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref(v___x_3882_);
v___x_3884_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3876_, v___y_3879_);
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref(v___x_3884_);
v___x_3886_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3883_, v___y_3879_);
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3889_ = v___x_3886_;
v_isShared_3890_ = v_isSharedCheck_3905_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3905_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
lean_inc(v_name_3717_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 2, v_a_3885_);
lean_ctor_set(v___x_3713_, 0, v_name_3717_);
v___x_3892_ = v___x_3713_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_name_3717_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_levelParams_3711_);
lean_ctor_set(v_reuseFailAlloc_3904_, 2, v_a_3885_);
v___x_3892_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3893_ = lean_box(0);
lean_inc(v_name_3717_);
v___x_3894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3894_, 0, v_name_3717_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3892_);
lean_ctor_set(v___x_3895_, 1, v_a_3887_);
lean_ctor_set(v___x_3895_, 2, v___x_3894_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set_tag(v___x_3889_, 2);
lean_ctor_set(v___x_3889_, 0, v___x_3895_);
v___x_3897_ = v___x_3889_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Lean_addDecl(v___x_3897_, v___x_3870_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v___x_3899_; uint8_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
lean_dec_ref(v___x_3898_);
v___x_3899_ = l_Lean_Meta_simpExtension;
v___x_3900_ = 0;
v___x_3901_ = lean_unsigned_to_nat(1000u);
v___x_3902_ = l_Lean_Meta_addSimpTheorem(v___x_3899_, v_name_3717_, v_hasTrace_3716_, v___x_3870_, v___x_3900_, v___x_3901_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
return v___x_3902_;
}
else
{
lean_dec(v_name_3717_);
return v___x_3898_;
}
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v_val_3876_);
lean_dec(v_name_3717_);
lean_del_object(v___x_3713_);
lean_dec(v_levelParams_3711_);
v_a_3906_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3882_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3882_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3920_; 
lean_dec(v_a_3872_);
lean_dec(v_name_3717_);
lean_del_object(v___x_3713_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v___x_3918_ = lean_box(0);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v___x_3918_);
v___x_3920_ = v___x_3874_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3918_);
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
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v_name_3717_);
lean_del_object(v___x_3713_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v_a_3923_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3871_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3871_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_del_object(v___x_3713_);
goto v___jp_3834_;
}
}
else
{
lean_del_object(v___x_3713_);
goto v___jp_3834_;
}
v___jp_3775_:
{
lean_object* v___x_3779_; double v___x_3780_; double v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3779_ = lean_io_get_num_heartbeats();
v___x_3780_ = lean_float_of_nat(v___y_3777_);
v___x_3781_ = lean_float_of_nat(v___x_3779_);
v___x_3782_ = lean_box_float(v___x_3780_);
v___x_3783_ = lean_box_float(v___x_3781_);
v___x_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3785_, 0, v_a_3778_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3771_, v_hasTrace_3716_, v___x_3772_, v_options_3709_, v___x_3774_, v___y_3776_, v___f_3770_, v___x_3785_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
return v___x_3786_;
}
v___jp_3787_:
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3791_, 0, v_a_3790_);
v___y_3776_ = v___y_3788_;
v___y_3777_ = v___y_3789_;
v_a_3778_ = v___x_3791_;
goto v___jp_3775_;
}
v___jp_3792_:
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3796_, 0, v_a_3795_);
v___y_3776_ = v___y_3793_;
v___y_3777_ = v___y_3794_;
v_a_3778_ = v___x_3796_;
goto v___jp_3775_;
}
v___jp_3797_:
{
if (lean_obj_tag(v___y_3800_) == 0)
{
lean_object* v_a_3801_; 
v_a_3801_ = lean_ctor_get(v___y_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref(v___y_3800_);
v___y_3793_ = v___y_3798_;
v___y_3794_ = v___y_3799_;
v_a_3795_ = v_a_3801_;
goto v___jp_3792_;
}
else
{
lean_object* v_a_3802_; 
v_a_3802_ = lean_ctor_get(v___y_3800_, 0);
lean_inc(v_a_3802_);
lean_dec_ref(v___y_3800_);
v___y_3788_ = v___y_3798_;
v___y_3789_ = v___y_3799_;
v_a_3790_ = v_a_3802_;
goto v___jp_3787_;
}
}
v___jp_3803_:
{
lean_object* v___x_3807_; double v___x_3808_; double v___x_3809_; double v___x_3810_; double v___x_3811_; double v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3807_ = lean_io_mono_nanos_now();
v___x_3808_ = lean_float_of_nat(v___y_3804_);
v___x_3809_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3810_ = lean_float_div(v___x_3808_, v___x_3809_);
v___x_3811_ = lean_float_of_nat(v___x_3807_);
v___x_3812_ = lean_float_div(v___x_3811_, v___x_3809_);
v___x_3813_ = lean_box_float(v___x_3810_);
v___x_3814_ = lean_box_float(v___x_3812_);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3816_, 0, v_a_3806_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3771_, v_hasTrace_3716_, v___x_3772_, v_options_3709_, v___x_3774_, v___y_3805_, v___f_3770_, v___x_3816_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
return v___x_3817_;
}
v___jp_3818_:
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3822_, 0, v_a_3821_);
v___y_3804_ = v___y_3819_;
v___y_3805_ = v___y_3820_;
v_a_3806_ = v___x_3822_;
goto v___jp_3803_;
}
v___jp_3823_:
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3827_, 0, v_a_3826_);
v___y_3804_ = v___y_3824_;
v___y_3805_ = v___y_3825_;
v_a_3806_ = v___x_3827_;
goto v___jp_3803_;
}
v___jp_3828_:
{
if (lean_obj_tag(v___y_3831_) == 0)
{
lean_object* v_a_3832_; 
v_a_3832_ = lean_ctor_get(v___y_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref(v___y_3831_);
v___y_3819_ = v___y_3829_;
v___y_3820_ = v___y_3830_;
v_a_3821_ = v_a_3832_;
goto v___jp_3818_;
}
else
{
lean_object* v_a_3833_; 
v_a_3833_ = lean_ctor_get(v___y_3831_, 0);
lean_inc(v_a_3833_);
lean_dec_ref(v___y_3831_);
v___y_3824_ = v___y_3829_;
v___y_3825_ = v___y_3830_;
v_a_3826_ = v_a_3833_;
goto v___jp_3823_;
}
}
v___jp_3834_:
{
lean_object* v___x_3835_; lean_object* v_a_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3835_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3706_);
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref(v___x_3835_);
v___x_3837_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3838_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3709_, v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3702_);
v___x_3840_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref(v___x_3840_);
if (lean_obj_tag(v_a_3841_) == 1)
{
if (v___x_3774_ == 0)
{
lean_object* v_val_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v_val_3842_ = lean_ctor_get(v_a_3841_, 0);
lean_inc(v_val_3842_);
lean_dec_ref(v_a_3841_);
v___x_3843_ = lean_box(0);
v___x_3844_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3702_, v_val_3842_, v_name_3717_, v_levelParams_3711_, v___x_3838_, v_hasTrace_3716_, v___x_3843_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
v___y_3829_ = v___x_3839_;
v___y_3830_ = v_a_3836_;
v___y_3831_ = v___x_3844_;
goto v___jp_3828_;
}
else
{
lean_object* v_val_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_val_3845_ = lean_ctor_get(v_a_3841_, 0);
lean_inc_n(v_val_3845_, 2);
lean_dec_ref(v_a_3841_);
v___x_3846_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3847_ = l_Lean_MessageData_ofExpr(v_val_3845_);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3771_, v___x_3848_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref(v___x_3849_);
v___x_3851_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3702_, v_val_3845_, v_name_3717_, v_levelParams_3711_, v___x_3838_, v_hasTrace_3716_, v_a_3850_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
v___y_3829_ = v___x_3839_;
v___y_3830_ = v_a_3836_;
v___y_3831_ = v___x_3851_;
goto v___jp_3828_;
}
else
{
lean_dec(v_val_3845_);
lean_dec(v_name_3717_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v___y_3829_ = v___x_3839_;
v___y_3830_ = v_a_3836_;
v___y_3831_ = v___x_3849_;
goto v___jp_3828_;
}
}
}
else
{
lean_object* v___x_3852_; 
lean_dec(v_a_3841_);
lean_dec(v_name_3717_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v___x_3852_ = lean_box(0);
v___y_3819_ = v___x_3839_;
v___y_3820_ = v_a_3836_;
v_a_3821_ = v___x_3852_;
goto v___jp_3818_;
}
}
else
{
lean_object* v_a_3853_; 
lean_dec(v_name_3717_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v_a_3853_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3853_);
lean_dec_ref(v___x_3840_);
v___y_3824_ = v___x_3839_;
v___y_3825_ = v_a_3836_;
v_a_3826_ = v_a_3853_;
goto v___jp_3823_;
}
}
else
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3702_);
v___x_3855_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref(v___x_3855_);
if (lean_obj_tag(v_a_3856_) == 1)
{
if (v___x_3774_ == 0)
{
lean_object* v_val_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v_val_3857_ = lean_ctor_get(v_a_3856_, 0);
lean_inc(v_val_3857_);
lean_dec_ref(v_a_3856_);
v___x_3858_ = lean_box(0);
v___x_3859_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3702_, v_val_3857_, v_name_3717_, v_levelParams_3711_, v___x_3838_, v___x_3858_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
v___y_3798_ = v_a_3836_;
v___y_3799_ = v___x_3854_;
v___y_3800_ = v___x_3859_;
goto v___jp_3797_;
}
else
{
lean_object* v_val_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v_val_3860_ = lean_ctor_get(v_a_3856_, 0);
lean_inc_n(v_val_3860_, 2);
lean_dec_ref(v_a_3856_);
v___x_3861_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3862_ = l_Lean_MessageData_ofExpr(v_val_3860_);
v___x_3863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3861_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3771_, v___x_3863_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3866_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref(v___x_3864_);
v___x_3866_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3702_, v_val_3860_, v_name_3717_, v_levelParams_3711_, v___x_3838_, v_a_3865_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
v___y_3798_ = v_a_3836_;
v___y_3799_ = v___x_3854_;
v___y_3800_ = v___x_3866_;
goto v___jp_3797_;
}
else
{
lean_dec(v_val_3860_);
lean_dec(v_name_3717_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v___y_3798_ = v_a_3836_;
v___y_3799_ = v___x_3854_;
v___y_3800_ = v___x_3864_;
goto v___jp_3797_;
}
}
}
else
{
lean_object* v___x_3867_; 
lean_dec(v_a_3856_);
lean_dec(v_name_3717_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v___x_3867_ = lean_box(0);
v___y_3793_ = v_a_3836_;
v___y_3794_ = v___x_3854_;
v_a_3795_ = v___x_3867_;
goto v___jp_3792_;
}
}
else
{
lean_object* v_a_3868_; 
lean_dec(v_name_3717_);
lean_dec(v_levelParams_3711_);
lean_dec_ref(v_ctorVal_3702_);
v_a_3868_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3868_);
lean_dec_ref(v___x_3855_);
v___y_3788_ = v_a_3836_;
v___y_3789_ = v___x_3854_;
v_a_3790_ = v_a_3868_;
goto v___jp_3787_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3940_, lean_object* v_decl_3941_, lean_object* v_ref_3942_){
_start:
{
lean_object* v_defValue_3944_; lean_object* v_descr_3945_; lean_object* v_deprecation_x3f_3946_; lean_object* v___x_3947_; uint8_t v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v_defValue_3944_ = lean_ctor_get(v_decl_3941_, 0);
v_descr_3945_ = lean_ctor_get(v_decl_3941_, 1);
v_deprecation_x3f_3946_ = lean_ctor_get(v_decl_3941_, 2);
v___x_3947_ = lean_alloc_ctor(1, 0, 1);
v___x_3948_ = lean_unbox(v_defValue_3944_);
lean_ctor_set_uint8(v___x_3947_, 0, v___x_3948_);
lean_inc(v_deprecation_x3f_3946_);
lean_inc_ref(v_descr_3945_);
lean_inc_n(v_name_3940_, 2);
v___x_3949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3949_, 0, v_name_3940_);
lean_ctor_set(v___x_3949_, 1, v_ref_3942_);
lean_ctor_set(v___x_3949_, 2, v___x_3947_);
lean_ctor_set(v___x_3949_, 3, v_descr_3945_);
lean_ctor_set(v___x_3949_, 4, v_deprecation_x3f_3946_);
v___x_3950_ = lean_register_option(v_name_3940_, v___x_3949_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3958_; 
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3958_ == 0)
{
lean_object* v_unused_3959_; 
v_unused_3959_ = lean_ctor_get(v___x_3950_, 0);
lean_dec(v_unused_3959_);
v___x_3952_ = v___x_3950_;
v_isShared_3953_ = v_isSharedCheck_3958_;
goto v_resetjp_3951_;
}
else
{
lean_dec(v___x_3950_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3958_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v___x_3956_; 
lean_inc(v_defValue_3944_);
v___x_3954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3954_, 0, v_name_3940_);
lean_ctor_set(v___x_3954_, 1, v_defValue_3944_);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3954_);
v___x_3956_ = v___x_3952_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3954_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec(v_name_3940_);
v_a_3960_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3950_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3950_);
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
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_3968_, lean_object* v_decl_3969_, lean_object* v_ref_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_3968_, v_decl_3969_, v_ref_3970_);
lean_dec_ref(v_decl_3969_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3987_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3988_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3989_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3990_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_3987_, v___x_3988_, v___x_3989_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_3993_, uint8_t v_isExporting_3994_, lean_object* v___x_3995_, lean_object* v___y_3996_, lean_object* v___x_3997_, lean_object* v_a_x3f_3998_){
_start:
{
lean_object* v___x_4000_; lean_object* v_env_4001_; lean_object* v_nextMacroScope_4002_; lean_object* v_ngen_4003_; lean_object* v_auxDeclNGen_4004_; lean_object* v_traceState_4005_; lean_object* v_messages_4006_; lean_object* v_infoState_4007_; lean_object* v_snapshotTasks_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4033_; 
v___x_4000_ = lean_st_ref_take(v___y_3993_);
v_env_4001_ = lean_ctor_get(v___x_4000_, 0);
v_nextMacroScope_4002_ = lean_ctor_get(v___x_4000_, 1);
v_ngen_4003_ = lean_ctor_get(v___x_4000_, 2);
v_auxDeclNGen_4004_ = lean_ctor_get(v___x_4000_, 3);
v_traceState_4005_ = lean_ctor_get(v___x_4000_, 4);
v_messages_4006_ = lean_ctor_get(v___x_4000_, 6);
v_infoState_4007_ = lean_ctor_get(v___x_4000_, 7);
v_snapshotTasks_4008_ = lean_ctor_get(v___x_4000_, 8);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4033_ == 0)
{
lean_object* v_unused_4034_; 
v_unused_4034_ = lean_ctor_get(v___x_4000_, 5);
lean_dec(v_unused_4034_);
v___x_4010_ = v___x_4000_;
v_isShared_4011_ = v_isSharedCheck_4033_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_snapshotTasks_4008_);
lean_inc(v_infoState_4007_);
lean_inc(v_messages_4006_);
lean_inc(v_traceState_4005_);
lean_inc(v_auxDeclNGen_4004_);
lean_inc(v_ngen_4003_);
lean_inc(v_nextMacroScope_4002_);
lean_inc(v_env_4001_);
lean_dec(v___x_4000_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4033_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4012_; lean_object* v___x_4014_; 
v___x_4012_ = l_Lean_Environment_setExporting(v_env_4001_, v_isExporting_3994_);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 5, v___x_3995_);
lean_ctor_set(v___x_4010_, 0, v___x_4012_);
v___x_4014_ = v___x_4010_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4012_);
lean_ctor_set(v_reuseFailAlloc_4032_, 1, v_nextMacroScope_4002_);
lean_ctor_set(v_reuseFailAlloc_4032_, 2, v_ngen_4003_);
lean_ctor_set(v_reuseFailAlloc_4032_, 3, v_auxDeclNGen_4004_);
lean_ctor_set(v_reuseFailAlloc_4032_, 4, v_traceState_4005_);
lean_ctor_set(v_reuseFailAlloc_4032_, 5, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_4032_, 6, v_messages_4006_);
lean_ctor_set(v_reuseFailAlloc_4032_, 7, v_infoState_4007_);
lean_ctor_set(v_reuseFailAlloc_4032_, 8, v_snapshotTasks_4008_);
v___x_4014_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v_mctx_4017_; lean_object* v_zetaDeltaFVarIds_4018_; lean_object* v_postponed_4019_; lean_object* v_diag_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4030_; 
v___x_4015_ = lean_st_ref_set(v___y_3993_, v___x_4014_);
v___x_4016_ = lean_st_ref_take(v___y_3996_);
v_mctx_4017_ = lean_ctor_get(v___x_4016_, 0);
v_zetaDeltaFVarIds_4018_ = lean_ctor_get(v___x_4016_, 2);
v_postponed_4019_ = lean_ctor_get(v___x_4016_, 3);
v_diag_4020_ = lean_ctor_get(v___x_4016_, 4);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4030_ == 0)
{
lean_object* v_unused_4031_; 
v_unused_4031_ = lean_ctor_get(v___x_4016_, 1);
lean_dec(v_unused_4031_);
v___x_4022_ = v___x_4016_;
v_isShared_4023_ = v_isSharedCheck_4030_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_diag_4020_);
lean_inc(v_postponed_4019_);
lean_inc(v_zetaDeltaFVarIds_4018_);
lean_inc(v_mctx_4017_);
lean_dec(v___x_4016_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4030_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_3997_);
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_mctx_4017_);
lean_ctor_set(v_reuseFailAlloc_4029_, 1, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4029_, 2, v_zetaDeltaFVarIds_4018_);
lean_ctor_set(v_reuseFailAlloc_4029_, 3, v_postponed_4019_);
lean_ctor_set(v_reuseFailAlloc_4029_, 4, v_diag_4020_);
v___x_4025_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = lean_st_ref_set(v___y_3996_, v___x_4025_);
v___x_4027_ = lean_box(0);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
return v___x_4028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4035_, lean_object* v_isExporting_4036_, lean_object* v___x_4037_, lean_object* v___y_4038_, lean_object* v___x_4039_, lean_object* v_a_x3f_4040_, lean_object* v___y_4041_){
_start:
{
uint8_t v_isExporting_boxed_4042_; lean_object* v_res_4043_; 
v_isExporting_boxed_4042_ = lean_unbox(v_isExporting_4036_);
v_res_4043_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4035_, v_isExporting_boxed_4042_, v___x_4037_, v___y_4038_, v___x_4039_, v_a_x3f_4040_);
lean_dec(v_a_x3f_4040_);
lean_dec(v___y_4038_);
lean_dec(v___y_4035_);
return v_res_4043_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4044_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
return v___x_4048_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4050_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
lean_ctor_set(v___x_4050_, 2, v___x_4049_);
lean_ctor_set(v___x_4050_, 3, v___x_4049_);
lean_ctor_set(v___x_4050_, 4, v___x_4049_);
lean_ctor_set(v___x_4050_, 5, v___x_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4051_, uint8_t v_isExporting_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v___x_4058_; lean_object* v_env_4059_; uint8_t v_isExporting_4060_; lean_object* v___x_4061_; lean_object* v_env_4062_; lean_object* v_nextMacroScope_4063_; lean_object* v_ngen_4064_; lean_object* v_auxDeclNGen_4065_; lean_object* v_traceState_4066_; lean_object* v_messages_4067_; lean_object* v_infoState_4068_; lean_object* v_snapshotTasks_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4123_; 
v___x_4058_ = lean_st_ref_get(v___y_4056_);
v_env_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc_ref(v_env_4059_);
lean_dec(v___x_4058_);
v_isExporting_4060_ = lean_ctor_get_uint8(v_env_4059_, sizeof(void*)*8);
lean_dec_ref(v_env_4059_);
v___x_4061_ = lean_st_ref_take(v___y_4056_);
v_env_4062_ = lean_ctor_get(v___x_4061_, 0);
v_nextMacroScope_4063_ = lean_ctor_get(v___x_4061_, 1);
v_ngen_4064_ = lean_ctor_get(v___x_4061_, 2);
v_auxDeclNGen_4065_ = lean_ctor_get(v___x_4061_, 3);
v_traceState_4066_ = lean_ctor_get(v___x_4061_, 4);
v_messages_4067_ = lean_ctor_get(v___x_4061_, 6);
v_infoState_4068_ = lean_ctor_get(v___x_4061_, 7);
v_snapshotTasks_4069_ = lean_ctor_get(v___x_4061_, 8);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4123_ == 0)
{
lean_object* v_unused_4124_; 
v_unused_4124_ = lean_ctor_get(v___x_4061_, 5);
lean_dec(v_unused_4124_);
v___x_4071_ = v___x_4061_;
v_isShared_4072_ = v_isSharedCheck_4123_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_snapshotTasks_4069_);
lean_inc(v_infoState_4068_);
lean_inc(v_messages_4067_);
lean_inc(v_traceState_4066_);
lean_inc(v_auxDeclNGen_4065_);
lean_inc(v_ngen_4064_);
lean_inc(v_nextMacroScope_4063_);
lean_inc(v_env_4062_);
lean_dec(v___x_4061_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4123_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4076_; 
v___x_4073_ = l_Lean_Environment_setExporting(v_env_4062_, v_isExporting_4052_);
v___x_4074_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 5, v___x_4074_);
lean_ctor_set(v___x_4071_, 0, v___x_4073_);
v___x_4076_ = v___x_4071_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4122_, 1, v_nextMacroScope_4063_);
lean_ctor_set(v_reuseFailAlloc_4122_, 2, v_ngen_4064_);
lean_ctor_set(v_reuseFailAlloc_4122_, 3, v_auxDeclNGen_4065_);
lean_ctor_set(v_reuseFailAlloc_4122_, 4, v_traceState_4066_);
lean_ctor_set(v_reuseFailAlloc_4122_, 5, v___x_4074_);
lean_ctor_set(v_reuseFailAlloc_4122_, 6, v_messages_4067_);
lean_ctor_set(v_reuseFailAlloc_4122_, 7, v_infoState_4068_);
lean_ctor_set(v_reuseFailAlloc_4122_, 8, v_snapshotTasks_4069_);
v___x_4076_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v_mctx_4079_; lean_object* v_zetaDeltaFVarIds_4080_; lean_object* v_postponed_4081_; lean_object* v_diag_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4120_; 
v___x_4077_ = lean_st_ref_set(v___y_4056_, v___x_4076_);
v___x_4078_ = lean_st_ref_take(v___y_4054_);
v_mctx_4079_ = lean_ctor_get(v___x_4078_, 0);
v_zetaDeltaFVarIds_4080_ = lean_ctor_get(v___x_4078_, 2);
v_postponed_4081_ = lean_ctor_get(v___x_4078_, 3);
v_diag_4082_ = lean_ctor_get(v___x_4078_, 4);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4120_ == 0)
{
lean_object* v_unused_4121_; 
v_unused_4121_ = lean_ctor_get(v___x_4078_, 1);
lean_dec(v_unused_4121_);
v___x_4084_ = v___x_4078_;
v_isShared_4085_ = v_isSharedCheck_4120_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_diag_4082_);
lean_inc(v_postponed_4081_);
lean_inc(v_zetaDeltaFVarIds_4080_);
lean_inc(v_mctx_4079_);
lean_dec(v___x_4078_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4120_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4086_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 1, v___x_4086_);
v___x_4088_ = v___x_4084_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_mctx_4079_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v___x_4086_);
lean_ctor_set(v_reuseFailAlloc_4119_, 2, v_zetaDeltaFVarIds_4080_);
lean_ctor_set(v_reuseFailAlloc_4119_, 3, v_postponed_4081_);
lean_ctor_set(v_reuseFailAlloc_4119_, 4, v_diag_4082_);
v___x_4088_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4089_; lean_object* v_r_4090_; 
v___x_4089_ = lean_st_ref_set(v___y_4054_, v___x_4088_);
lean_inc(v___y_4056_);
lean_inc_ref(v___y_4055_);
lean_inc(v___y_4054_);
lean_inc_ref(v___y_4053_);
v_r_4090_ = lean_apply_5(v_x_4051_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, lean_box(0));
if (lean_obj_tag(v_r_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4107_; 
v_a_4091_ = lean_ctor_get(v_r_4090_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v_r_4090_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4093_ = v_r_4090_;
v_isShared_4094_ = v_isSharedCheck_4107_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v_r_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4107_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
lean_inc(v_a_4091_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set_tag(v___x_4093_, 1);
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
lean_object* v___x_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
v___x_4097_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4056_, v_isExporting_4060_, v___x_4074_, v___y_4054_, v___x_4086_, v___x_4096_);
lean_dec_ref(v___x_4096_);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4104_ == 0)
{
lean_object* v_unused_4105_; 
v_unused_4105_ = lean_ctor_get(v___x_4097_, 0);
lean_dec(v_unused_4105_);
v___x_4099_ = v___x_4097_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_dec(v___x_4097_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v_a_4091_);
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4091_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
v_a_4108_ = lean_ctor_get(v_r_4090_, 0);
lean_inc(v_a_4108_);
lean_dec_ref(v_r_4090_);
v___x_4109_ = lean_box(0);
v___x_4110_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4056_, v_isExporting_4060_, v___x_4074_, v___y_4054_, v___x_4086_, v___x_4109_);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4117_ == 0)
{
lean_object* v_unused_4118_; 
v_unused_4118_ = lean_ctor_get(v___x_4110_, 0);
lean_dec(v_unused_4118_);
v___x_4112_ = v___x_4110_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_dec(v___x_4110_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
lean_ctor_set_tag(v___x_4112_, 1);
lean_ctor_set(v___x_4112_, 0, v_a_4108_);
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4108_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4125_, lean_object* v_isExporting_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
uint8_t v_isExporting_boxed_4132_; lean_object* v_res_4133_; 
v_isExporting_boxed_4132_ = lean_unbox(v_isExporting_4126_);
v_res_4133_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4125_, v_isExporting_boxed_4132_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4134_, lean_object* v_x_4135_, uint8_t v_isExporting_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4135_, v_isExporting_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4143_, lean_object* v_x_4144_, lean_object* v_isExporting_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
uint8_t v_isExporting_boxed_4151_; lean_object* v_res_4152_; 
v_isExporting_boxed_4151_ = lean_unbox(v_isExporting_4145_);
v_res_4152_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4143_, v_x_4144_, v_isExporting_boxed_4151_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4153_, lean_object* v_localInsts_4154_, lean_object* v_x_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4153_, v_localInsts_4154_, v_x_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4161_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4161_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
v_a_4170_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4161_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4161_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4178_, lean_object* v_localInsts_4179_, lean_object* v_x_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4178_, v_localInsts_4179_, v_x_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4187_, lean_object* v_lctx_4188_, lean_object* v_localInsts_4189_, lean_object* v_x_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4188_, v_localInsts_4189_, v_x_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4197_, lean_object* v_lctx_4198_, lean_object* v_localInsts_4199_, lean_object* v_x_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4197_, v_lctx_4198_, v_localInsts_4199_, v_x_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4207_, lean_object* v_x_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = l_Lean_MessageData_ofName(v_declName_4207_);
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4216_, lean_object* v_x_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4216_, v_x_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec_ref(v_x_4217_);
return v_res_4223_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = l_instMonadEIO(lean_box(0));
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v_toApplicative_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4298_; 
v___x_4235_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4236_ = l_StateRefT_x27_instMonad___redArg(v___x_4235_);
v_toApplicative_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4298_ == 0)
{
lean_object* v_unused_4299_; 
v_unused_4299_ = lean_ctor_get(v___x_4236_, 1);
lean_dec(v_unused_4299_);
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4298_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_toApplicative_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4298_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v_toFunctor_4241_; lean_object* v_toSeq_4242_; lean_object* v_toSeqLeft_4243_; lean_object* v_toSeqRight_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4296_; 
v_toFunctor_4241_ = lean_ctor_get(v_toApplicative_4237_, 0);
v_toSeq_4242_ = lean_ctor_get(v_toApplicative_4237_, 2);
v_toSeqLeft_4243_ = lean_ctor_get(v_toApplicative_4237_, 3);
v_toSeqRight_4244_ = lean_ctor_get(v_toApplicative_4237_, 4);
v_isSharedCheck_4296_ = !lean_is_exclusive(v_toApplicative_4237_);
if (v_isSharedCheck_4296_ == 0)
{
lean_object* v_unused_4297_; 
v_unused_4297_ = lean_ctor_get(v_toApplicative_4237_, 1);
lean_dec(v_unused_4297_);
v___x_4246_ = v_toApplicative_4237_;
v_isShared_4247_ = v_isSharedCheck_4296_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_toSeqRight_4244_);
lean_inc(v_toSeqLeft_4243_);
lean_inc(v_toSeq_4242_);
lean_inc(v_toFunctor_4241_);
lean_dec(v_toApplicative_4237_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4296_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___f_4248_; lean_object* v___f_4249_; lean_object* v___f_4250_; lean_object* v___f_4251_; lean_object* v___x_4252_; lean_object* v___f_4253_; lean_object* v___f_4254_; lean_object* v___f_4255_; lean_object* v___x_4257_; 
v___f_4248_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4249_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4241_);
v___f_4250_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4250_, 0, v_toFunctor_4241_);
v___f_4251_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4251_, 0, v_toFunctor_4241_);
v___x_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___f_4250_);
lean_ctor_set(v___x_4252_, 1, v___f_4251_);
v___f_4253_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4253_, 0, v_toSeqRight_4244_);
v___f_4254_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4254_, 0, v_toSeqLeft_4243_);
v___f_4255_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4255_, 0, v_toSeq_4242_);
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 4, v___f_4253_);
lean_ctor_set(v___x_4246_, 3, v___f_4254_);
lean_ctor_set(v___x_4246_, 2, v___f_4255_);
lean_ctor_set(v___x_4246_, 1, v___f_4248_);
lean_ctor_set(v___x_4246_, 0, v___x_4252_);
v___x_4257_ = v___x_4246_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4252_);
lean_ctor_set(v_reuseFailAlloc_4295_, 1, v___f_4248_);
lean_ctor_set(v_reuseFailAlloc_4295_, 2, v___f_4255_);
lean_ctor_set(v_reuseFailAlloc_4295_, 3, v___f_4254_);
lean_ctor_set(v_reuseFailAlloc_4295_, 4, v___f_4253_);
v___x_4257_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
lean_object* v___x_4259_; 
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 1, v___f_4249_);
lean_ctor_set(v___x_4239_, 0, v___x_4257_);
v___x_4259_ = v___x_4239_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4257_);
lean_ctor_set(v_reuseFailAlloc_4294_, 1, v___f_4249_);
v___x_4259_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
lean_object* v___x_4260_; lean_object* v_toApplicative_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4292_; 
v___x_4260_ = l_StateRefT_x27_instMonad___redArg(v___x_4259_);
v_toApplicative_4261_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4292_ == 0)
{
lean_object* v_unused_4293_; 
v_unused_4293_ = lean_ctor_get(v___x_4260_, 1);
lean_dec(v_unused_4293_);
v___x_4263_ = v___x_4260_;
v_isShared_4264_ = v_isSharedCheck_4292_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_toApplicative_4261_);
lean_dec(v___x_4260_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4292_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v_toFunctor_4265_; lean_object* v_toSeq_4266_; lean_object* v_toSeqLeft_4267_; lean_object* v_toSeqRight_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4290_; 
v_toFunctor_4265_ = lean_ctor_get(v_toApplicative_4261_, 0);
v_toSeq_4266_ = lean_ctor_get(v_toApplicative_4261_, 2);
v_toSeqLeft_4267_ = lean_ctor_get(v_toApplicative_4261_, 3);
v_toSeqRight_4268_ = lean_ctor_get(v_toApplicative_4261_, 4);
v_isSharedCheck_4290_ = !lean_is_exclusive(v_toApplicative_4261_);
if (v_isSharedCheck_4290_ == 0)
{
lean_object* v_unused_4291_; 
v_unused_4291_ = lean_ctor_get(v_toApplicative_4261_, 1);
lean_dec(v_unused_4291_);
v___x_4270_ = v_toApplicative_4261_;
v_isShared_4271_ = v_isSharedCheck_4290_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_toSeqRight_4268_);
lean_inc(v_toSeqLeft_4267_);
lean_inc(v_toSeq_4266_);
lean_inc(v_toFunctor_4265_);
lean_dec(v_toApplicative_4261_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4290_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___f_4272_; lean_object* v___f_4273_; lean_object* v___f_4274_; lean_object* v___f_4275_; lean_object* v___x_4276_; lean_object* v___f_4277_; lean_object* v___f_4278_; lean_object* v___f_4279_; lean_object* v___x_4281_; 
v___f_4272_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4273_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4265_);
v___f_4274_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4274_, 0, v_toFunctor_4265_);
v___f_4275_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4275_, 0, v_toFunctor_4265_);
v___x_4276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___f_4274_);
lean_ctor_set(v___x_4276_, 1, v___f_4275_);
v___f_4277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4277_, 0, v_toSeqRight_4268_);
v___f_4278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4278_, 0, v_toSeqLeft_4267_);
v___f_4279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4279_, 0, v_toSeq_4266_);
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 4, v___f_4277_);
lean_ctor_set(v___x_4270_, 3, v___f_4278_);
lean_ctor_set(v___x_4270_, 2, v___f_4279_);
lean_ctor_set(v___x_4270_, 1, v___f_4272_);
lean_ctor_set(v___x_4270_, 0, v___x_4276_);
v___x_4281_ = v___x_4270_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v___x_4276_);
lean_ctor_set(v_reuseFailAlloc_4289_, 1, v___f_4272_);
lean_ctor_set(v_reuseFailAlloc_4289_, 2, v___f_4279_);
lean_ctor_set(v_reuseFailAlloc_4289_, 3, v___f_4278_);
lean_ctor_set(v_reuseFailAlloc_4289_, 4, v___f_4277_);
v___x_4281_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
lean_object* v___x_4283_; 
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 1, v___f_4273_);
lean_ctor_set(v___x_4263_, 0, v___x_4281_);
v___x_4283_ = v___x_4263_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v___x_4281_);
lean_ctor_set(v_reuseFailAlloc_4288_, 1, v___f_4273_);
v___x_4283_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_19101__overap_4286_; lean_object* v___x_4287_; 
v___x_4284_ = lean_box(0);
v___x_4285_ = l_instInhabitedOfMonad___redArg(v___x_4283_, v___x_4284_);
v___x_19101__overap_4286_ = lean_panic_fn_borrowed(v___x_4285_, v_msg_4229_);
lean_dec(v___x_4285_);
lean_inc(v___y_4233_);
lean_inc_ref(v___y_4232_);
lean_inc(v___y_4231_);
lean_inc_ref(v___y_4230_);
v___x_4287_ = lean_apply_5(v___x_19101__overap_4286_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, lean_box(0));
return v___x_4287_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
return v_res_4306_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4309_ = l_Lean_stringToMessageData(v___x_4308_);
return v___x_4309_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4312_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4313_ = lean_unsigned_to_nat(11u);
v___x_4314_ = lean_unsigned_to_nat(122u);
v___x_4315_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4316_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4317_ = l_mkPanicMessageWithDecl(v___x_4316_, v___x_4315_, v___x_4314_, v___x_4313_, v___x_4312_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v___x_4332_; lean_object* v_env_4333_; uint8_t v___x_4334_; lean_object* v___x_4335_; 
v___x_4332_ = lean_st_ref_get(v___y_4322_);
v_env_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc_ref(v_env_4333_);
lean_dec(v___x_4332_);
v___x_4334_ = 0;
lean_inc(v_constName_4318_);
v___x_4335_ = l_Lean_Environment_findAsync_x3f(v_env_4333_, v_constName_4318_, v___x_4334_);
if (lean_obj_tag(v___x_4335_) == 1)
{
lean_object* v_val_4336_; uint8_t v_kind_4337_; 
v_val_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_val_4336_);
lean_dec_ref(v___x_4335_);
v_kind_4337_ = lean_ctor_get_uint8(v_val_4336_, sizeof(void*)*3);
if (v_kind_4337_ == 6)
{
lean_object* v___x_4338_; 
v___x_4338_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4336_);
if (lean_obj_tag(v___x_4338_) == 6)
{
lean_object* v_val_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec(v_constName_4318_);
v_val_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_val_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
lean_ctor_set_tag(v___x_4341_, 0);
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_val_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
else
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
lean_dec_ref(v___x_4338_);
v___x_4347_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4348_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4347_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4357_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4351_ = v___x_4348_;
v_isShared_4352_ = v_isSharedCheck_4357_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4348_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4357_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
if (lean_obj_tag(v_a_4349_) == 0)
{
lean_del_object(v___x_4351_);
goto v___jp_4324_;
}
else
{
lean_object* v_val_4353_; lean_object* v___x_4355_; 
lean_dec(v_constName_4318_);
v_val_4353_ = lean_ctor_get(v_a_4349_, 0);
lean_inc(v_val_4353_);
lean_dec_ref(v_a_4349_);
if (v_isShared_4352_ == 0)
{
lean_ctor_set(v___x_4351_, 0, v_val_4353_);
v___x_4355_ = v___x_4351_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_val_4353_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_dec(v_constName_4318_);
v_a_4358_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4348_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4348_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
else
{
lean_dec(v_val_4336_);
goto v___jp_4324_;
}
}
else
{
lean_dec(v___x_4335_);
goto v___jp_4324_;
}
v___jp_4324_:
{
lean_object* v___x_4325_; uint8_t v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4325_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4326_ = 0;
v___x_4327_ = l_Lean_MessageData_ofConstName(v_constName_4318_, v___x_4326_);
v___x_4328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4325_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
v___x_4329_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___x_4328_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
v___x_4331_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4330_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
return v___x_4331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4373_, lean_object* v___x_4374_, lean_object* v___x_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4373_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4393_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4384_ = v___x_4381_;
v_isShared_4385_ = v_isSharedCheck_4393_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4381_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4393_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v_numFields_4386_; uint8_t v___x_4387_; 
v_numFields_4386_ = lean_ctor_get(v_a_4382_, 4);
v___x_4387_ = lean_nat_dec_lt(v___x_4374_, v_numFields_4386_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4389_; 
lean_dec(v_a_4382_);
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 0, v___x_4375_);
v___x_4389_ = v___x_4384_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4375_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
else
{
lean_object* v___x_4391_; 
lean_del_object(v___x_4384_);
lean_inc(v_a_4382_);
v___x_4391_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4382_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v___x_4392_; 
lean_dec_ref(v___x_4391_);
v___x_4392_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4382_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
return v___x_4392_;
}
else
{
lean_dec(v_a_4382_);
return v___x_4391_;
}
}
}
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
v_a_4394_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4381_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4381_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4402_, lean_object* v___x_4403_, lean_object* v___x_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4402_, v___x_4403_, v___x_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___x_4403_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4411_, uint8_t v___x_4412_, lean_object* v_as_x27_4413_, lean_object* v_b_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
if (lean_obj_tag(v_as_x27_4413_) == 0)
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4420_, 0, v_b_4414_);
return v___x_4420_;
}
else
{
lean_object* v_head_4421_; lean_object* v_tail_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___f_4425_; uint8_t v___y_4427_; uint8_t v___x_4430_; 
v_head_4421_ = lean_ctor_get(v_as_x27_4413_, 0);
v_tail_4422_ = lean_ctor_get(v_as_x27_4413_, 1);
v___x_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = lean_box(0);
lean_inc(v_head_4421_);
v___f_4425_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4425_, 0, v_head_4421_);
lean_closure_set(v___f_4425_, 1, v___x_4423_);
lean_closure_set(v___f_4425_, 2, v___x_4424_);
v___x_4430_ = l_Lean_isPrivateName(v_head_4421_);
if (v___x_4430_ == 0)
{
v___y_4427_ = v___y_4411_;
goto v___jp_4426_;
}
else
{
v___y_4427_ = v___x_4412_;
goto v___jp_4426_;
}
v___jp_4426_:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4425_, v___y_4427_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_dec_ref(v___x_4428_);
v_as_x27_4413_ = v_tail_4422_;
v_b_4414_ = v___x_4424_;
goto _start;
}
else
{
return v___x_4428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4431_, lean_object* v___x_4432_, lean_object* v_as_x27_4433_, lean_object* v_b_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
uint8_t v___y_20211__boxed_4440_; uint8_t v___x_20212__boxed_4441_; lean_object* v_res_4442_; 
v___y_20211__boxed_4440_ = lean_unbox(v___y_4431_);
v___x_20212__boxed_4441_ = lean_unbox(v___x_4432_);
v_res_4442_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_20211__boxed_4440_, v___x_20212__boxed_4441_, v_as_x27_4433_, v_b_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v_as_x27_4433_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4443_, uint8_t v_hasTrace_4444_, lean_object* v_ctors_4445_, lean_object* v___x_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4443_, v_hasTrace_4444_, v_ctors_4445_, v___x_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4459_ == 0)
{
lean_object* v_unused_4460_; 
v_unused_4460_ = lean_ctor_get(v___x_4452_, 0);
lean_dec(v_unused_4460_);
v___x_4454_ = v___x_4452_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_dec(v___x_4452_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 0, v___x_4446_);
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4446_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
else
{
return v___x_4452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4461_, lean_object* v_hasTrace_4462_, lean_object* v_ctors_4463_, lean_object* v___x_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
uint8_t v___y_20256__boxed_4470_; uint8_t v_hasTrace_boxed_4471_; lean_object* v_res_4472_; 
v___y_20256__boxed_4470_ = lean_unbox(v___y_4461_);
v_hasTrace_boxed_4471_ = lean_unbox(v_hasTrace_4462_);
v_res_4472_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_20256__boxed_4470_, v_hasTrace_boxed_4471_, v_ctors_4463_, v___x_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v_ctors_4463_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t v_hasTrace_4473_, uint8_t v___x_4474_, lean_object* v_ctors_4475_, lean_object* v___x_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_hasTrace_4473_, v___x_4474_, v_ctors_4475_, v___x_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4489_ == 0)
{
lean_object* v_unused_4490_; 
v_unused_4490_ = lean_ctor_get(v___x_4482_, 0);
lean_dec(v_unused_4490_);
v___x_4484_ = v___x_4482_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_dec(v___x_4482_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4476_);
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4476_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
else
{
return v___x_4482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object* v_hasTrace_4491_, lean_object* v___x_4492_, lean_object* v_ctors_4493_, lean_object* v___x_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
uint8_t v_hasTrace_boxed_4500_; uint8_t v___x_20297__boxed_4501_; lean_object* v_res_4502_; 
v_hasTrace_boxed_4500_ = lean_unbox(v_hasTrace_4491_);
v___x_20297__boxed_4501_ = lean_unbox(v___x_4492_);
v_res_4502_ = l_Lean_Meta_mkInjectiveTheorems___lam__2(v_hasTrace_boxed_4500_, v___x_20297__boxed_4501_, v_ctors_4493_, v___x_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v_ctors_4493_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t v___x_4503_, uint8_t v_isUnsafe_4504_, lean_object* v_ctors_4505_, lean_object* v___x_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v___x_4512_; 
v___x_4512_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4503_, v_isUnsafe_4504_, v_ctors_4505_, v___x_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v___x_4512_, 0);
lean_dec(v_unused_4520_);
v___x_4514_ = v___x_4512_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_dec(v___x_4512_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
lean_ctor_set(v___x_4514_, 0, v___x_4506_);
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4506_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
else
{
return v___x_4512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object* v___x_4521_, lean_object* v_isUnsafe_4522_, lean_object* v_ctors_4523_, lean_object* v___x_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
uint8_t v___x_20338__boxed_4530_; uint8_t v_isUnsafe_boxed_4531_; lean_object* v_res_4532_; 
v___x_20338__boxed_4530_ = lean_unbox(v___x_4521_);
v_isUnsafe_boxed_4531_ = lean_unbox(v_isUnsafe_4522_);
v_res_4532_ = l_Lean_Meta_mkInjectiveTheorems___lam__3(v___x_20338__boxed_4530_, v_isUnsafe_boxed_4531_, v_ctors_4523_, v___x_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v_ctors_4523_);
return v_res_4532_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4535_ = l_Lean_stringToMessageData(v___x_4534_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v___x_4542_; lean_object* v_env_4543_; lean_object* v___x_4544_; 
v___x_4542_ = lean_st_ref_get(v___y_4540_);
v_env_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc_ref(v_env_4543_);
lean_dec(v___x_4542_);
lean_inc(v_constName_4536_);
v___x_4544_ = l_Lean_isInductiveCore_x3f(v_env_4543_, v_constName_4536_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v___x_4545_; uint8_t v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4545_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4546_ = 0;
v___x_4547_ = l_Lean_MessageData_ofConstName(v_constName_4536_, v___x_4546_);
v___x_4548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4545_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
v___x_4549_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4548_);
lean_ctor_set(v___x_4550_, 1, v___x_4549_);
v___x_4551_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4550_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
return v___x_4551_;
}
else
{
lean_object* v_val_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v_constName_4536_);
v_val_4552_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4544_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_val_4552_);
lean_dec(v___x_4544_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
lean_ctor_set_tag(v___x_4554_, 0);
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_val_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
return v_res_4566_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4567_; 
v___x_4567_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4567_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
return v___x_4569_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4570_ = lean_unsigned_to_nat(32u);
v___x_4571_ = lean_mk_empty_array_with_capacity(v___x_4570_);
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
return v___x_4572_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4573_ = ((size_t)5ULL);
v___x_4574_ = lean_unsigned_to_nat(0u);
v___x_4575_ = lean_unsigned_to_nat(32u);
v___x_4576_ = lean_mk_empty_array_with_capacity(v___x_4575_);
v___x_4577_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4578_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
lean_ctor_set(v___x_4578_, 1, v___x_4576_);
lean_ctor_set(v___x_4578_, 2, v___x_4574_);
lean_ctor_set(v___x_4578_, 3, v___x_4574_);
lean_ctor_set_usize(v___x_4578_, 4, v___x_4573_);
return v___x_4578_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4579_ = lean_box(1);
v___x_4580_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4581_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
lean_ctor_set(v___x_4582_, 1, v___x_4580_);
lean_ctor_set(v___x_4582_, 2, v___x_4579_);
return v___x_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4591_ = lean_st_ref_get(v_a_4589_);
lean_inc(v_declName_4585_);
v___x_4592_ = l_Lean_Meta_isInductivePredicate(v_declName_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4789_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4595_ = v___x_4592_;
v_isShared_4596_ = v_isSharedCheck_4789_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4592_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4789_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v_env_4602_; lean_object* v___f_4603_; lean_object* v___x_4604_; uint8_t v___x_4605_; uint8_t v___y_4607_; lean_object* v___y_4608_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v_a_4613_; lean_object* v___y_4623_; lean_object* v___y_4624_; uint8_t v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v_a_4629_; lean_object* v___y_4632_; lean_object* v___y_4633_; uint8_t v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v_a_4638_; uint8_t v___y_4641_; lean_object* v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v_a_4647_; lean_object* v___y_4660_; lean_object* v___y_4661_; uint8_t v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v_a_4666_; lean_object* v___y_4669_; lean_object* v___y_4670_; uint8_t v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v_a_4675_; uint8_t v___y_4678_; uint8_t v___y_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; uint8_t v___y_4720_; uint8_t v___x_4785_; 
v_env_4602_ = lean_ctor_get(v___x_4591_, 0);
lean_inc_ref(v_env_4602_);
lean_dec(v___x_4591_);
lean_inc(v_declName_4585_);
v___f_4603_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4603_, 0, v_declName_4585_);
v___x_4604_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4605_ = 1;
v___x_4785_ = l_Lean_Environment_contains(v_env_4602_, v___x_4604_, v___x_4605_);
if (v___x_4785_ == 0)
{
v___y_4720_ = v___x_4785_;
goto v___jp_4719_;
}
else
{
lean_object* v_options_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v_options_4786_ = lean_ctor_get(v_a_4588_, 2);
v___x_4787_ = l_Lean_Meta_genInjectivity;
v___x_4788_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4786_, v___x_4787_);
v___y_4720_ = v___x_4788_;
goto v___jp_4719_;
}
v___jp_4597_:
{
lean_object* v___x_4598_; lean_object* v___x_4600_; 
v___x_4598_ = lean_box(0);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 0, v___x_4598_);
v___x_4600_ = v___x_4595_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
v___jp_4606_:
{
lean_object* v___x_4614_; double v___x_4615_; double v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4614_ = lean_io_get_num_heartbeats();
v___x_4615_ = lean_float_of_nat(v___y_4609_);
v___x_4616_ = lean_float_of_nat(v___x_4614_);
v___x_4617_ = lean_box_float(v___x_4615_);
v___x_4618_ = lean_box_float(v___x_4616_);
v___x_4619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4617_);
lean_ctor_set(v___x_4619_, 1, v___x_4618_);
v___x_4620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4620_, 0, v_a_4613_);
lean_ctor_set(v___x_4620_, 1, v___x_4619_);
lean_inc_ref(v___y_4610_);
lean_inc(v___y_4611_);
v___x_4621_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4611_, v___x_4605_, v___y_4610_, v___y_4608_, v___y_4607_, v___y_4612_, v___f_4603_, v___x_4620_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4621_;
}
v___jp_4622_:
{
lean_object* v___x_4630_; 
v___x_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4630_, 0, v_a_4629_);
v___y_4607_ = v___y_4625_;
v___y_4608_ = v___y_4624_;
v___y_4609_ = v___y_4623_;
v___y_4610_ = v___y_4626_;
v___y_4611_ = v___y_4627_;
v___y_4612_ = v___y_4628_;
v_a_4613_ = v___x_4630_;
goto v___jp_4606_;
}
v___jp_4631_:
{
lean_object* v___x_4639_; 
v___x_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4639_, 0, v_a_4638_);
v___y_4607_ = v___y_4634_;
v___y_4608_ = v___y_4633_;
v___y_4609_ = v___y_4632_;
v___y_4610_ = v___y_4635_;
v___y_4611_ = v___y_4636_;
v___y_4612_ = v___y_4637_;
v_a_4613_ = v___x_4639_;
goto v___jp_4606_;
}
v___jp_4640_:
{
lean_object* v___x_4648_; double v___x_4649_; double v___x_4650_; double v___x_4651_; double v___x_4652_; double v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4648_ = lean_io_mono_nanos_now();
v___x_4649_ = lean_float_of_nat(v___y_4643_);
v___x_4650_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4651_ = lean_float_div(v___x_4649_, v___x_4650_);
v___x_4652_ = lean_float_of_nat(v___x_4648_);
v___x_4653_ = lean_float_div(v___x_4652_, v___x_4650_);
v___x_4654_ = lean_box_float(v___x_4651_);
v___x_4655_ = lean_box_float(v___x_4653_);
v___x_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4654_);
lean_ctor_set(v___x_4656_, 1, v___x_4655_);
v___x_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4657_, 0, v_a_4647_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
lean_inc_ref(v___y_4644_);
lean_inc(v___y_4645_);
v___x_4658_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4645_, v___x_4605_, v___y_4644_, v___y_4642_, v___y_4641_, v___y_4646_, v___f_4603_, v___x_4657_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4658_;
}
v___jp_4659_:
{
lean_object* v___x_4667_; 
v___x_4667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4667_, 0, v_a_4666_);
v___y_4641_ = v___y_4662_;
v___y_4642_ = v___y_4661_;
v___y_4643_ = v___y_4660_;
v___y_4644_ = v___y_4663_;
v___y_4645_ = v___y_4664_;
v___y_4646_ = v___y_4665_;
v_a_4647_ = v___x_4667_;
goto v___jp_4640_;
}
v___jp_4668_:
{
lean_object* v___x_4676_; 
v___x_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4676_, 0, v_a_4675_);
v___y_4641_ = v___y_4671_;
v___y_4642_ = v___y_4670_;
v___y_4643_ = v___y_4669_;
v___y_4644_ = v___y_4672_;
v___y_4645_ = v___y_4673_;
v___y_4646_ = v___y_4674_;
v_a_4647_ = v___x_4676_;
goto v___jp_4640_;
}
v___jp_4677_:
{
lean_object* v___x_4683_; lean_object* v_a_4684_; lean_object* v___x_4685_; uint8_t v___x_4686_; 
v___x_4683_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4589_);
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_a_4684_);
lean_dec_ref(v___x_4683_);
v___x_4685_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4686_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4680_, v___x_4685_);
if (v___x_4686_ == 0)
{
lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4687_ = lean_io_mono_nanos_now();
v___x_4688_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; uint8_t v_isUnsafe_4690_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_a_4689_);
lean_dec_ref(v___x_4688_);
v_isUnsafe_4690_ = lean_ctor_get_uint8(v_a_4689_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4690_ == 0)
{
lean_object* v_ctors_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___f_4697_; lean_object* v___x_4698_; 
v_ctors_4691_ = lean_ctor_get(v_a_4689_, 4);
lean_inc(v_ctors_4691_);
lean_dec(v_a_4689_);
v___x_4692_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4693_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4694_ = lean_box(0);
v___x_4695_ = lean_box(v___y_4678_);
v___x_4696_ = lean_box(v___x_4686_);
v___f_4697_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4697_, 0, v___x_4695_);
lean_closure_set(v___f_4697_, 1, v___x_4696_);
lean_closure_set(v___f_4697_, 2, v_ctors_4691_);
lean_closure_set(v___f_4697_, 3, v___x_4694_);
v___x_4698_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4692_, v___x_4693_, v___f_4697_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
lean_inc(v_a_4699_);
lean_dec_ref(v___x_4698_);
v___y_4660_ = v___x_4687_;
v___y_4661_ = v___y_4680_;
v___y_4662_ = v___y_4679_;
v___y_4663_ = v___y_4681_;
v___y_4664_ = v___y_4682_;
v___y_4665_ = v_a_4684_;
v_a_4666_ = v_a_4699_;
goto v___jp_4659_;
}
else
{
lean_object* v_a_4700_; 
v_a_4700_ = lean_ctor_get(v___x_4698_, 0);
lean_inc(v_a_4700_);
lean_dec_ref(v___x_4698_);
v___y_4669_ = v___x_4687_;
v___y_4670_ = v___y_4680_;
v___y_4671_ = v___y_4679_;
v___y_4672_ = v___y_4681_;
v___y_4673_ = v___y_4682_;
v___y_4674_ = v_a_4684_;
v_a_4675_ = v_a_4700_;
goto v___jp_4668_;
}
}
else
{
lean_object* v___x_4701_; 
lean_dec(v_a_4689_);
v___x_4701_ = lean_box(0);
v___y_4660_ = v___x_4687_;
v___y_4661_ = v___y_4680_;
v___y_4662_ = v___y_4679_;
v___y_4663_ = v___y_4681_;
v___y_4664_ = v___y_4682_;
v___y_4665_ = v_a_4684_;
v_a_4666_ = v___x_4701_;
goto v___jp_4659_;
}
}
else
{
lean_object* v_a_4702_; 
v_a_4702_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_a_4702_);
lean_dec_ref(v___x_4688_);
v___y_4669_ = v___x_4687_;
v___y_4670_ = v___y_4680_;
v___y_4671_ = v___y_4679_;
v___y_4672_ = v___y_4681_;
v___y_4673_ = v___y_4682_;
v___y_4674_ = v_a_4684_;
v_a_4675_ = v_a_4702_;
goto v___jp_4668_;
}
}
else
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4703_ = lean_io_get_num_heartbeats();
v___x_4704_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v_a_4705_; uint8_t v_isUnsafe_4706_; 
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc(v_a_4705_);
lean_dec_ref(v___x_4704_);
v_isUnsafe_4706_ = lean_ctor_get_uint8(v_a_4705_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4706_ == 0)
{
lean_object* v_ctors_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___f_4713_; lean_object* v___x_4714_; 
v_ctors_4707_ = lean_ctor_get(v_a_4705_, 4);
lean_inc(v_ctors_4707_);
lean_dec(v_a_4705_);
v___x_4708_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4709_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4710_ = lean_box(0);
v___x_4711_ = lean_box(v___x_4686_);
v___x_4712_ = lean_box(v_isUnsafe_4706_);
v___f_4713_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed), 9, 4);
lean_closure_set(v___f_4713_, 0, v___x_4711_);
lean_closure_set(v___f_4713_, 1, v___x_4712_);
lean_closure_set(v___f_4713_, 2, v_ctors_4707_);
lean_closure_set(v___f_4713_, 3, v___x_4710_);
v___x_4714_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4708_, v___x_4709_, v___f_4713_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v_a_4715_; 
v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
lean_inc(v_a_4715_);
lean_dec_ref(v___x_4714_);
v___y_4623_ = v___x_4703_;
v___y_4624_ = v___y_4680_;
v___y_4625_ = v___y_4679_;
v___y_4626_ = v___y_4681_;
v___y_4627_ = v___y_4682_;
v___y_4628_ = v_a_4684_;
v_a_4629_ = v_a_4715_;
goto v___jp_4622_;
}
else
{
lean_object* v_a_4716_; 
v_a_4716_ = lean_ctor_get(v___x_4714_, 0);
lean_inc(v_a_4716_);
lean_dec_ref(v___x_4714_);
v___y_4632_ = v___x_4703_;
v___y_4633_ = v___y_4680_;
v___y_4634_ = v___y_4679_;
v___y_4635_ = v___y_4681_;
v___y_4636_ = v___y_4682_;
v___y_4637_ = v_a_4684_;
v_a_4638_ = v_a_4716_;
goto v___jp_4631_;
}
}
else
{
lean_object* v___x_4717_; 
lean_dec(v_a_4705_);
v___x_4717_ = lean_box(0);
v___y_4623_ = v___x_4703_;
v___y_4624_ = v___y_4680_;
v___y_4625_ = v___y_4679_;
v___y_4626_ = v___y_4681_;
v___y_4627_ = v___y_4682_;
v___y_4628_ = v_a_4684_;
v_a_4629_ = v___x_4717_;
goto v___jp_4622_;
}
}
else
{
lean_object* v_a_4718_; 
v_a_4718_ = lean_ctor_get(v___x_4704_, 0);
lean_inc(v_a_4718_);
lean_dec_ref(v___x_4704_);
v___y_4632_ = v___x_4703_;
v___y_4633_ = v___y_4680_;
v___y_4634_ = v___y_4679_;
v___y_4635_ = v___y_4681_;
v___y_4636_ = v___y_4682_;
v___y_4637_ = v_a_4684_;
v_a_4638_ = v_a_4718_;
goto v___jp_4631_;
}
}
}
v___jp_4719_:
{
if (v___y_4720_ == 0)
{
lean_dec_ref(v___f_4603_);
lean_dec(v_a_4593_);
lean_dec(v_declName_4585_);
goto v___jp_4597_;
}
else
{
uint8_t v___x_4721_; 
v___x_4721_ = lean_unbox(v_a_4593_);
lean_dec(v_a_4593_);
if (v___x_4721_ == 0)
{
lean_object* v_options_4722_; uint8_t v_hasTrace_4723_; 
lean_del_object(v___x_4595_);
v_options_4722_ = lean_ctor_get(v_a_4588_, 2);
v_hasTrace_4723_ = lean_ctor_get_uint8(v_options_4722_, sizeof(void*)*1);
if (v_hasTrace_4723_ == 0)
{
lean_object* v___x_4724_; 
lean_dec_ref(v___f_4603_);
v___x_4724_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4742_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4727_ = v___x_4724_;
v_isShared_4728_ = v_isSharedCheck_4742_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4742_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
uint8_t v_isUnsafe_4729_; 
v_isUnsafe_4729_ = lean_ctor_get_uint8(v_a_4725_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4729_ == 0)
{
lean_object* v_ctors_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___f_4736_; lean_object* v___x_4737_; 
lean_del_object(v___x_4727_);
v_ctors_4730_ = lean_ctor_get(v_a_4725_, 4);
lean_inc(v_ctors_4730_);
lean_dec(v_a_4725_);
v___x_4731_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4732_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4733_ = lean_box(0);
v___x_4734_ = lean_box(v___y_4720_);
v___x_4735_ = lean_box(v_hasTrace_4723_);
v___f_4736_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4736_, 0, v___x_4734_);
lean_closure_set(v___f_4736_, 1, v___x_4735_);
lean_closure_set(v___f_4736_, 2, v_ctors_4730_);
lean_closure_set(v___f_4736_, 3, v___x_4733_);
v___x_4737_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4731_, v___x_4732_, v___f_4736_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4737_;
}
else
{
lean_object* v___x_4738_; lean_object* v___x_4740_; 
lean_dec(v_a_4725_);
v___x_4738_ = lean_box(0);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 0, v___x_4738_);
v___x_4740_ = v___x_4727_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4738_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
v_a_4743_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___x_4724_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4724_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; uint8_t v___x_4755_; 
v_inheritedTraceOptions_4751_ = lean_ctor_get(v_a_4588_, 13);
v___x_4752_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4753_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4754_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4755_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4751_, v_options_4722_, v___x_4754_);
if (v___x_4755_ == 0)
{
lean_object* v___x_4756_; uint8_t v___x_4757_; 
v___x_4756_ = l_Lean_trace_profiler;
v___x_4757_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4722_, v___x_4756_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; 
lean_dec_ref(v___f_4603_);
v___x_4758_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4776_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4761_ = v___x_4758_;
v_isShared_4762_ = v_isSharedCheck_4776_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4758_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4776_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
uint8_t v_isUnsafe_4763_; 
v_isUnsafe_4763_ = lean_ctor_get_uint8(v_a_4759_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4763_ == 0)
{
lean_object* v_ctors_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___f_4770_; lean_object* v___x_4771_; 
lean_del_object(v___x_4761_);
v_ctors_4764_ = lean_ctor_get(v_a_4759_, 4);
lean_inc(v_ctors_4764_);
lean_dec(v_a_4759_);
v___x_4765_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4766_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4767_ = lean_box(0);
v___x_4768_ = lean_box(v_hasTrace_4723_);
v___x_4769_ = lean_box(v___x_4757_);
v___f_4770_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4770_, 0, v___x_4768_);
lean_closure_set(v___f_4770_, 1, v___x_4769_);
lean_closure_set(v___f_4770_, 2, v_ctors_4764_);
lean_closure_set(v___f_4770_, 3, v___x_4767_);
v___x_4771_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4765_, v___x_4766_, v___f_4770_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4771_;
}
else
{
lean_object* v___x_4772_; lean_object* v___x_4774_; 
lean_dec(v_a_4759_);
v___x_4772_ = lean_box(0);
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 0, v___x_4772_);
v___x_4774_ = v___x_4761_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
else
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4784_; 
v_a_4777_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4779_ = v___x_4758_;
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4758_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4782_; 
if (v_isShared_4780_ == 0)
{
v___x_4782_ = v___x_4779_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
}
else
{
v___y_4678_ = v_hasTrace_4723_;
v___y_4679_ = v___x_4755_;
v___y_4680_ = v_options_4722_;
v___y_4681_ = v___x_4753_;
v___y_4682_ = v___x_4752_;
goto v___jp_4677_;
}
}
else
{
v___y_4678_ = v_hasTrace_4723_;
v___y_4679_ = v___x_4755_;
v___y_4680_ = v_options_4722_;
v___y_4681_ = v___x_4753_;
v___y_4682_ = v___x_4752_;
goto v___jp_4677_;
}
}
}
else
{
lean_dec_ref(v___f_4603_);
lean_dec(v_declName_4585_);
goto v___jp_4597_;
}
}
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec(v___x_4591_);
lean_dec(v_declName_4585_);
v_a_4790_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4592_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4592_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_){
_start:
{
lean_object* v_res_4804_; 
v_res_4804_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4805_, uint8_t v___x_4806_, lean_object* v_as_4807_, lean_object* v_as_x27_4808_, lean_object* v_b_4809_, lean_object* v_a_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_){
_start:
{
lean_object* v___x_4816_; 
v___x_4816_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4805_, v___x_4806_, v_as_x27_4808_, v_b_4809_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4817_, lean_object* v___x_4818_, lean_object* v_as_4819_, lean_object* v_as_x27_4820_, lean_object* v_b_4821_, lean_object* v_a_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
uint8_t v___y_20965__boxed_4828_; uint8_t v___x_20966__boxed_4829_; lean_object* v_res_4830_; 
v___y_20965__boxed_4828_ = lean_unbox(v___y_4817_);
v___x_20966__boxed_4829_ = lean_unbox(v___x_4818_);
v_res_4830_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_20965__boxed_4828_, v___x_20966__boxed_4829_, v_as_4819_, v_as_x27_4820_, v_b_4821_, v_a_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v_as_x27_4820_);
lean_dec(v_as_4819_);
return v_res_4830_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4871_ = lean_unsigned_to_nat(4172903888u);
v___x_4872_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4873_ = l_Lean_Name_num___override(v___x_4872_, v___x_4871_);
return v___x_4873_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4875_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4876_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4877_ = l_Lean_Name_str___override(v___x_4876_, v___x_4875_);
return v___x_4877_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4879_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4880_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4881_ = l_Lean_Name_str___override(v___x_4880_, v___x_4879_);
return v___x_4881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4882_ = lean_unsigned_to_nat(2u);
v___x_4883_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4884_ = l_Lean_Name_num___override(v___x_4883_, v___x_4882_);
return v___x_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4886_; uint8_t v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4886_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4887_ = 0;
v___x_4888_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4889_ = l_Lean_registerTraceClass(v___x_4886_, v___x_4887_, v___x_4888_);
return v___x_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4892_, lean_object* v_b_4893_){
_start:
{
lean_object* v_array_4894_; lean_object* v_start_4895_; lean_object* v_stop_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4909_; 
v_array_4894_ = lean_ctor_get(v_a_4892_, 0);
v_start_4895_ = lean_ctor_get(v_a_4892_, 1);
v_stop_4896_ = lean_ctor_get(v_a_4892_, 2);
v_isSharedCheck_4909_ = !lean_is_exclusive(v_a_4892_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4898_ = v_a_4892_;
v_isShared_4899_ = v_isSharedCheck_4909_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_stop_4896_);
lean_inc(v_start_4895_);
lean_inc(v_array_4894_);
lean_dec(v_a_4892_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4909_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
uint8_t v___x_4900_; 
v___x_4900_ = lean_nat_dec_lt(v_start_4895_, v_stop_4896_);
if (v___x_4900_ == 0)
{
lean_del_object(v___x_4898_);
lean_dec(v_stop_4896_);
lean_dec(v_start_4895_);
lean_dec_ref(v_array_4894_);
return v_b_4893_;
}
else
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4904_; 
v___x_4901_ = lean_unsigned_to_nat(1u);
v___x_4902_ = lean_nat_add(v_start_4895_, v___x_4901_);
lean_inc_ref(v_array_4894_);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 1, v___x_4902_);
v___x_4904_ = v___x_4898_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_array_4894_);
lean_ctor_set(v_reuseFailAlloc_4908_, 1, v___x_4902_);
lean_ctor_set(v_reuseFailAlloc_4908_, 2, v_stop_4896_);
v___x_4904_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = lean_array_fget(v_array_4894_, v_start_4895_);
lean_dec(v_start_4895_);
lean_dec_ref(v_array_4894_);
v___x_4906_ = lean_array_push(v_b_4893_, v___x_4905_);
v_a_4892_ = v___x_4904_;
v_b_4893_ = v___x_4906_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4910_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4911_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4911_);
return v___x_4912_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4913_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4914_ = lean_unsigned_to_nat(0u);
v___x_4915_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
lean_ctor_set(v___x_4915_, 1, v___x_4914_);
lean_ctor_set(v___x_4915_, 2, v___x_4914_);
lean_ctor_set(v___x_4915_, 3, v___x_4914_);
lean_ctor_set(v___x_4915_, 4, v___x_4913_);
lean_ctor_set(v___x_4915_, 5, v___x_4913_);
lean_ctor_set(v___x_4915_, 6, v___x_4913_);
lean_ctor_set(v___x_4915_, 7, v___x_4913_);
lean_ctor_set(v___x_4915_, 8, v___x_4913_);
lean_ctor_set(v___x_4915_, 9, v___x_4913_);
return v___x_4915_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4916_ = lean_box(1);
v___x_4917_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4918_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4918_);
lean_ctor_set(v___x_4919_, 1, v___x_4917_);
lean_ctor_set(v___x_4919_, 2, v___x_4916_);
return v___x_4919_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4921_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4922_ = l_Lean_stringToMessageData(v___x_4921_);
return v___x_4922_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4924_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4925_ = l_Lean_stringToMessageData(v___x_4924_);
return v___x_4925_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4928_ = l_Lean_stringToMessageData(v___x_4927_);
return v___x_4928_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
v___x_4930_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4931_ = l_Lean_stringToMessageData(v___x_4930_);
return v___x_4931_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; 
v___x_4933_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4934_ = l_Lean_stringToMessageData(v___x_4933_);
return v___x_4934_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4936_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4937_ = l_Lean_stringToMessageData(v___x_4936_);
return v___x_4937_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4940_ = l_Lean_stringToMessageData(v___x_4939_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4941_, lean_object* v_declHint_4942_, lean_object* v___y_4943_){
_start:
{
lean_object* v___x_4945_; lean_object* v_env_4946_; uint8_t v___x_4947_; 
v___x_4945_ = lean_st_ref_get(v___y_4943_);
v_env_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc_ref(v_env_4946_);
lean_dec(v___x_4945_);
v___x_4947_ = l_Lean_Name_isAnonymous(v_declHint_4942_);
if (v___x_4947_ == 0)
{
uint8_t v_isExporting_4948_; 
v_isExporting_4948_ = lean_ctor_get_uint8(v_env_4946_, sizeof(void*)*8);
if (v_isExporting_4948_ == 0)
{
lean_object* v___x_4949_; 
lean_dec_ref(v_env_4946_);
lean_dec(v_declHint_4942_);
v___x_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4949_, 0, v_msg_4941_);
return v___x_4949_;
}
else
{
lean_object* v___x_4950_; uint8_t v___x_4951_; 
lean_inc_ref(v_env_4946_);
v___x_4950_ = l_Lean_Environment_setExporting(v_env_4946_, v___x_4947_);
lean_inc(v_declHint_4942_);
lean_inc_ref(v___x_4950_);
v___x_4951_ = l_Lean_Environment_contains(v___x_4950_, v_declHint_4942_, v_isExporting_4948_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; 
lean_dec_ref(v___x_4950_);
lean_dec_ref(v_env_4946_);
lean_dec(v_declHint_4942_);
v___x_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4952_, 0, v_msg_4941_);
return v___x_4952_;
}
else
{
lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v_c_4958_; lean_object* v___x_4959_; 
v___x_4953_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4954_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4955_ = l_Lean_Options_empty;
v___x_4956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4950_);
lean_ctor_set(v___x_4956_, 1, v___x_4953_);
lean_ctor_set(v___x_4956_, 2, v___x_4954_);
lean_ctor_set(v___x_4956_, 3, v___x_4955_);
lean_inc(v_declHint_4942_);
v___x_4957_ = l_Lean_MessageData_ofConstName(v_declHint_4942_, v___x_4947_);
v_c_4958_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4958_, 0, v___x_4956_);
lean_ctor_set(v_c_4958_, 1, v___x_4957_);
v___x_4959_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4946_, v_declHint_4942_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
lean_dec_ref(v_env_4946_);
lean_dec(v_declHint_4942_);
v___x_4960_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4960_);
lean_ctor_set(v___x_4961_, 1, v_c_4958_);
v___x_4962_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4961_);
lean_ctor_set(v___x_4963_, 1, v___x_4962_);
v___x_4964_ = l_Lean_MessageData_note(v___x_4963_);
v___x_4965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4965_, 0, v_msg_4941_);
lean_ctor_set(v___x_4965_, 1, v___x_4964_);
v___x_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4965_);
return v___x_4966_;
}
else
{
lean_object* v_val_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_5002_; 
v_val_4967_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4969_ = v___x_4959_;
v_isShared_4970_ = v_isSharedCheck_5002_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_val_4967_);
lean_dec(v___x_4959_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_5002_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v_mod_4974_; uint8_t v___x_4975_; 
v___x_4971_ = lean_box(0);
v___x_4972_ = l_Lean_Environment_header(v_env_4946_);
lean_dec_ref(v_env_4946_);
v___x_4973_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4972_);
v_mod_4974_ = lean_array_get(v___x_4971_, v___x_4973_, v_val_4967_);
lean_dec(v_val_4967_);
lean_dec_ref(v___x_4973_);
v___x_4975_ = l_Lean_isPrivateName(v_declHint_4942_);
lean_dec(v_declHint_4942_);
if (v___x_4975_ == 0)
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4987_; 
v___x_4976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_4977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4976_);
lean_ctor_set(v___x_4977_, 1, v_c_4958_);
v___x_4978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_4979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4977_);
lean_ctor_set(v___x_4979_, 1, v___x_4978_);
v___x_4980_ = l_Lean_MessageData_ofName(v_mod_4974_);
v___x_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_4983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4981_);
lean_ctor_set(v___x_4983_, 1, v___x_4982_);
v___x_4984_ = l_Lean_MessageData_note(v___x_4983_);
v___x_4985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4985_, 0, v_msg_4941_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4985_);
v___x_4987_ = v___x_4969_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4985_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
else
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_5000_; 
v___x_4989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
lean_ctor_set(v___x_4990_, 1, v_c_4958_);
v___x_4991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l_Lean_MessageData_ofName(v_mod_4974_);
v___x_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4992_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_4996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4994_);
lean_ctor_set(v___x_4996_, 1, v___x_4995_);
v___x_4997_ = l_Lean_MessageData_note(v___x_4996_);
v___x_4998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4998_, 0, v_msg_4941_);
lean_ctor_set(v___x_4998_, 1, v___x_4997_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4998_);
v___x_5000_ = v___x_4969_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4998_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5003_; 
lean_dec_ref(v_env_4946_);
lean_dec(v_declHint_4942_);
v___x_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5003_, 0, v_msg_4941_);
return v___x_5003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_5004_, lean_object* v_declHint_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5004_, v_declHint_5005_, v___y_5006_);
lean_dec(v___y_5006_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_5009_, lean_object* v_declHint_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v___x_5016_; lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5026_; 
v___x_5016_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5009_, v_declHint_5010_, v___y_5014_);
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5019_ = v___x_5016_;
v_isShared_5020_ = v_isSharedCheck_5026_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5016_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5026_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5024_; 
v___x_5021_ = l_Lean_unknownIdentifierMessageTag;
v___x_5022_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
lean_ctor_set(v___x_5022_, 1, v_a_5017_);
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 0, v___x_5022_);
v___x_5024_ = v___x_5019_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5027_, lean_object* v_declHint_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5027_, v_declHint_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
return v_res_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5035_, lean_object* v_msg_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
lean_object* v_fileName_5042_; lean_object* v_fileMap_5043_; lean_object* v_options_5044_; lean_object* v_currRecDepth_5045_; lean_object* v_maxRecDepth_5046_; lean_object* v_ref_5047_; lean_object* v_currNamespace_5048_; lean_object* v_openDecls_5049_; lean_object* v_initHeartbeats_5050_; lean_object* v_maxHeartbeats_5051_; lean_object* v_quotContext_5052_; lean_object* v_currMacroScope_5053_; uint8_t v_diag_5054_; lean_object* v_cancelTk_x3f_5055_; uint8_t v_suppressElabErrors_5056_; lean_object* v_inheritedTraceOptions_5057_; lean_object* v_ref_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v_fileName_5042_ = lean_ctor_get(v___y_5039_, 0);
v_fileMap_5043_ = lean_ctor_get(v___y_5039_, 1);
v_options_5044_ = lean_ctor_get(v___y_5039_, 2);
v_currRecDepth_5045_ = lean_ctor_get(v___y_5039_, 3);
v_maxRecDepth_5046_ = lean_ctor_get(v___y_5039_, 4);
v_ref_5047_ = lean_ctor_get(v___y_5039_, 5);
v_currNamespace_5048_ = lean_ctor_get(v___y_5039_, 6);
v_openDecls_5049_ = lean_ctor_get(v___y_5039_, 7);
v_initHeartbeats_5050_ = lean_ctor_get(v___y_5039_, 8);
v_maxHeartbeats_5051_ = lean_ctor_get(v___y_5039_, 9);
v_quotContext_5052_ = lean_ctor_get(v___y_5039_, 10);
v_currMacroScope_5053_ = lean_ctor_get(v___y_5039_, 11);
v_diag_5054_ = lean_ctor_get_uint8(v___y_5039_, sizeof(void*)*14);
v_cancelTk_x3f_5055_ = lean_ctor_get(v___y_5039_, 12);
v_suppressElabErrors_5056_ = lean_ctor_get_uint8(v___y_5039_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5057_ = lean_ctor_get(v___y_5039_, 13);
v_ref_5058_ = l_Lean_replaceRef(v_ref_5035_, v_ref_5047_);
lean_inc_ref(v_inheritedTraceOptions_5057_);
lean_inc(v_cancelTk_x3f_5055_);
lean_inc(v_currMacroScope_5053_);
lean_inc(v_quotContext_5052_);
lean_inc(v_maxHeartbeats_5051_);
lean_inc(v_initHeartbeats_5050_);
lean_inc(v_openDecls_5049_);
lean_inc(v_currNamespace_5048_);
lean_inc(v_maxRecDepth_5046_);
lean_inc(v_currRecDepth_5045_);
lean_inc_ref(v_options_5044_);
lean_inc_ref(v_fileMap_5043_);
lean_inc_ref(v_fileName_5042_);
v___x_5059_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5059_, 0, v_fileName_5042_);
lean_ctor_set(v___x_5059_, 1, v_fileMap_5043_);
lean_ctor_set(v___x_5059_, 2, v_options_5044_);
lean_ctor_set(v___x_5059_, 3, v_currRecDepth_5045_);
lean_ctor_set(v___x_5059_, 4, v_maxRecDepth_5046_);
lean_ctor_set(v___x_5059_, 5, v_ref_5058_);
lean_ctor_set(v___x_5059_, 6, v_currNamespace_5048_);
lean_ctor_set(v___x_5059_, 7, v_openDecls_5049_);
lean_ctor_set(v___x_5059_, 8, v_initHeartbeats_5050_);
lean_ctor_set(v___x_5059_, 9, v_maxHeartbeats_5051_);
lean_ctor_set(v___x_5059_, 10, v_quotContext_5052_);
lean_ctor_set(v___x_5059_, 11, v_currMacroScope_5053_);
lean_ctor_set(v___x_5059_, 12, v_cancelTk_x3f_5055_);
lean_ctor_set(v___x_5059_, 13, v_inheritedTraceOptions_5057_);
lean_ctor_set_uint8(v___x_5059_, sizeof(void*)*14, v_diag_5054_);
lean_ctor_set_uint8(v___x_5059_, sizeof(void*)*14 + 1, v_suppressElabErrors_5056_);
v___x_5060_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5036_, v___y_5037_, v___y_5038_, v___x_5059_, v___y_5040_);
lean_dec_ref(v___x_5059_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5061_, lean_object* v_msg_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5061_, v_msg_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_);
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5065_);
lean_dec(v___y_5064_);
lean_dec_ref(v___y_5063_);
lean_dec(v_ref_5061_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5069_, lean_object* v_msg_5070_, lean_object* v_declHint_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v___x_5077_; lean_object* v_a_5078_; lean_object* v___x_5079_; 
v___x_5077_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5070_, v_declHint_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref(v___x_5077_);
v___x_5079_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5069_, v_a_5078_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
return v___x_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5080_, lean_object* v_msg_5081_, lean_object* v_declHint_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v_res_5088_; 
v_res_5088_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5080_, v_msg_5081_, v_declHint_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_);
lean_dec(v___y_5086_);
lean_dec_ref(v___y_5085_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v_ref_5080_);
return v_res_5088_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5090_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5091_ = l_Lean_stringToMessageData(v___x_5090_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5092_, lean_object* v_constName_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v___x_5099_; uint8_t v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5099_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5100_ = 0;
lean_inc(v_constName_5093_);
v___x_5101_ = l_Lean_MessageData_ofConstName(v_constName_5093_, v___x_5100_);
v___x_5102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5099_);
lean_ctor_set(v___x_5102_, 1, v___x_5101_);
v___x_5103_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5102_);
lean_ctor_set(v___x_5104_, 1, v___x_5103_);
v___x_5105_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5092_, v___x_5104_, v_constName_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5106_, lean_object* v_constName_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5106_, v_constName_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_);
lean_dec(v___y_5111_);
lean_dec_ref(v___y_5110_);
lean_dec(v___y_5109_);
lean_dec_ref(v___y_5108_);
lean_dec(v_ref_5106_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
lean_object* v_ref_5120_; lean_object* v___x_5121_; 
v_ref_5120_ = lean_ctor_get(v___y_5117_, 5);
v___x_5121_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5120_, v_constName_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v___x_5135_; lean_object* v_env_5136_; uint8_t v___x_5137_; lean_object* v___x_5138_; 
v___x_5135_ = lean_st_ref_get(v___y_5133_);
v_env_5136_ = lean_ctor_get(v___x_5135_, 0);
lean_inc_ref(v_env_5136_);
lean_dec(v___x_5135_);
v___x_5137_ = 0;
lean_inc(v_constName_5129_);
v___x_5138_ = l_Lean_Environment_find_x3f(v_env_5136_, v_constName_5129_, v___x_5137_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v___x_5139_; 
v___x_5139_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
return v___x_5139_;
}
else
{
lean_object* v_val_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5147_; 
lean_dec(v_constName_5129_);
v_val_5140_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5142_ = v___x_5138_;
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_val_5140_);
lean_dec(v___x_5138_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v___x_5145_; 
if (v_isShared_5143_ == 0)
{
lean_ctor_set_tag(v___x_5142_, 0);
v___x_5145_ = v___x_5142_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_val_5140_);
v___x_5145_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
return v___x_5145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_){
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5157_, lean_object* v_x_5158_, lean_object* v_x_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_){
_start:
{
if (lean_obj_tag(v_x_5157_) == 5)
{
lean_object* v_fn_5165_; lean_object* v_arg_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; 
v_fn_5165_ = lean_ctor_get(v_x_5157_, 0);
lean_inc_ref(v_fn_5165_);
v_arg_5166_ = lean_ctor_get(v_x_5157_, 1);
lean_inc_ref(v_arg_5166_);
lean_dec_ref(v_x_5157_);
v___x_5167_ = lean_array_set(v_x_5158_, v_x_5159_, v_arg_5166_);
v___x_5168_ = lean_unsigned_to_nat(1u);
v___x_5169_ = lean_nat_sub(v_x_5159_, v___x_5168_);
lean_dec(v_x_5159_);
v_x_5157_ = v_fn_5165_;
v_x_5158_ = v___x_5167_;
v_x_5159_ = v___x_5169_;
goto _start;
}
else
{
lean_dec(v_x_5159_);
if (lean_obj_tag(v_x_5157_) == 4)
{
lean_object* v_declName_5171_; lean_object* v___x_5172_; 
v_declName_5171_ = lean_ctor_get(v_x_5157_, 0);
lean_inc(v_declName_5171_);
lean_dec_ref(v_x_5157_);
v___x_5172_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5171_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5204_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5175_ = v___x_5172_;
v_isShared_5176_ = v_isSharedCheck_5204_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5172_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5204_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v_lower_5178_; lean_object* v_upper_5179_; 
if (lean_obj_tag(v_a_5173_) == 5)
{
lean_object* v_val_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5201_; 
v_val_5187_ = lean_ctor_get(v_a_5173_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v_a_5173_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5189_ = v_a_5173_;
v_isShared_5190_ = v_isSharedCheck_5201_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_val_5187_);
lean_dec(v_a_5173_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5201_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v_numParams_5191_; lean_object* v_numIndices_5192_; lean_object* v___x_5193_; uint8_t v___x_5194_; 
v_numParams_5191_ = lean_ctor_get(v_val_5187_, 1);
lean_inc(v_numParams_5191_);
v_numIndices_5192_ = lean_ctor_get(v_val_5187_, 2);
lean_inc(v_numIndices_5192_);
lean_dec_ref(v_val_5187_);
v___x_5193_ = lean_unsigned_to_nat(0u);
v___x_5194_ = lean_nat_dec_eq(v_numIndices_5192_, v___x_5193_);
lean_dec(v_numIndices_5192_);
if (v___x_5194_ == 0)
{
lean_object* v___x_5195_; uint8_t v___x_5196_; 
lean_del_object(v___x_5189_);
v___x_5195_ = lean_array_get_size(v_x_5158_);
v___x_5196_ = lean_nat_dec_le(v_numParams_5191_, v___x_5193_);
if (v___x_5196_ == 0)
{
v_lower_5178_ = v_numParams_5191_;
v_upper_5179_ = v___x_5195_;
goto v___jp_5177_;
}
else
{
lean_dec(v_numParams_5191_);
v_lower_5178_ = v___x_5193_;
v_upper_5179_ = v___x_5195_;
goto v___jp_5177_;
}
}
else
{
lean_object* v___x_5197_; lean_object* v___x_5199_; 
lean_dec(v_numParams_5191_);
lean_del_object(v___x_5175_);
lean_dec_ref(v_x_5158_);
v___x_5197_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5190_ == 0)
{
lean_ctor_set_tag(v___x_5189_, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5197_);
v___x_5199_ = v___x_5189_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v___x_5197_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
}
else
{
lean_object* v___x_5202_; lean_object* v___x_5203_; 
lean_del_object(v___x_5175_);
lean_dec(v_a_5173_);
lean_dec_ref(v_x_5158_);
v___x_5202_ = lean_box(0);
v___x_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5202_);
return v___x_5203_;
}
v___jp_5177_:
{
lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5185_; 
v___x_5180_ = l_Array_toSubarray___redArg(v_x_5158_, v_lower_5178_, v_upper_5179_);
v___x_5181_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5182_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5180_, v___x_5181_);
v___x_5183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5182_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 0, v___x_5183_);
v___x_5185_ = v___x_5175_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5186_; 
v_reuseFailAlloc_5186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5186_, 0, v___x_5183_);
v___x_5185_ = v_reuseFailAlloc_5186_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
return v___x_5185_;
}
}
}
}
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
lean_dec_ref(v_x_5158_);
v_a_5205_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5172_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5172_);
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
else
{
lean_object* v___x_5213_; lean_object* v___x_5214_; 
lean_dec_ref(v_x_5158_);
lean_dec_ref(v_x_5157_);
v___x_5213_ = lean_box(0);
v___x_5214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5214_, 0, v___x_5213_);
return v___x_5214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5215_, lean_object* v_x_5216_, lean_object* v_x_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v_res_5223_; 
v_res_5223_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5215_, v_x_5216_, v_x_5217_, v___y_5218_, v___y_5219_, v___y_5220_, v___y_5221_);
lean_dec(v___y_5221_);
lean_dec_ref(v___y_5220_);
lean_dec(v___y_5219_);
lean_dec_ref(v___y_5218_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
lean_object* v___x_5230_; 
lean_inc(v_a_5228_);
lean_inc_ref(v_a_5227_);
lean_inc(v_a_5226_);
lean_inc_ref(v_a_5225_);
v___x_5230_ = lean_infer_type(v_ctorApp_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5232_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_a_5231_);
lean_dec_ref(v___x_5230_);
v___x_5232_ = l_Lean_Meta_whnfD(v_a_5231_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; lean_object* v_dummy_5234_; lean_object* v_nargs_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc(v_a_5233_);
lean_dec_ref(v___x_5232_);
v_dummy_5234_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5235_ = l_Lean_Expr_getAppNumArgs(v_a_5233_);
lean_inc(v_nargs_5235_);
v___x_5236_ = lean_mk_array(v_nargs_5235_, v_dummy_5234_);
v___x_5237_ = lean_unsigned_to_nat(1u);
v___x_5238_ = lean_nat_sub(v_nargs_5235_, v___x_5237_);
lean_dec(v_nargs_5235_);
v___x_5239_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5233_, v___x_5236_, v___x_5238_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_);
return v___x_5239_;
}
else
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5247_; 
v_a_5240_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5242_ = v___x_5232_;
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v___x_5232_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5245_; 
if (v_isShared_5243_ == 0)
{
v___x_5245_ = v___x_5242_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_a_5240_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
}
}
else
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5255_; 
v_a_5248_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5250_ = v___x_5230_;
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5230_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5255_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v___x_5253_; 
if (v_isShared_5251_ == 0)
{
v___x_5253_ = v___x_5250_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_);
lean_dec(v_a_5260_);
lean_dec_ref(v_a_5259_);
lean_dec(v_a_5258_);
lean_dec_ref(v_a_5257_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5263_, lean_object* v_R_5264_, lean_object* v_a_5265_, lean_object* v_b_5266_){
_start:
{
lean_object* v___x_5267_; 
v___x_5267_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5265_, v_b_5266_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5268_, lean_object* v_constName_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
lean_object* v___x_5275_; 
v___x_5275_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
return v___x_5275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5276_, lean_object* v_constName_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v_res_5283_; 
v_res_5283_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5276_, v_constName_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5284_, lean_object* v_ref_5285_, lean_object* v_constName_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_){
_start:
{
lean_object* v___x_5292_; 
v___x_5292_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5285_, v_constName_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
return v___x_5292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5293_, lean_object* v_ref_5294_, lean_object* v_constName_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5293_, v_ref_5294_, v_constName_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec(v___y_5297_);
lean_dec_ref(v___y_5296_);
lean_dec(v_ref_5294_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5302_, lean_object* v_ref_5303_, lean_object* v_msg_5304_, lean_object* v_declHint_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v___x_5311_; 
v___x_5311_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5303_, v_msg_5304_, v_declHint_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_);
return v___x_5311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5312_, lean_object* v_ref_5313_, lean_object* v_msg_5314_, lean_object* v_declHint_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_){
_start:
{
lean_object* v_res_5321_; 
v_res_5321_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5312_, v_ref_5313_, v_msg_5314_, v_declHint_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v_ref_5313_);
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5322_, lean_object* v_declHint_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_){
_start:
{
lean_object* v___x_5329_; 
v___x_5329_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5322_, v_declHint_5323_, v___y_5327_);
return v___x_5329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5330_, lean_object* v_declHint_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5330_, v_declHint_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5338_, lean_object* v_ref_5339_, lean_object* v_msg_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_){
_start:
{
lean_object* v___x_5346_; 
v___x_5346_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5339_, v_msg_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_);
return v___x_5346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5347_, lean_object* v_ref_5348_, lean_object* v_msg_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5347_, v_ref_5348_, v_msg_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
lean_dec(v_ref_5348_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5356_, lean_object* v_body_5357_, lean_object* v_args2_5358_, lean_object* v_ctorVal_5359_, lean_object* v_args1_5360_, lean_object* v_k_5361_, lean_object* v_arg2_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_){
_start:
{
lean_object* v_res_5368_; 
v_res_5368_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5356_, v_body_5357_, v_args2_5358_, v_ctorVal_5359_, v_args1_5360_, v_k_5361_, v_arg2_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec_ref(v_body_5357_);
lean_dec(v_i_5356_);
return v_res_5368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5369_, lean_object* v_args1_5370_, lean_object* v_k_5371_, lean_object* v_i_5372_, lean_object* v_type_5373_, lean_object* v_args2_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_){
_start:
{
lean_object* v___x_5380_; uint8_t v___x_5381_; 
v___x_5380_ = lean_array_get_size(v_args1_5370_);
v___x_5381_ = lean_nat_dec_lt(v_i_5372_, v___x_5380_);
if (v___x_5381_ == 0)
{
lean_object* v___x_5382_; 
lean_dec_ref(v_type_5373_);
lean_dec(v_i_5372_);
lean_dec_ref(v_args1_5370_);
lean_dec_ref(v_ctorVal_5369_);
lean_inc(v_a_5378_);
lean_inc_ref(v_a_5377_);
lean_inc(v_a_5376_);
lean_inc_ref(v_a_5375_);
v___x_5382_ = lean_apply_6(v_k_5371_, v_args2_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, lean_box(0));
return v___x_5382_;
}
else
{
lean_object* v___x_5383_; 
lean_inc(v_a_5378_);
lean_inc_ref(v_a_5377_);
lean_inc(v_a_5376_);
lean_inc_ref(v_a_5375_);
v___x_5383_ = lean_whnf(v_type_5373_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_);
if (lean_obj_tag(v___x_5383_) == 0)
{
lean_object* v_a_5384_; 
v_a_5384_ = lean_ctor_get(v___x_5383_, 0);
lean_inc(v_a_5384_);
lean_dec_ref(v___x_5383_);
if (lean_obj_tag(v_a_5384_) == 7)
{
lean_object* v_binderName_5385_; lean_object* v_binderType_5386_; lean_object* v_body_5387_; lean_object* v___f_5388_; uint8_t v___x_5389_; uint8_t v___x_5390_; lean_object* v___x_5391_; 
v_binderName_5385_ = lean_ctor_get(v_a_5384_, 0);
lean_inc(v_binderName_5385_);
v_binderType_5386_ = lean_ctor_get(v_a_5384_, 1);
lean_inc_ref(v_binderType_5386_);
v_body_5387_ = lean_ctor_get(v_a_5384_, 2);
lean_inc_ref(v_body_5387_);
lean_dec_ref(v_a_5384_);
v___f_5388_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5388_, 0, v_i_5372_);
lean_closure_set(v___f_5388_, 1, v_body_5387_);
lean_closure_set(v___f_5388_, 2, v_args2_5374_);
lean_closure_set(v___f_5388_, 3, v_ctorVal_5369_);
lean_closure_set(v___f_5388_, 4, v_args1_5370_);
lean_closure_set(v___f_5388_, 5, v_k_5371_);
v___x_5389_ = 1;
v___x_5390_ = 0;
v___x_5391_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5385_, v___x_5389_, v_binderType_5386_, v___f_5388_, v___x_5390_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_);
return v___x_5391_;
}
else
{
lean_object* v_toConstantVal_5392_; lean_object* v_name_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; 
lean_dec(v_a_5384_);
lean_dec_ref(v_args2_5374_);
lean_dec(v_i_5372_);
lean_dec_ref(v_k_5371_);
lean_dec_ref(v_args1_5370_);
v_toConstantVal_5392_ = lean_ctor_get(v_ctorVal_5369_, 0);
lean_inc_ref(v_toConstantVal_5392_);
lean_dec_ref(v_ctorVal_5369_);
v_name_5393_ = lean_ctor_get(v_toConstantVal_5392_, 0);
lean_inc(v_name_5393_);
lean_dec_ref(v_toConstantVal_5392_);
v___x_5394_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5395_ = l_Lean_MessageData_ofName(v_name_5393_);
v___x_5396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5396_, 0, v___x_5394_);
lean_ctor_set(v___x_5396_, 1, v___x_5395_);
v___x_5397_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5398_, 0, v___x_5396_);
lean_ctor_set(v___x_5398_, 1, v___x_5397_);
v___x_5399_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5398_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_);
return v___x_5399_;
}
}
else
{
lean_object* v_a_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5407_; 
lean_dec_ref(v_args2_5374_);
lean_dec(v_i_5372_);
lean_dec_ref(v_k_5371_);
lean_dec_ref(v_args1_5370_);
lean_dec_ref(v_ctorVal_5369_);
v_a_5400_ = lean_ctor_get(v___x_5383_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5383_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5402_ = v___x_5383_;
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_a_5400_);
lean_dec(v___x_5383_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5405_; 
if (v_isShared_5403_ == 0)
{
v___x_5405_ = v___x_5402_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5400_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5408_, lean_object* v_body_5409_, lean_object* v_args2_5410_, lean_object* v_ctorVal_5411_, lean_object* v_args1_5412_, lean_object* v_k_5413_, lean_object* v_arg2_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_){
_start:
{
lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5420_ = lean_unsigned_to_nat(1u);
v___x_5421_ = lean_nat_add(v_i_5408_, v___x_5420_);
v___x_5422_ = lean_expr_instantiate1(v_body_5409_, v_arg2_5414_);
v___x_5423_ = lean_array_push(v_args2_5410_, v_arg2_5414_);
v___x_5424_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5411_, v_args1_5412_, v_k_5413_, v___x_5421_, v___x_5422_, v___x_5423_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
return v___x_5424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5425_, lean_object* v_args1_5426_, lean_object* v_k_5427_, lean_object* v_i_5428_, lean_object* v_type_5429_, lean_object* v_args2_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_){
_start:
{
lean_object* v_res_5436_; 
v_res_5436_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5425_, v_args1_5426_, v_k_5427_, v_i_5428_, v_type_5429_, v_args2_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_);
lean_dec(v_a_5434_);
lean_dec_ref(v_a_5433_);
lean_dec(v_a_5432_);
lean_dec_ref(v_a_5431_);
return v_res_5436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5437_, lean_object* v_us_5438_, lean_object* v_args1_5439_, lean_object* v___x_5440_, lean_object* v_numParams_5441_, lean_object* v___x_5442_, lean_object* v_args2_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; 
lean_inc(v_us_5438_);
v___x_5449_ = l_Lean_mkConst(v_name_5437_, v_us_5438_);
lean_inc_ref(v___x_5449_);
v___x_5450_ = l_Lean_mkAppN(v___x_5449_, v_args1_5439_);
v___x_5451_ = l_Lean_mkAppN(v___x_5449_, v_args2_5443_);
lean_inc_ref(v___x_5451_);
lean_inc_ref(v___x_5450_);
v___x_5452_ = l_Lean_Meta_mkEqHEq(v___x_5450_, v___x_5451_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
if (lean_obj_tag(v___x_5452_) == 0)
{
lean_object* v_a_5453_; lean_object* v___x_5454_; uint8_t v___x_5455_; lean_object* v___x_5456_; 
v_a_5453_ = lean_ctor_get(v___x_5452_, 0);
lean_inc(v_a_5453_);
lean_dec_ref(v___x_5452_);
lean_inc_ref_n(v_args2_5443_, 2);
v___x_5454_ = l_Array_toSubarray___redArg(v_args2_5443_, v___x_5440_, v_numParams_5441_);
v___x_5455_ = 1;
v___x_5456_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5439_, v_args2_5443_, v___x_5455_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_object* v_a_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5577_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5577_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5577_ == 0)
{
v___x_5459_ = v___x_5456_;
v_isShared_5460_ = v_isSharedCheck_5577_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_a_5457_);
lean_dec(v___x_5456_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5577_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v___x_5461_; 
v___x_5461_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5457_);
if (lean_obj_tag(v___x_5461_) == 1)
{
lean_object* v_val_5462_; lean_object* v___x_5463_; 
lean_del_object(v___x_5459_);
v_val_5462_ = lean_ctor_get(v___x_5461_, 0);
lean_inc(v_val_5462_);
lean_dec_ref(v___x_5461_);
v___x_5463_ = l_Lean_mkArrow(v_a_5453_, v_val_5462_, v___y_5446_, v___y_5447_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; lean_object* v___x_5465_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc(v_a_5464_);
lean_dec_ref(v___x_5463_);
v___x_5465_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5450_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5556_; 
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5556_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5556_ == 0)
{
v___x_5468_ = v___x_5465_;
v_isShared_5469_ = v_isSharedCheck_5556_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5465_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5556_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
if (lean_obj_tag(v_a_5466_) == 1)
{
lean_object* v_val_5470_; lean_object* v___x_5471_; 
lean_del_object(v___x_5468_);
v_val_5470_ = lean_ctor_get(v_a_5466_, 0);
lean_inc(v_val_5470_);
lean_dec_ref(v_a_5466_);
v___x_5471_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5451_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
if (lean_obj_tag(v___x_5471_) == 0)
{
lean_object* v_a_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5543_; 
v_a_5472_ = lean_ctor_get(v___x_5471_, 0);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5474_ = v___x_5471_;
v_isShared_5475_ = v_isSharedCheck_5543_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_a_5472_);
lean_dec(v___x_5471_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5543_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
if (lean_obj_tag(v_a_5472_) == 1)
{
lean_object* v_val_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5538_; 
lean_del_object(v___x_5474_);
v_val_5476_ = lean_ctor_get(v_a_5472_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v_a_5472_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5478_ = v_a_5472_;
v_isShared_5479_ = v_isSharedCheck_5538_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_val_5476_);
lean_dec(v_a_5472_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5538_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; uint8_t v___x_5484_; lean_object* v___x_5485_; 
v___x_5480_ = l_Subarray_copy___redArg(v___x_5442_);
v___x_5481_ = l_Array_append___redArg(v___x_5480_, v_val_5470_);
v___x_5482_ = l_Subarray_copy___redArg(v___x_5454_);
v___x_5483_ = l_Array_append___redArg(v___x_5482_, v_val_5476_);
lean_dec(v_val_5476_);
v___x_5484_ = 0;
v___x_5485_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5481_, v___x_5483_, v___x_5484_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
lean_dec_ref(v___x_5481_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v___x_5487_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc(v_a_5486_);
lean_dec_ref(v___x_5485_);
v___x_5487_ = l_Lean_mkArrowN(v_a_5486_, v_a_5464_, v___y_5446_, v___y_5447_);
lean_dec(v_a_5486_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v_a_5488_; uint8_t v___x_5489_; lean_object* v___x_5490_; 
v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_a_5488_);
lean_dec_ref(v___x_5487_);
v___x_5489_ = 1;
v___x_5490_ = l_Lean_Meta_mkForallFVars(v_args2_5443_, v_a_5488_, v___x_5484_, v___x_5455_, v___x_5455_, v___x_5489_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
lean_dec_ref(v_args2_5443_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; lean_object* v___x_5492_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref(v___x_5490_);
v___x_5492_ = l_Lean_Meta_mkForallFVars(v_args1_5439_, v_a_5491_, v___x_5484_, v___x_5455_, v___x_5455_, v___x_5489_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5505_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5495_ = v___x_5492_;
v_isShared_5496_ = v_isSharedCheck_5505_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v___x_5492_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5505_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5500_; 
v___x_5497_ = lean_array_get_size(v_val_5470_);
lean_dec(v_val_5470_);
v___x_5498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5498_, 0, v_a_5493_);
lean_ctor_set(v___x_5498_, 1, v_us_5438_);
lean_ctor_set(v___x_5498_, 2, v___x_5497_);
if (v_isShared_5479_ == 0)
{
lean_ctor_set(v___x_5478_, 0, v___x_5498_);
v___x_5500_ = v___x_5478_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5498_);
v___x_5500_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
lean_object* v___x_5502_; 
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 0, v___x_5500_);
v___x_5502_ = v___x_5495_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5500_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
}
else
{
lean_object* v_a_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5513_; 
lean_del_object(v___x_5478_);
lean_dec(v_val_5470_);
lean_dec(v_us_5438_);
v_a_5506_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5508_ = v___x_5492_;
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_a_5506_);
lean_dec(v___x_5492_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
lean_object* v___x_5511_; 
if (v_isShared_5509_ == 0)
{
v___x_5511_ = v___x_5508_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5506_);
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
lean_del_object(v___x_5478_);
lean_dec(v_val_5470_);
lean_dec(v_us_5438_);
v_a_5514_ = lean_ctor_get(v___x_5490_, 0);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5516_ = v___x_5490_;
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_a_5514_);
lean_dec(v___x_5490_);
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
lean_del_object(v___x_5478_);
lean_dec(v_val_5470_);
lean_dec_ref(v_args2_5443_);
lean_dec(v_us_5438_);
v_a_5522_ = lean_ctor_get(v___x_5487_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5487_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5524_ = v___x_5487_;
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_a_5522_);
lean_dec(v___x_5487_);
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
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5537_; 
lean_del_object(v___x_5478_);
lean_dec(v_val_5470_);
lean_dec(v_a_5464_);
lean_dec_ref(v_args2_5443_);
lean_dec(v_us_5438_);
v_a_5530_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5532_ = v___x_5485_;
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5485_);
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
}
else
{
lean_object* v___x_5539_; lean_object* v___x_5541_; 
lean_dec(v_a_5472_);
lean_dec(v_val_5470_);
lean_dec(v_a_5464_);
lean_dec_ref(v___x_5454_);
lean_dec_ref(v_args2_5443_);
lean_dec_ref(v___x_5442_);
lean_dec(v_us_5438_);
v___x_5539_ = lean_box(0);
if (v_isShared_5475_ == 0)
{
lean_ctor_set(v___x_5474_, 0, v___x_5539_);
v___x_5541_ = v___x_5474_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v___x_5539_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
return v___x_5541_;
}
}
}
}
else
{
lean_object* v_a_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5551_; 
lean_dec(v_val_5470_);
lean_dec(v_a_5464_);
lean_dec_ref(v___x_5454_);
lean_dec_ref(v_args2_5443_);
lean_dec_ref(v___x_5442_);
lean_dec(v_us_5438_);
v_a_5544_ = lean_ctor_get(v___x_5471_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5546_ = v___x_5471_;
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5471_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5549_; 
if (v_isShared_5547_ == 0)
{
v___x_5549_ = v___x_5546_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
v___x_5549_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
return v___x_5549_;
}
}
}
}
else
{
lean_object* v___x_5552_; lean_object* v___x_5554_; 
lean_dec(v_a_5466_);
lean_dec(v_a_5464_);
lean_dec_ref(v___x_5454_);
lean_dec_ref(v___x_5451_);
lean_dec_ref(v_args2_5443_);
lean_dec_ref(v___x_5442_);
lean_dec(v_us_5438_);
v___x_5552_ = lean_box(0);
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 0, v___x_5552_);
v___x_5554_ = v___x_5468_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5552_);
v___x_5554_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
return v___x_5554_;
}
}
}
}
else
{
lean_object* v_a_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5564_; 
lean_dec(v_a_5464_);
lean_dec_ref(v___x_5454_);
lean_dec_ref(v___x_5451_);
lean_dec_ref(v_args2_5443_);
lean_dec_ref(v___x_5442_);
lean_dec(v_us_5438_);
v_a_5557_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5564_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5564_ == 0)
{
v___x_5559_ = v___x_5465_;
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_a_5557_);
lean_dec(v___x_5465_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5562_; 
if (v_isShared_5560_ == 0)
{
v___x_5562_ = v___x_5559_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_a_5557_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
}
else
{
lean_object* v_a_5565_; lean_object* v___x_5567_; uint8_t v_isShared_5568_; uint8_t v_isSharedCheck_5572_; 
lean_dec_ref(v___x_5454_);
lean_dec_ref(v___x_5451_);
lean_dec_ref(v___x_5450_);
lean_dec_ref(v_args2_5443_);
lean_dec_ref(v___x_5442_);
lean_dec(v_us_5438_);
v_a_5565_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5567_ = v___x_5463_;
v_isShared_5568_ = v_isSharedCheck_5572_;
goto v_resetjp_5566_;
}
else
{
lean_inc(v_a_5565_);
lean_dec(v___x_5463_);
v___x_5567_ = lean_box(0);
v_isShared_5568_ = v_isSharedCheck_5572_;
goto v_resetjp_5566_;
}
v_resetjp_5566_:
{
lean_object* v___x_5570_; 
if (v_isShared_5568_ == 0)
{
v___x_5570_ = v___x_5567_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_a_5565_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
}
else
{
lean_object* v___x_5573_; lean_object* v___x_5575_; 
lean_dec(v___x_5461_);
lean_dec_ref(v___x_5454_);
lean_dec(v_a_5453_);
lean_dec_ref(v___x_5451_);
lean_dec_ref(v___x_5450_);
lean_dec_ref(v_args2_5443_);
lean_dec_ref(v___x_5442_);
lean_dec(v_us_5438_);
v___x_5573_ = lean_box(0);
if (v_isShared_5460_ == 0)
{
lean_ctor_set(v___x_5459_, 0, v___x_5573_);
v___x_5575_ = v___x_5459_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v___x_5573_);
v___x_5575_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
return v___x_5575_;
}
}
}
}
else
{
lean_object* v_a_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5585_; 
lean_dec_ref(v___x_5454_);
lean_dec(v_a_5453_);
lean_dec_ref(v___x_5451_);
lean_dec_ref(v___x_5450_);
lean_dec_ref(v_args2_5443_);
lean_dec_ref(v___x_5442_);
lean_dec(v_us_5438_);
v_a_5578_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5580_ = v___x_5456_;
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_a_5578_);
lean_dec(v___x_5456_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5581_ == 0)
{
v___x_5583_ = v___x_5580_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_a_5578_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
return v___x_5583_;
}
}
}
}
else
{
lean_object* v_a_5586_; lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5593_; 
lean_dec_ref(v___x_5451_);
lean_dec_ref(v___x_5450_);
lean_dec_ref(v_args2_5443_);
lean_dec_ref(v___x_5442_);
lean_dec(v_numParams_5441_);
lean_dec(v___x_5440_);
lean_dec(v_us_5438_);
v_a_5586_ = lean_ctor_get(v___x_5452_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5452_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5588_ = v___x_5452_;
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_a_5586_);
lean_dec(v___x_5452_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v___x_5591_; 
if (v_isShared_5589_ == 0)
{
v___x_5591_ = v___x_5588_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_a_5586_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5594_, lean_object* v_us_5595_, lean_object* v_args1_5596_, lean_object* v___x_5597_, lean_object* v_numParams_5598_, lean_object* v___x_5599_, lean_object* v_args2_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_){
_start:
{
lean_object* v_res_5606_; 
v_res_5606_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5594_, v_us_5595_, v_args1_5596_, v___x_5597_, v_numParams_5598_, v___x_5599_, v_args2_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec_ref(v_args1_5596_);
return v_res_5606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5607_, lean_object* v_name_5608_, lean_object* v_us_5609_, lean_object* v_ctorVal_5610_, lean_object* v_a_5611_, lean_object* v_args1_5612_, lean_object* v_x_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_){
_start:
{
lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___f_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v___x_5619_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5607_);
lean_inc_ref_n(v_args1_5612_, 3);
v___x_5620_ = l_Array_toSubarray___redArg(v_args1_5612_, v___x_5619_, v_numParams_5607_);
v___f_5621_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5621_, 0, v_name_5608_);
lean_closure_set(v___f_5621_, 1, v_us_5609_);
lean_closure_set(v___f_5621_, 2, v_args1_5612_);
lean_closure_set(v___f_5621_, 3, v___x_5619_);
lean_closure_set(v___f_5621_, 4, v_numParams_5607_);
lean_closure_set(v___f_5621_, 5, v___x_5620_);
v___x_5622_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5623_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5623_, 0, v_ctorVal_5610_);
lean_closure_set(v___x_5623_, 1, v_args1_5612_);
lean_closure_set(v___x_5623_, 2, v___f_5621_);
lean_closure_set(v___x_5623_, 3, v___x_5619_);
lean_closure_set(v___x_5623_, 4, v_a_5611_);
lean_closure_set(v___x_5623_, 5, v___x_5622_);
v___x_5624_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5612_, v___x_5623_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_);
return v___x_5624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5625_, lean_object* v_name_5626_, lean_object* v_us_5627_, lean_object* v_ctorVal_5628_, lean_object* v_a_5629_, lean_object* v_args1_5630_, lean_object* v_x_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_){
_start:
{
lean_object* v_res_5637_; 
v_res_5637_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5625_, v_name_5626_, v_us_5627_, v_ctorVal_5628_, v_a_5629_, v_args1_5630_, v_x_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec_ref(v_x_5631_);
return v_res_5637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_){
_start:
{
lean_object* v_toConstantVal_5644_; lean_object* v_numParams_5645_; lean_object* v_name_5646_; lean_object* v_levelParams_5647_; lean_object* v_type_5648_; lean_object* v___x_5649_; 
v_toConstantVal_5644_ = lean_ctor_get(v_ctorVal_5638_, 0);
v_numParams_5645_ = lean_ctor_get(v_ctorVal_5638_, 3);
lean_inc(v_numParams_5645_);
v_name_5646_ = lean_ctor_get(v_toConstantVal_5644_, 0);
lean_inc(v_name_5646_);
v_levelParams_5647_ = lean_ctor_get(v_toConstantVal_5644_, 1);
v_type_5648_ = lean_ctor_get(v_toConstantVal_5644_, 2);
lean_inc_ref(v_type_5648_);
v___x_5649_ = l_Lean_Meta_elimOptParam(v_type_5648_, v_a_5641_, v_a_5642_);
if (lean_obj_tag(v___x_5649_) == 0)
{
lean_object* v_a_5650_; lean_object* v___x_5651_; lean_object* v_us_5652_; lean_object* v___f_5653_; uint8_t v___x_5654_; lean_object* v___x_5655_; 
v_a_5650_ = lean_ctor_get(v___x_5649_, 0);
lean_inc_n(v_a_5650_, 2);
lean_dec_ref(v___x_5649_);
v___x_5651_ = lean_box(0);
lean_inc(v_levelParams_5647_);
v_us_5652_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5647_, v___x_5651_);
v___f_5653_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5653_, 0, v_numParams_5645_);
lean_closure_set(v___f_5653_, 1, v_name_5646_);
lean_closure_set(v___f_5653_, 2, v_us_5652_);
lean_closure_set(v___f_5653_, 3, v_ctorVal_5638_);
lean_closure_set(v___f_5653_, 4, v_a_5650_);
v___x_5654_ = 0;
v___x_5655_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5650_, v___f_5653_, v___x_5654_, v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_);
return v___x_5655_;
}
else
{
lean_object* v_a_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5663_; 
lean_dec(v_name_5646_);
lean_dec(v_numParams_5645_);
lean_dec_ref(v_ctorVal_5638_);
v_a_5656_ = lean_ctor_get(v___x_5649_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5649_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5658_ = v___x_5649_;
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_a_5656_);
lean_dec(v___x_5649_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___x_5661_; 
if (v_isShared_5659_ == 0)
{
v___x_5661_ = v___x_5658_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_){
_start:
{
lean_object* v_res_5670_; 
v_res_5670_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_);
lean_dec(v_a_5668_);
lean_dec_ref(v_a_5667_);
lean_dec(v_a_5666_);
lean_dec_ref(v_a_5665_);
return v_res_5670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5672_; lean_object* v___x_5673_; 
v___x_5672_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5673_ = l_Lean_stringToMessageData(v___x_5672_);
return v___x_5673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v_toConstantVal_5680_; lean_object* v_name_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; 
v_toConstantVal_5680_ = lean_ctor_get(v_ctorVal_5674_, 0);
lean_inc_ref(v_toConstantVal_5680_);
lean_dec_ref(v_ctorVal_5674_);
v_name_5681_ = lean_ctor_get(v_toConstantVal_5680_, 0);
lean_inc(v_name_5681_);
lean_dec_ref(v_toConstantVal_5680_);
v___x_5682_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5683_ = l_Lean_MessageData_ofName(v_name_5681_);
v___x_5684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5682_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5684_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
v___x_5687_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5686_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_);
return v___x_5687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_){
_start:
{
lean_object* v_res_5694_; 
v_res_5694_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5688_, v_a_5689_, v_a_5690_, v_a_5691_, v_a_5692_);
lean_dec(v_a_5692_);
lean_dec_ref(v_a_5691_);
lean_dec(v_a_5690_);
lean_dec_ref(v_a_5689_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5695_, lean_object* v_ctorVal_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_){
_start:
{
lean_object* v___x_5702_; 
v___x_5702_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5696_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_);
return v___x_5702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5703_, lean_object* v_ctorVal_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_){
_start:
{
lean_object* v_res_5710_; 
v_res_5710_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5703_, v_ctorVal_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_);
lean_dec(v_a_5708_);
lean_dec_ref(v_a_5707_);
lean_dec(v_a_5706_);
lean_dec_ref(v_a_5705_);
return v_res_5710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5716_, size_t v_sz_5717_, size_t v_i_5718_, lean_object* v_bs_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_){
_start:
{
uint8_t v___x_5725_; 
v___x_5725_ = lean_usize_dec_lt(v_i_5718_, v_sz_5717_);
if (v___x_5725_ == 0)
{
lean_object* v___x_5726_; 
lean_dec_ref(v_ctorVal_5716_);
v___x_5726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5726_, 0, v_bs_5719_);
return v___x_5726_;
}
else
{
lean_object* v_v_5727_; lean_object* v___x_5728_; 
v_v_5727_ = lean_array_uget_borrowed(v_bs_5719_, v_i_5718_);
lean_inc(v___y_5723_);
lean_inc_ref(v___y_5722_);
lean_inc(v___y_5721_);
lean_inc_ref(v___y_5720_);
lean_inc(v_v_5727_);
v___x_5728_ = lean_infer_type(v_v_5727_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
if (lean_obj_tag(v___x_5728_) == 0)
{
lean_object* v_a_5729_; lean_object* v___x_5730_; 
v_a_5729_ = lean_ctor_get(v___x_5728_, 0);
lean_inc(v_a_5729_);
lean_dec_ref(v___x_5728_);
v___x_5730_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5729_, v___y_5721_);
if (lean_obj_tag(v___x_5730_) == 0)
{
lean_object* v_a_5731_; lean_object* v___x_5732_; lean_object* v_bs_x27_5733_; lean_object* v_a_5735_; lean_object* v___y_5741_; lean_object* v_lhs_5752_; lean_object* v_rhs_5753_; lean_object* v___x_5755_; uint8_t v___x_5756_; 
v_a_5731_ = lean_ctor_get(v___x_5730_, 0);
lean_inc(v_a_5731_);
lean_dec_ref(v___x_5730_);
v___x_5732_ = lean_unsigned_to_nat(0u);
v_bs_x27_5733_ = lean_array_uset(v_bs_5719_, v_i_5718_, v___x_5732_);
v___x_5755_ = l_Lean_Expr_cleanupAnnotations(v_a_5731_);
v___x_5756_ = l_Lean_Expr_isApp(v___x_5755_);
if (v___x_5756_ == 0)
{
lean_object* v___x_5757_; 
lean_dec_ref(v___x_5755_);
lean_inc_ref(v_ctorVal_5716_);
v___x_5757_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5716_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
v___y_5741_ = v___x_5757_;
goto v___jp_5740_;
}
else
{
lean_object* v_arg_5758_; lean_object* v___x_5759_; uint8_t v___x_5760_; 
v_arg_5758_ = lean_ctor_get(v___x_5755_, 1);
lean_inc_ref(v_arg_5758_);
v___x_5759_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5755_);
v___x_5760_ = l_Lean_Expr_isApp(v___x_5759_);
if (v___x_5760_ == 0)
{
lean_object* v___x_5761_; 
lean_dec_ref(v___x_5759_);
lean_dec_ref(v_arg_5758_);
lean_inc_ref(v_ctorVal_5716_);
v___x_5761_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5716_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
v___y_5741_ = v___x_5761_;
goto v___jp_5740_;
}
else
{
lean_object* v_arg_5762_; lean_object* v___x_5763_; uint8_t v___x_5764_; 
v_arg_5762_ = lean_ctor_get(v___x_5759_, 1);
lean_inc_ref(v_arg_5762_);
v___x_5763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5759_);
v___x_5764_ = l_Lean_Expr_isApp(v___x_5763_);
if (v___x_5764_ == 0)
{
lean_object* v___x_5765_; 
lean_dec_ref(v___x_5763_);
lean_dec_ref(v_arg_5762_);
lean_dec_ref(v_arg_5758_);
lean_inc_ref(v_ctorVal_5716_);
v___x_5765_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5716_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
v___y_5741_ = v___x_5765_;
goto v___jp_5740_;
}
else
{
lean_object* v_arg_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; uint8_t v___x_5769_; 
v_arg_5766_ = lean_ctor_get(v___x_5763_, 1);
lean_inc_ref(v_arg_5766_);
v___x_5767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5763_);
v___x_5768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5769_ = l_Lean_Expr_isConstOf(v___x_5767_, v___x_5768_);
if (v___x_5769_ == 0)
{
uint8_t v___x_5770_; 
lean_dec_ref(v_arg_5762_);
v___x_5770_ = l_Lean_Expr_isApp(v___x_5767_);
if (v___x_5770_ == 0)
{
lean_object* v___x_5771_; 
lean_dec_ref(v___x_5767_);
lean_dec_ref(v_arg_5766_);
lean_dec_ref(v_arg_5758_);
lean_inc_ref(v_ctorVal_5716_);
v___x_5771_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5716_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
v___y_5741_ = v___x_5771_;
goto v___jp_5740_;
}
else
{
lean_object* v___x_5772_; lean_object* v___x_5773_; uint8_t v___x_5774_; 
v___x_5772_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5767_);
v___x_5773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5774_ = l_Lean_Expr_isConstOf(v___x_5772_, v___x_5773_);
lean_dec_ref(v___x_5772_);
if (v___x_5774_ == 0)
{
lean_object* v___x_5775_; 
lean_dec_ref(v_arg_5766_);
lean_dec_ref(v_arg_5758_);
lean_inc_ref(v_ctorVal_5716_);
v___x_5775_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5716_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_);
v___y_5741_ = v___x_5775_;
goto v___jp_5740_;
}
else
{
v_lhs_5752_ = v_arg_5766_;
v_rhs_5753_ = v_arg_5758_;
goto v___jp_5751_;
}
}
}
else
{
lean_dec_ref(v___x_5767_);
lean_dec_ref(v_arg_5766_);
v_lhs_5752_ = v_arg_5762_;
v_rhs_5753_ = v_arg_5758_;
goto v___jp_5751_;
}
}
}
}
v___jp_5734_:
{
size_t v___x_5736_; size_t v___x_5737_; lean_object* v___x_5738_; 
v___x_5736_ = ((size_t)1ULL);
v___x_5737_ = lean_usize_add(v_i_5718_, v___x_5736_);
v___x_5738_ = lean_array_uset(v_bs_x27_5733_, v_i_5718_, v_a_5735_);
v_i_5718_ = v___x_5737_;
v_bs_5719_ = v___x_5738_;
goto _start;
}
v___jp_5740_:
{
if (lean_obj_tag(v___y_5741_) == 0)
{
lean_object* v_a_5742_; 
v_a_5742_ = lean_ctor_get(v___y_5741_, 0);
lean_inc(v_a_5742_);
lean_dec_ref(v___y_5741_);
v_a_5735_ = v_a_5742_;
goto v___jp_5734_;
}
else
{
lean_object* v_a_5743_; lean_object* v___x_5745_; uint8_t v_isShared_5746_; uint8_t v_isSharedCheck_5750_; 
lean_dec_ref(v_bs_x27_5733_);
lean_dec_ref(v_ctorVal_5716_);
v_a_5743_ = lean_ctor_get(v___y_5741_, 0);
v_isSharedCheck_5750_ = !lean_is_exclusive(v___y_5741_);
if (v_isSharedCheck_5750_ == 0)
{
v___x_5745_ = v___y_5741_;
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
else
{
lean_inc(v_a_5743_);
lean_dec(v___y_5741_);
v___x_5745_ = lean_box(0);
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
v_resetjp_5744_:
{
lean_object* v___x_5748_; 
if (v_isShared_5746_ == 0)
{
v___x_5748_ = v___x_5745_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_a_5743_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
return v___x_5748_;
}
}
}
}
v___jp_5751_:
{
lean_object* v___x_5754_; 
v___x_5754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5754_, 0, v_lhs_5752_);
lean_ctor_set(v___x_5754_, 1, v_rhs_5753_);
v_a_5735_ = v___x_5754_;
goto v___jp_5734_;
}
}
else
{
lean_object* v_a_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5783_; 
lean_dec_ref(v_bs_5719_);
lean_dec_ref(v_ctorVal_5716_);
v_a_5776_ = lean_ctor_get(v___x_5730_, 0);
v_isSharedCheck_5783_ = !lean_is_exclusive(v___x_5730_);
if (v_isSharedCheck_5783_ == 0)
{
v___x_5778_ = v___x_5730_;
v_isShared_5779_ = v_isSharedCheck_5783_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_a_5776_);
lean_dec(v___x_5730_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5783_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v___x_5781_; 
if (v_isShared_5779_ == 0)
{
v___x_5781_ = v___x_5778_;
goto v_reusejp_5780_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v_a_5776_);
v___x_5781_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5780_;
}
v_reusejp_5780_:
{
return v___x_5781_;
}
}
}
}
else
{
lean_object* v_a_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5791_; 
lean_dec_ref(v_bs_5719_);
lean_dec_ref(v_ctorVal_5716_);
v_a_5784_ = lean_ctor_get(v___x_5728_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v___x_5728_);
if (v_isSharedCheck_5791_ == 0)
{
v___x_5786_ = v___x_5728_;
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_a_5784_);
lean_dec(v___x_5728_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5789_; 
if (v_isShared_5787_ == 0)
{
v___x_5789_ = v___x_5786_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
v___x_5789_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
return v___x_5789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5792_, lean_object* v_sz_5793_, lean_object* v_i_5794_, lean_object* v_bs_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_){
_start:
{
size_t v_sz_boxed_5801_; size_t v_i_boxed_5802_; lean_object* v_res_5803_; 
v_sz_boxed_5801_ = lean_unbox_usize(v_sz_5793_);
lean_dec(v_sz_5793_);
v_i_boxed_5802_ = lean_unbox_usize(v_i_5794_);
lean_dec(v_i_5794_);
v_res_5803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5792_, v_sz_boxed_5801_, v_i_boxed_5802_, v_bs_5795_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
return v_res_5803_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5805_; lean_object* v___x_5806_; 
v___x_5805_ = lean_unsigned_to_nat(0u);
v___x_5806_ = l_Lean_Level_ofNat(v___x_5805_);
return v___x_5806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5807_, lean_object* v_us_5808_, lean_object* v_numIndices_5809_, lean_object* v_xs_5810_, lean_object* v_type_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_){
_start:
{
lean_object* v_toConstantVal_5817_; lean_object* v_induct_5818_; lean_object* v_numParams_5819_; lean_object* v___x_5820_; lean_object* v_noConfusionName_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v_noConfusion_5825_; lean_object* v_noConfusion_5826_; lean_object* v_lower_5828_; lean_object* v_upper_5829_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v_n_5940_; uint8_t v___x_5941_; 
v_toConstantVal_5817_ = lean_ctor_get(v_ctorVal_5807_, 0);
v_induct_5818_ = lean_ctor_get(v_ctorVal_5807_, 1);
v_numParams_5819_ = lean_ctor_get(v_ctorVal_5807_, 3);
v___x_5820_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5818_);
v_noConfusionName_5821_ = l_Lean_Name_str___override(v_induct_5818_, v___x_5820_);
v___x_5822_ = lean_unsigned_to_nat(0u);
v___x_5823_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5824_, 0, v___x_5823_);
lean_ctor_set(v___x_5824_, 1, v_us_5808_);
v_noConfusion_5825_ = l_Lean_mkConst(v_noConfusionName_5821_, v___x_5824_);
v_noConfusion_5826_ = l_Lean_Expr_app___override(v_noConfusion_5825_, v_type_5811_);
v___x_5936_ = lean_array_get_size(v_xs_5810_);
v___x_5937_ = lean_nat_sub(v___x_5936_, v_numParams_5819_);
v___x_5938_ = lean_nat_sub(v___x_5937_, v_numIndices_5809_);
lean_dec(v___x_5937_);
v___x_5939_ = lean_unsigned_to_nat(1u);
v_n_5940_ = lean_nat_sub(v___x_5938_, v___x_5939_);
lean_dec(v___x_5938_);
v___x_5941_ = lean_nat_dec_le(v_n_5940_, v___x_5822_);
if (v___x_5941_ == 0)
{
v_lower_5828_ = v_n_5940_;
v_upper_5829_ = v___x_5936_;
goto v___jp_5827_;
}
else
{
lean_dec(v_n_5940_);
v_lower_5828_ = v___x_5822_;
v_upper_5829_ = v___x_5936_;
goto v___jp_5827_;
}
v___jp_5827_:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v_eqs_5832_; size_t v_sz_5833_; size_t v___x_5834_; lean_object* v___x_5835_; 
lean_inc_ref(v_xs_5810_);
v___x_5830_ = l_Array_toSubarray___redArg(v_xs_5810_, v_lower_5828_, v_upper_5829_);
v___x_5831_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5832_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5830_, v___x_5831_);
v_sz_5833_ = lean_array_size(v_eqs_5832_);
v___x_5834_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5832_);
lean_inc_ref(v_ctorVal_5807_);
v___x_5835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5807_, v_sz_5833_, v___x_5834_, v_eqs_5832_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
if (lean_obj_tag(v___x_5835_) == 0)
{
lean_object* v_a_5836_; lean_object* v___x_5837_; lean_object* v_fst_5838_; lean_object* v_snd_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; 
v_a_5836_ = lean_ctor_get(v___x_5835_, 0);
lean_inc(v_a_5836_);
lean_dec_ref(v___x_5835_);
v___x_5837_ = l_Array_unzip___redArg(v_a_5836_);
lean_dec(v_a_5836_);
v_fst_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_fst_5838_);
v_snd_5839_ = lean_ctor_get(v___x_5837_, 1);
lean_inc(v_snd_5839_);
lean_dec_ref(v___x_5837_);
v___x_5840_ = l_Lean_mkAppN(v_noConfusion_5826_, v_fst_5838_);
lean_dec(v_fst_5838_);
v___x_5841_ = l_Lean_mkAppN(v___x_5840_, v_snd_5839_);
lean_dec(v_snd_5839_);
v___x_5842_ = l_Lean_mkAppN(v___x_5841_, v_eqs_5832_);
lean_dec_ref(v_eqs_5832_);
lean_inc(v___y_5815_);
lean_inc_ref(v___y_5814_);
lean_inc(v___y_5813_);
lean_inc_ref(v___y_5812_);
lean_inc_ref(v___x_5842_);
v___x_5843_ = lean_infer_type(v___x_5842_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
if (lean_obj_tag(v___x_5843_) == 0)
{
lean_object* v_a_5844_; lean_object* v___x_5845_; 
v_a_5844_ = lean_ctor_get(v___x_5843_, 0);
lean_inc(v_a_5844_);
lean_dec_ref(v___x_5843_);
lean_inc(v___y_5815_);
lean_inc_ref(v___y_5814_);
lean_inc(v___y_5813_);
lean_inc_ref(v___y_5812_);
v___x_5845_ = lean_whnf(v_a_5844_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
if (lean_obj_tag(v___x_5845_) == 0)
{
lean_object* v_a_5846_; 
v_a_5846_ = lean_ctor_get(v___x_5845_, 0);
lean_inc(v_a_5846_);
lean_dec_ref(v___x_5845_);
if (lean_obj_tag(v_a_5846_) == 7)
{
lean_object* v_binderType_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; 
lean_inc_ref(v_toConstantVal_5817_);
lean_dec_ref(v_ctorVal_5807_);
v_binderType_5847_ = lean_ctor_get(v_a_5846_, 1);
lean_inc_ref(v_binderType_5847_);
lean_dec_ref(v_a_5846_);
v___x_5848_ = lean_box(0);
v___x_5849_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5847_, v___x_5848_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_object* v_a_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; 
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
lean_inc(v_a_5850_);
lean_dec_ref(v___x_5849_);
v___x_5851_ = l_Lean_Expr_mvarId_x21(v_a_5850_);
v___x_5852_ = l_Lean_MVarId_intros(v___x_5851_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
if (lean_obj_tag(v___x_5852_) == 0)
{
lean_object* v_a_5853_; lean_object* v_snd_5854_; lean_object* v_name_5855_; lean_object* v___x_5856_; 
v_a_5853_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_a_5853_);
lean_dec_ref(v___x_5852_);
v_snd_5854_ = lean_ctor_get(v_a_5853_, 1);
lean_inc(v_snd_5854_);
lean_dec(v_a_5853_);
v_name_5855_ = lean_ctor_get(v_toConstantVal_5817_, 0);
lean_inc(v_name_5855_);
lean_dec_ref(v_toConstantVal_5817_);
v___x_5856_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5854_, v_name_5855_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
if (lean_obj_tag(v___x_5856_) == 0)
{
lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v_a_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5886_; 
lean_dec_ref(v___x_5856_);
v___x_5857_ = l_Lean_Expr_app___override(v___x_5842_, v_a_5850_);
v___x_5858_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5857_, v___y_5813_);
v_a_5859_ = lean_ctor_get(v___x_5858_, 0);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5858_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5861_ = v___x_5858_;
v_isShared_5862_ = v_isSharedCheck_5886_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_a_5859_);
lean_dec(v___x_5858_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5886_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
uint8_t v___x_5863_; uint8_t v___x_5864_; uint8_t v___x_5865_; lean_object* v___x_5866_; 
v___x_5863_ = 0;
v___x_5864_ = 1;
v___x_5865_ = 1;
v___x_5866_ = l_Lean_Meta_mkLambdaFVars(v_xs_5810_, v_a_5859_, v___x_5863_, v___x_5864_, v___x_5863_, v___x_5864_, v___x_5865_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
lean_dec_ref(v_xs_5810_);
if (lean_obj_tag(v___x_5866_) == 0)
{
lean_object* v_a_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_5877_; 
v_a_5867_ = lean_ctor_get(v___x_5866_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5866_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5869_ = v___x_5866_;
v_isShared_5870_ = v_isSharedCheck_5877_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_a_5867_);
lean_dec(v___x_5866_);
v___x_5869_ = lean_box(0);
v_isShared_5870_ = v_isSharedCheck_5877_;
goto v_resetjp_5868_;
}
v_resetjp_5868_:
{
lean_object* v___x_5872_; 
if (v_isShared_5862_ == 0)
{
lean_ctor_set_tag(v___x_5861_, 1);
lean_ctor_set(v___x_5861_, 0, v_a_5867_);
v___x_5872_ = v___x_5861_;
goto v_reusejp_5871_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5867_);
v___x_5872_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5871_;
}
v_reusejp_5871_:
{
lean_object* v___x_5874_; 
if (v_isShared_5870_ == 0)
{
lean_ctor_set(v___x_5869_, 0, v___x_5872_);
v___x_5874_ = v___x_5869_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v___x_5872_);
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
lean_object* v_a_5878_; lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_5885_; 
lean_del_object(v___x_5861_);
v_a_5878_ = lean_ctor_get(v___x_5866_, 0);
v_isSharedCheck_5885_ = !lean_is_exclusive(v___x_5866_);
if (v_isSharedCheck_5885_ == 0)
{
v___x_5880_ = v___x_5866_;
v_isShared_5881_ = v_isSharedCheck_5885_;
goto v_resetjp_5879_;
}
else
{
lean_inc(v_a_5878_);
lean_dec(v___x_5866_);
v___x_5880_ = lean_box(0);
v_isShared_5881_ = v_isSharedCheck_5885_;
goto v_resetjp_5879_;
}
v_resetjp_5879_:
{
lean_object* v___x_5883_; 
if (v_isShared_5881_ == 0)
{
v___x_5883_ = v___x_5880_;
goto v_reusejp_5882_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v_a_5878_);
v___x_5883_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5882_;
}
v_reusejp_5882_:
{
return v___x_5883_;
}
}
}
}
}
else
{
lean_object* v_a_5887_; lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5894_; 
lean_dec(v_a_5850_);
lean_dec_ref(v___x_5842_);
lean_dec_ref(v_xs_5810_);
v_a_5887_ = lean_ctor_get(v___x_5856_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5856_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5889_ = v___x_5856_;
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
else
{
lean_inc(v_a_5887_);
lean_dec(v___x_5856_);
v___x_5889_ = lean_box(0);
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
v_resetjp_5888_:
{
lean_object* v___x_5892_; 
if (v_isShared_5890_ == 0)
{
v___x_5892_ = v___x_5889_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_a_5887_);
v___x_5892_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
return v___x_5892_;
}
}
}
}
else
{
lean_object* v_a_5895_; lean_object* v___x_5897_; uint8_t v_isShared_5898_; uint8_t v_isSharedCheck_5902_; 
lean_dec(v_a_5850_);
lean_dec_ref(v___x_5842_);
lean_dec_ref(v_toConstantVal_5817_);
lean_dec_ref(v_xs_5810_);
v_a_5895_ = lean_ctor_get(v___x_5852_, 0);
v_isSharedCheck_5902_ = !lean_is_exclusive(v___x_5852_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5897_ = v___x_5852_;
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
else
{
lean_inc(v_a_5895_);
lean_dec(v___x_5852_);
v___x_5897_ = lean_box(0);
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
v_resetjp_5896_:
{
lean_object* v___x_5900_; 
if (v_isShared_5898_ == 0)
{
v___x_5900_ = v___x_5897_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5895_);
v___x_5900_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
return v___x_5900_;
}
}
}
}
else
{
lean_object* v_a_5903_; lean_object* v___x_5905_; uint8_t v_isShared_5906_; uint8_t v_isSharedCheck_5910_; 
lean_dec_ref(v___x_5842_);
lean_dec_ref(v_toConstantVal_5817_);
lean_dec_ref(v_xs_5810_);
v_a_5903_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5910_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5910_ == 0)
{
v___x_5905_ = v___x_5849_;
v_isShared_5906_ = v_isSharedCheck_5910_;
goto v_resetjp_5904_;
}
else
{
lean_inc(v_a_5903_);
lean_dec(v___x_5849_);
v___x_5905_ = lean_box(0);
v_isShared_5906_ = v_isSharedCheck_5910_;
goto v_resetjp_5904_;
}
v_resetjp_5904_:
{
lean_object* v___x_5908_; 
if (v_isShared_5906_ == 0)
{
v___x_5908_ = v___x_5905_;
goto v_reusejp_5907_;
}
else
{
lean_object* v_reuseFailAlloc_5909_; 
v_reuseFailAlloc_5909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_a_5903_);
v___x_5908_ = v_reuseFailAlloc_5909_;
goto v_reusejp_5907_;
}
v_reusejp_5907_:
{
return v___x_5908_;
}
}
}
}
else
{
lean_object* v___x_5911_; 
lean_dec(v_a_5846_);
lean_dec_ref(v___x_5842_);
lean_dec_ref(v_xs_5810_);
v___x_5911_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5807_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
return v___x_5911_;
}
}
else
{
lean_object* v_a_5912_; lean_object* v___x_5914_; uint8_t v_isShared_5915_; uint8_t v_isSharedCheck_5919_; 
lean_dec_ref(v___x_5842_);
lean_dec_ref(v_xs_5810_);
lean_dec_ref(v_ctorVal_5807_);
v_a_5912_ = lean_ctor_get(v___x_5845_, 0);
v_isSharedCheck_5919_ = !lean_is_exclusive(v___x_5845_);
if (v_isSharedCheck_5919_ == 0)
{
v___x_5914_ = v___x_5845_;
v_isShared_5915_ = v_isSharedCheck_5919_;
goto v_resetjp_5913_;
}
else
{
lean_inc(v_a_5912_);
lean_dec(v___x_5845_);
v___x_5914_ = lean_box(0);
v_isShared_5915_ = v_isSharedCheck_5919_;
goto v_resetjp_5913_;
}
v_resetjp_5913_:
{
lean_object* v___x_5917_; 
if (v_isShared_5915_ == 0)
{
v___x_5917_ = v___x_5914_;
goto v_reusejp_5916_;
}
else
{
lean_object* v_reuseFailAlloc_5918_; 
v_reuseFailAlloc_5918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5918_, 0, v_a_5912_);
v___x_5917_ = v_reuseFailAlloc_5918_;
goto v_reusejp_5916_;
}
v_reusejp_5916_:
{
return v___x_5917_;
}
}
}
}
else
{
lean_object* v_a_5920_; lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_5927_; 
lean_dec_ref(v___x_5842_);
lean_dec_ref(v_xs_5810_);
lean_dec_ref(v_ctorVal_5807_);
v_a_5920_ = lean_ctor_get(v___x_5843_, 0);
v_isSharedCheck_5927_ = !lean_is_exclusive(v___x_5843_);
if (v_isSharedCheck_5927_ == 0)
{
v___x_5922_ = v___x_5843_;
v_isShared_5923_ = v_isSharedCheck_5927_;
goto v_resetjp_5921_;
}
else
{
lean_inc(v_a_5920_);
lean_dec(v___x_5843_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_5927_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v___x_5925_; 
if (v_isShared_5923_ == 0)
{
v___x_5925_ = v___x_5922_;
goto v_reusejp_5924_;
}
else
{
lean_object* v_reuseFailAlloc_5926_; 
v_reuseFailAlloc_5926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5926_, 0, v_a_5920_);
v___x_5925_ = v_reuseFailAlloc_5926_;
goto v_reusejp_5924_;
}
v_reusejp_5924_:
{
return v___x_5925_;
}
}
}
}
else
{
lean_object* v_a_5928_; lean_object* v___x_5930_; uint8_t v_isShared_5931_; uint8_t v_isSharedCheck_5935_; 
lean_dec_ref(v_eqs_5832_);
lean_dec_ref(v_noConfusion_5826_);
lean_dec_ref(v_xs_5810_);
lean_dec_ref(v_ctorVal_5807_);
v_a_5928_ = lean_ctor_get(v___x_5835_, 0);
v_isSharedCheck_5935_ = !lean_is_exclusive(v___x_5835_);
if (v_isSharedCheck_5935_ == 0)
{
v___x_5930_ = v___x_5835_;
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
else
{
lean_inc(v_a_5928_);
lean_dec(v___x_5835_);
v___x_5930_ = lean_box(0);
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
v_resetjp_5929_:
{
lean_object* v___x_5933_; 
if (v_isShared_5931_ == 0)
{
v___x_5933_ = v___x_5930_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
v___x_5933_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
return v___x_5933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5942_, lean_object* v_us_5943_, lean_object* v_numIndices_5944_, lean_object* v_xs_5945_, lean_object* v_type_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_){
_start:
{
lean_object* v_res_5952_; 
v_res_5952_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5942_, v_us_5943_, v_numIndices_5944_, v_xs_5945_, v_type_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
lean_dec(v___y_5948_);
lean_dec_ref(v___y_5947_);
lean_dec(v_numIndices_5944_);
return v_res_5952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5953_, lean_object* v_typeInfo_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_){
_start:
{
lean_object* v_thmType_5960_; lean_object* v_us_5961_; lean_object* v_numIndices_5962_; lean_object* v___f_5963_; uint8_t v___x_5964_; lean_object* v___x_5965_; 
v_thmType_5960_ = lean_ctor_get(v_typeInfo_5954_, 0);
lean_inc_ref(v_thmType_5960_);
v_us_5961_ = lean_ctor_get(v_typeInfo_5954_, 1);
lean_inc(v_us_5961_);
v_numIndices_5962_ = lean_ctor_get(v_typeInfo_5954_, 2);
lean_inc(v_numIndices_5962_);
lean_dec_ref(v_typeInfo_5954_);
v___f_5963_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5963_, 0, v_ctorVal_5953_);
lean_closure_set(v___f_5963_, 1, v_us_5961_);
lean_closure_set(v___f_5963_, 2, v_numIndices_5962_);
v___x_5964_ = 0;
v___x_5965_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5960_, v___f_5963_, v___x_5964_, v___x_5964_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_);
return v___x_5965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5966_, lean_object* v_typeInfo_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_){
_start:
{
lean_object* v_res_5973_; 
v_res_5973_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5966_, v_typeInfo_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_);
lean_dec(v_a_5971_);
lean_dec_ref(v_a_5970_);
lean_dec(v_a_5969_);
lean_dec_ref(v_a_5968_);
return v_res_5973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5976_){
_start:
{
lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5977_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5978_ = l_Lean_Name_str___override(v_ctorName_5976_, v___x_5977_);
return v___x_5978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5979_, lean_object* v_ctorVal_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_){
_start:
{
lean_object* v___x_5986_; 
lean_inc_ref(v_ctorVal_5980_);
v___x_5986_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5980_, v_a_5981_, v_a_5982_, v_a_5983_, v_a_5984_);
if (lean_obj_tag(v___x_5986_) == 0)
{
lean_object* v_a_5987_; lean_object* v___x_5989_; uint8_t v_isShared_5990_; uint8_t v_isSharedCheck_6048_; 
v_a_5987_ = lean_ctor_get(v___x_5986_, 0);
v_isSharedCheck_6048_ = !lean_is_exclusive(v___x_5986_);
if (v_isSharedCheck_6048_ == 0)
{
v___x_5989_ = v___x_5986_;
v_isShared_5990_ = v_isSharedCheck_6048_;
goto v_resetjp_5988_;
}
else
{
lean_inc(v_a_5987_);
lean_dec(v___x_5986_);
v___x_5989_ = lean_box(0);
v_isShared_5990_ = v_isSharedCheck_6048_;
goto v_resetjp_5988_;
}
v_resetjp_5988_:
{
if (lean_obj_tag(v_a_5987_) == 1)
{
lean_object* v_val_5991_; lean_object* v___x_5992_; 
lean_del_object(v___x_5989_);
v_val_5991_ = lean_ctor_get(v_a_5987_, 0);
lean_inc_n(v_val_5991_, 2);
lean_dec_ref(v_a_5987_);
lean_inc_ref(v_ctorVal_5980_);
v___x_5992_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5980_, v_val_5991_, v_a_5981_, v_a_5982_, v_a_5983_, v_a_5984_);
if (lean_obj_tag(v___x_5992_) == 0)
{
lean_object* v_a_5993_; lean_object* v___x_5995_; uint8_t v_isShared_5996_; uint8_t v_isSharedCheck_6035_; 
v_a_5993_ = lean_ctor_get(v___x_5992_, 0);
v_isSharedCheck_6035_ = !lean_is_exclusive(v___x_5992_);
if (v_isSharedCheck_6035_ == 0)
{
v___x_5995_ = v___x_5992_;
v_isShared_5996_ = v_isSharedCheck_6035_;
goto v_resetjp_5994_;
}
else
{
lean_inc(v_a_5993_);
lean_dec(v___x_5992_);
v___x_5995_ = lean_box(0);
v_isShared_5996_ = v_isSharedCheck_6035_;
goto v_resetjp_5994_;
}
v_resetjp_5994_:
{
if (lean_obj_tag(v_a_5993_) == 1)
{
lean_object* v_toConstantVal_5997_; lean_object* v_val_5998_; lean_object* v___x_6000_; uint8_t v_isShared_6001_; uint8_t v_isSharedCheck_6030_; 
v_toConstantVal_5997_ = lean_ctor_get(v_ctorVal_5980_, 0);
lean_inc_ref(v_toConstantVal_5997_);
lean_dec_ref(v_ctorVal_5980_);
v_val_5998_ = lean_ctor_get(v_a_5993_, 0);
v_isSharedCheck_6030_ = !lean_is_exclusive(v_a_5993_);
if (v_isSharedCheck_6030_ == 0)
{
v___x_6000_ = v_a_5993_;
v_isShared_6001_ = v_isSharedCheck_6030_;
goto v_resetjp_5999_;
}
else
{
lean_inc(v_val_5998_);
lean_dec(v_a_5993_);
v___x_6000_ = lean_box(0);
v_isShared_6001_ = v_isSharedCheck_6030_;
goto v_resetjp_5999_;
}
v_resetjp_5999_:
{
lean_object* v_levelParams_6002_; lean_object* v___x_6004_; uint8_t v_isShared_6005_; uint8_t v_isSharedCheck_6027_; 
v_levelParams_6002_ = lean_ctor_get(v_toConstantVal_5997_, 1);
v_isSharedCheck_6027_ = !lean_is_exclusive(v_toConstantVal_5997_);
if (v_isSharedCheck_6027_ == 0)
{
lean_object* v_unused_6028_; lean_object* v_unused_6029_; 
v_unused_6028_ = lean_ctor_get(v_toConstantVal_5997_, 2);
lean_dec(v_unused_6028_);
v_unused_6029_ = lean_ctor_get(v_toConstantVal_5997_, 0);
lean_dec(v_unused_6029_);
v___x_6004_ = v_toConstantVal_5997_;
v_isShared_6005_ = v_isSharedCheck_6027_;
goto v_resetjp_6003_;
}
else
{
lean_inc(v_levelParams_6002_);
lean_dec(v_toConstantVal_5997_);
v___x_6004_ = lean_box(0);
v_isShared_6005_ = v_isSharedCheck_6027_;
goto v_resetjp_6003_;
}
v_resetjp_6003_:
{
lean_object* v_thmType_6006_; lean_object* v___x_6008_; uint8_t v_isShared_6009_; uint8_t v_isSharedCheck_6024_; 
v_thmType_6006_ = lean_ctor_get(v_val_5991_, 0);
v_isSharedCheck_6024_ = !lean_is_exclusive(v_val_5991_);
if (v_isSharedCheck_6024_ == 0)
{
lean_object* v_unused_6025_; lean_object* v_unused_6026_; 
v_unused_6025_ = lean_ctor_get(v_val_5991_, 2);
lean_dec(v_unused_6025_);
v_unused_6026_ = lean_ctor_get(v_val_5991_, 1);
lean_dec(v_unused_6026_);
v___x_6008_ = v_val_5991_;
v_isShared_6009_ = v_isSharedCheck_6024_;
goto v_resetjp_6007_;
}
else
{
lean_inc(v_thmType_6006_);
lean_dec(v_val_5991_);
v___x_6008_ = lean_box(0);
v_isShared_6009_ = v_isSharedCheck_6024_;
goto v_resetjp_6007_;
}
v_resetjp_6007_:
{
lean_object* v___x_6011_; 
lean_inc(v_thmName_5979_);
if (v_isShared_6005_ == 0)
{
lean_ctor_set(v___x_6004_, 2, v_thmType_6006_);
lean_ctor_set(v___x_6004_, 0, v_thmName_5979_);
v___x_6011_ = v___x_6004_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_thmName_5979_);
lean_ctor_set(v_reuseFailAlloc_6023_, 1, v_levelParams_6002_);
lean_ctor_set(v_reuseFailAlloc_6023_, 2, v_thmType_6006_);
v___x_6011_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6015_; 
v___x_6012_ = lean_box(0);
v___x_6013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6013_, 0, v_thmName_5979_);
lean_ctor_set(v___x_6013_, 1, v___x_6012_);
if (v_isShared_6009_ == 0)
{
lean_ctor_set(v___x_6008_, 2, v___x_6013_);
lean_ctor_set(v___x_6008_, 1, v_val_5998_);
lean_ctor_set(v___x_6008_, 0, v___x_6011_);
v___x_6015_ = v___x_6008_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v___x_6011_);
lean_ctor_set(v_reuseFailAlloc_6022_, 1, v_val_5998_);
lean_ctor_set(v_reuseFailAlloc_6022_, 2, v___x_6013_);
v___x_6015_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
lean_object* v___x_6017_; 
if (v_isShared_6001_ == 0)
{
lean_ctor_set(v___x_6000_, 0, v___x_6015_);
v___x_6017_ = v___x_6000_;
goto v_reusejp_6016_;
}
else
{
lean_object* v_reuseFailAlloc_6021_; 
v_reuseFailAlloc_6021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6021_, 0, v___x_6015_);
v___x_6017_ = v_reuseFailAlloc_6021_;
goto v_reusejp_6016_;
}
v_reusejp_6016_:
{
lean_object* v___x_6019_; 
if (v_isShared_5996_ == 0)
{
lean_ctor_set(v___x_5995_, 0, v___x_6017_);
v___x_6019_ = v___x_5995_;
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
}
}
}
}
else
{
lean_object* v___x_6031_; lean_object* v___x_6033_; 
lean_dec(v_a_5993_);
lean_dec(v_val_5991_);
lean_dec_ref(v_ctorVal_5980_);
lean_dec(v_thmName_5979_);
v___x_6031_ = lean_box(0);
if (v_isShared_5996_ == 0)
{
lean_ctor_set(v___x_5995_, 0, v___x_6031_);
v___x_6033_ = v___x_5995_;
goto v_reusejp_6032_;
}
else
{
lean_object* v_reuseFailAlloc_6034_; 
v_reuseFailAlloc_6034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6034_, 0, v___x_6031_);
v___x_6033_ = v_reuseFailAlloc_6034_;
goto v_reusejp_6032_;
}
v_reusejp_6032_:
{
return v___x_6033_;
}
}
}
}
else
{
lean_object* v_a_6036_; lean_object* v___x_6038_; uint8_t v_isShared_6039_; uint8_t v_isSharedCheck_6043_; 
lean_dec(v_val_5991_);
lean_dec_ref(v_ctorVal_5980_);
lean_dec(v_thmName_5979_);
v_a_6036_ = lean_ctor_get(v___x_5992_, 0);
v_isSharedCheck_6043_ = !lean_is_exclusive(v___x_5992_);
if (v_isSharedCheck_6043_ == 0)
{
v___x_6038_ = v___x_5992_;
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
else
{
lean_inc(v_a_6036_);
lean_dec(v___x_5992_);
v___x_6038_ = lean_box(0);
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
v_resetjp_6037_:
{
lean_object* v___x_6041_; 
if (v_isShared_6039_ == 0)
{
v___x_6041_ = v___x_6038_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6042_; 
v_reuseFailAlloc_6042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6042_, 0, v_a_6036_);
v___x_6041_ = v_reuseFailAlloc_6042_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
return v___x_6041_;
}
}
}
}
else
{
lean_object* v___x_6044_; lean_object* v___x_6046_; 
lean_dec(v_a_5987_);
lean_dec_ref(v_ctorVal_5980_);
lean_dec(v_thmName_5979_);
v___x_6044_ = lean_box(0);
if (v_isShared_5990_ == 0)
{
lean_ctor_set(v___x_5989_, 0, v___x_6044_);
v___x_6046_ = v___x_5989_;
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
lean_object* v_a_6049_; lean_object* v___x_6051_; uint8_t v_isShared_6052_; uint8_t v_isSharedCheck_6056_; 
lean_dec_ref(v_ctorVal_5980_);
lean_dec(v_thmName_5979_);
v_a_6049_ = lean_ctor_get(v___x_5986_, 0);
v_isSharedCheck_6056_ = !lean_is_exclusive(v___x_5986_);
if (v_isSharedCheck_6056_ == 0)
{
v___x_6051_ = v___x_5986_;
v_isShared_6052_ = v_isSharedCheck_6056_;
goto v_resetjp_6050_;
}
else
{
lean_inc(v_a_6049_);
lean_dec(v___x_5986_);
v___x_6051_ = lean_box(0);
v_isShared_6052_ = v_isSharedCheck_6056_;
goto v_resetjp_6050_;
}
v_resetjp_6050_:
{
lean_object* v___x_6054_; 
if (v_isShared_6052_ == 0)
{
v___x_6054_ = v___x_6051_;
goto v_reusejp_6053_;
}
else
{
lean_object* v_reuseFailAlloc_6055_; 
v_reuseFailAlloc_6055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_a_6049_);
v___x_6054_ = v_reuseFailAlloc_6055_;
goto v_reusejp_6053_;
}
v_reusejp_6053_:
{
return v___x_6054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6057_, lean_object* v_ctorVal_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_){
_start:
{
lean_object* v_res_6064_; 
v_res_6064_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6057_, v_ctorVal_6058_, v_a_6059_, v_a_6060_, v_a_6061_, v_a_6062_);
lean_dec(v_a_6062_);
lean_dec_ref(v_a_6061_);
lean_dec(v_a_6060_);
lean_dec_ref(v_a_6059_);
return v_res_6064_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6065_, lean_object* v_n_6066_){
_start:
{
if (lean_obj_tag(v_n_6066_) == 1)
{
lean_object* v_pre_6067_; lean_object* v_str_6068_; lean_object* v___x_6069_; uint8_t v___x_6070_; 
v_pre_6067_ = lean_ctor_get(v_n_6066_, 0);
lean_inc(v_pre_6067_);
v_str_6068_ = lean_ctor_get(v_n_6066_, 1);
lean_inc_ref(v_str_6068_);
lean_dec_ref(v_n_6066_);
v___x_6069_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6070_ = lean_string_dec_eq(v_str_6068_, v___x_6069_);
lean_dec_ref(v_str_6068_);
if (v___x_6070_ == 0)
{
lean_dec(v_pre_6067_);
lean_dec_ref(v_env_6065_);
return v___x_6070_;
}
else
{
uint8_t v___x_6071_; lean_object* v___x_6072_; 
v___x_6071_ = 0;
v___x_6072_ = l_Lean_Environment_find_x3f(v_env_6065_, v_pre_6067_, v___x_6071_);
if (lean_obj_tag(v___x_6072_) == 1)
{
lean_object* v_val_6073_; 
v_val_6073_ = lean_ctor_get(v___x_6072_, 0);
lean_inc(v_val_6073_);
lean_dec_ref(v___x_6072_);
if (lean_obj_tag(v_val_6073_) == 6)
{
lean_dec_ref(v_val_6073_);
return v___x_6070_;
}
else
{
lean_dec(v_val_6073_);
return v___x_6071_;
}
}
else
{
lean_dec(v___x_6072_);
return v___x_6071_;
}
}
}
else
{
uint8_t v___x_6074_; 
lean_dec(v_n_6066_);
lean_dec_ref(v_env_6065_);
v___x_6074_ = 0;
return v___x_6074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6075_, lean_object* v_n_6076_){
_start:
{
uint8_t v_res_6077_; lean_object* v_r_6078_; 
v_res_6077_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6075_, v_n_6076_);
v_r_6078_ = lean_box(v_res_6077_);
return v_r_6078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6081_; lean_object* v___x_6082_; 
v___f_6081_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6082_ = l_Lean_registerReservedNamePredicate(v___f_6081_);
return v___x_6082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6083_){
_start:
{
lean_object* v_res_6084_; 
v_res_6084_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6084_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6085_, lean_object* v___y_6086_){
_start:
{
lean_object* v___x_6088_; lean_object* v_env_6089_; lean_object* v_toConstantVal_6090_; lean_object* v_value_6091_; lean_object* v_all_6092_; uint8_t v___y_6094_; lean_object* v_type_6102_; uint8_t v___x_6103_; 
v___x_6088_ = lean_st_ref_get(v___y_6086_);
v_env_6089_ = lean_ctor_get(v___x_6088_, 0);
lean_inc_ref_n(v_env_6089_, 2);
lean_dec(v___x_6088_);
v_toConstantVal_6090_ = lean_ctor_get(v_thm_6085_, 0);
v_value_6091_ = lean_ctor_get(v_thm_6085_, 1);
v_all_6092_ = lean_ctor_get(v_thm_6085_, 2);
v_type_6102_ = lean_ctor_get(v_toConstantVal_6090_, 2);
v___x_6103_ = l_Lean_Environment_hasUnsafe(v_env_6089_, v_type_6102_);
if (v___x_6103_ == 0)
{
uint8_t v___x_6104_; 
v___x_6104_ = l_Lean_Environment_hasUnsafe(v_env_6089_, v_value_6091_);
v___y_6094_ = v___x_6104_;
goto v___jp_6093_;
}
else
{
lean_dec_ref(v_env_6089_);
v___y_6094_ = v___x_6103_;
goto v___jp_6093_;
}
v___jp_6093_:
{
if (v___y_6094_ == 0)
{
lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6095_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6095_, 0, v_thm_6085_);
v___x_6096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6095_);
return v___x_6096_;
}
else
{
lean_object* v___x_6097_; uint8_t v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; 
lean_inc(v_all_6092_);
lean_inc_ref(v_value_6091_);
lean_inc_ref(v_toConstantVal_6090_);
lean_dec_ref(v_thm_6085_);
v___x_6097_ = lean_box(0);
v___x_6098_ = 0;
v___x_6099_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6099_, 0, v_toConstantVal_6090_);
lean_ctor_set(v___x_6099_, 1, v_value_6091_);
lean_ctor_set(v___x_6099_, 2, v___x_6097_);
lean_ctor_set(v___x_6099_, 3, v_all_6092_);
lean_ctor_set_uint8(v___x_6099_, sizeof(void*)*4, v___x_6098_);
v___x_6100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
v___x_6101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
return v___x_6101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_){
_start:
{
lean_object* v_res_6108_; 
v_res_6108_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6105_, v___y_6106_);
lean_dec(v___y_6106_);
return v_res_6108_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_){
_start:
{
lean_object* v___x_6115_; 
v___x_6115_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6109_, v___y_6113_);
return v___x_6115_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_){
_start:
{
lean_object* v_res_6122_; 
v_res_6122_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_);
lean_dec(v___y_6120_);
lean_dec_ref(v___y_6119_);
lean_dec(v___y_6118_);
lean_dec_ref(v___y_6117_);
return v_res_6122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6123_, uint8_t v___x_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_){
_start:
{
lean_object* v___x_6130_; lean_object* v_a_6131_; lean_object* v___x_6132_; 
v___x_6130_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6123_, v___y_6128_);
v_a_6131_ = lean_ctor_get(v___x_6130_, 0);
lean_inc(v_a_6131_);
lean_dec_ref(v___x_6130_);
v___x_6132_ = l_Lean_addDecl(v_a_6131_, v___x_6124_, v___y_6127_, v___y_6128_);
return v___x_6132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6133_, lean_object* v___x_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_){
_start:
{
uint8_t v___x_2122__boxed_6140_; lean_object* v_res_6141_; 
v___x_2122__boxed_6140_ = lean_unbox(v___x_6134_);
v_res_6141_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6133_, v___x_2122__boxed_6140_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec(v___y_6136_);
lean_dec_ref(v___y_6135_);
return v_res_6141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; 
v___x_6144_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6145_ = lean_unsigned_to_nat(0u);
v___x_6146_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6145_);
lean_ctor_set(v___x_6146_, 1, v___x_6145_);
lean_ctor_set(v___x_6146_, 2, v___x_6145_);
lean_ctor_set(v___x_6146_, 3, v___x_6145_);
lean_ctor_set(v___x_6146_, 4, v___x_6144_);
lean_ctor_set(v___x_6146_, 5, v___x_6144_);
lean_ctor_set(v___x_6146_, 6, v___x_6144_);
lean_ctor_set(v___x_6146_, 7, v___x_6144_);
lean_ctor_set(v___x_6146_, 8, v___x_6144_);
lean_ctor_set(v___x_6146_, 9, v___x_6144_);
return v___x_6146_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6147_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6148_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6147_);
lean_ctor_set(v___x_6148_, 1, v___x_6147_);
lean_ctor_set(v___x_6148_, 2, v___x_6147_);
lean_ctor_set(v___x_6148_, 3, v___x_6147_);
lean_ctor_set(v___x_6148_, 4, v___x_6147_);
lean_ctor_set(v___x_6148_, 5, v___x_6147_);
return v___x_6148_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6149_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6149_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
lean_ctor_set(v___x_6150_, 2, v___x_6149_);
lean_ctor_set(v___x_6150_, 3, v___x_6149_);
lean_ctor_set(v___x_6150_, 4, v___x_6149_);
return v___x_6150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6151_, lean_object* v_name_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_){
_start:
{
if (lean_obj_tag(v_name_6152_) == 1)
{
lean_object* v_pre_6164_; lean_object* v_str_6165_; lean_object* v___x_6166_; uint8_t v___x_6167_; 
v_pre_6164_ = lean_ctor_get(v_name_6152_, 0);
lean_inc(v_pre_6164_);
v_str_6165_ = lean_ctor_get(v_name_6152_, 1);
v___x_6166_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6167_ = lean_string_dec_eq(v_str_6165_, v___x_6166_);
if (v___x_6167_ == 0)
{
lean_dec(v_pre_6164_);
lean_dec_ref(v_name_6152_);
lean_dec(v___x_6151_);
goto v___jp_6160_;
}
else
{
lean_object* v___x_6168_; lean_object* v_env_6169_; uint8_t v___x_6170_; lean_object* v___x_6171_; 
v___x_6168_ = lean_st_ref_get(v___y_6154_);
v_env_6169_ = lean_ctor_get(v___x_6168_, 0);
lean_inc_ref(v_env_6169_);
lean_dec(v___x_6168_);
v___x_6170_ = 0;
lean_inc(v_pre_6164_);
v___x_6171_ = l_Lean_Environment_find_x3f(v_env_6169_, v_pre_6164_, v___x_6170_);
if (lean_obj_tag(v___x_6171_) == 1)
{
lean_object* v_val_6172_; 
v_val_6172_ = lean_ctor_get(v___x_6171_, 0);
lean_inc(v_val_6172_);
lean_dec_ref(v___x_6171_);
if (lean_obj_tag(v_val_6172_) == 6)
{
lean_object* v_val_6173_; lean_object* v___x_6175_; uint8_t v_isShared_6176_; uint8_t v_isSharedCheck_6223_; 
v_val_6173_ = lean_ctor_get(v_val_6172_, 0);
v_isSharedCheck_6223_ = !lean_is_exclusive(v_val_6172_);
if (v_isSharedCheck_6223_ == 0)
{
v___x_6175_ = v_val_6172_;
v_isShared_6176_ = v_isSharedCheck_6223_;
goto v_resetjp_6174_;
}
else
{
lean_inc(v_val_6173_);
lean_dec(v_val_6172_);
v___x_6175_ = lean_box(0);
v_isShared_6176_ = v_isSharedCheck_6223_;
goto v_resetjp_6174_;
}
v_resetjp_6174_:
{
uint8_t v___x_6177_; uint8_t v___x_6178_; uint8_t v___x_6179_; lean_object* v___x_6180_; uint64_t v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; uint8_t v_a_6195_; lean_object* v___x_6201_; 
v___x_6177_ = 1;
v___x_6178_ = 0;
v___x_6179_ = 2;
v___x_6180_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6180_, 0, v___x_6170_);
lean_ctor_set_uint8(v___x_6180_, 1, v___x_6170_);
lean_ctor_set_uint8(v___x_6180_, 2, v___x_6170_);
lean_ctor_set_uint8(v___x_6180_, 3, v___x_6170_);
lean_ctor_set_uint8(v___x_6180_, 4, v___x_6170_);
lean_ctor_set_uint8(v___x_6180_, 5, v___x_6167_);
lean_ctor_set_uint8(v___x_6180_, 6, v___x_6167_);
lean_ctor_set_uint8(v___x_6180_, 7, v___x_6170_);
lean_ctor_set_uint8(v___x_6180_, 8, v___x_6167_);
lean_ctor_set_uint8(v___x_6180_, 9, v___x_6177_);
lean_ctor_set_uint8(v___x_6180_, 10, v___x_6178_);
lean_ctor_set_uint8(v___x_6180_, 11, v___x_6167_);
lean_ctor_set_uint8(v___x_6180_, 12, v___x_6167_);
lean_ctor_set_uint8(v___x_6180_, 13, v___x_6167_);
lean_ctor_set_uint8(v___x_6180_, 14, v___x_6179_);
lean_ctor_set_uint8(v___x_6180_, 15, v___x_6167_);
lean_ctor_set_uint8(v___x_6180_, 16, v___x_6167_);
lean_ctor_set_uint8(v___x_6180_, 17, v___x_6167_);
lean_ctor_set_uint8(v___x_6180_, 18, v___x_6167_);
v___x_6181_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6180_);
v___x_6182_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6182_, 0, v___x_6180_);
lean_ctor_set_uint64(v___x_6182_, sizeof(void*)*1, v___x_6181_);
v___x_6183_ = lean_unsigned_to_nat(0u);
v___x_6184_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6185_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6186_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6187_ = lean_box(0);
lean_inc(v___x_6151_);
v___x_6188_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6188_, 0, v___x_6182_);
lean_ctor_set(v___x_6188_, 1, v___x_6151_);
lean_ctor_set(v___x_6188_, 2, v___x_6185_);
lean_ctor_set(v___x_6188_, 3, v___x_6186_);
lean_ctor_set(v___x_6188_, 4, v___x_6187_);
lean_ctor_set(v___x_6188_, 5, v___x_6183_);
lean_ctor_set(v___x_6188_, 6, v___x_6187_);
lean_ctor_set_uint8(v___x_6188_, sizeof(void*)*7, v___x_6170_);
lean_ctor_set_uint8(v___x_6188_, sizeof(void*)*7 + 1, v___x_6170_);
lean_ctor_set_uint8(v___x_6188_, sizeof(void*)*7 + 2, v___x_6170_);
lean_ctor_set_uint8(v___x_6188_, sizeof(void*)*7 + 3, v___x_6167_);
v___x_6189_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6190_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6191_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6189_);
lean_ctor_set(v___x_6192_, 1, v___x_6190_);
lean_ctor_set(v___x_6192_, 2, v___x_6151_);
lean_ctor_set(v___x_6192_, 3, v___x_6184_);
lean_ctor_set(v___x_6192_, 4, v___x_6191_);
v___x_6193_ = lean_st_mk_ref(v___x_6192_);
lean_inc_ref(v_name_6152_);
v___x_6201_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6152_, v_val_6173_, v___x_6188_, v___x_6193_, v___y_6153_, v___y_6154_);
if (lean_obj_tag(v___x_6201_) == 0)
{
lean_object* v_a_6202_; 
v_a_6202_ = lean_ctor_get(v___x_6201_, 0);
lean_inc(v_a_6202_);
lean_dec_ref(v___x_6201_);
if (lean_obj_tag(v_a_6202_) == 1)
{
lean_object* v_val_6203_; lean_object* v___x_6204_; lean_object* v___f_6205_; lean_object* v___x_6206_; 
v_val_6203_ = lean_ctor_get(v_a_6202_, 0);
lean_inc(v_val_6203_);
lean_dec_ref(v_a_6202_);
v___x_6204_ = lean_box(v___x_6170_);
v___f_6205_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6205_, 0, v_val_6203_);
lean_closure_set(v___f_6205_, 1, v___x_6204_);
v___x_6206_ = l_Lean_Meta_realizeConst(v_pre_6164_, v_name_6152_, v___f_6205_, v___x_6188_, v___x_6193_, v___y_6153_, v___y_6154_);
lean_dec_ref(v___x_6188_);
if (lean_obj_tag(v___x_6206_) == 0)
{
lean_dec_ref(v___x_6206_);
v_a_6195_ = v___x_6167_;
goto v___jp_6194_;
}
else
{
lean_object* v_a_6207_; lean_object* v___x_6209_; uint8_t v_isShared_6210_; uint8_t v_isSharedCheck_6214_; 
lean_dec(v___x_6193_);
lean_del_object(v___x_6175_);
v_a_6207_ = lean_ctor_get(v___x_6206_, 0);
v_isSharedCheck_6214_ = !lean_is_exclusive(v___x_6206_);
if (v_isSharedCheck_6214_ == 0)
{
v___x_6209_ = v___x_6206_;
v_isShared_6210_ = v_isSharedCheck_6214_;
goto v_resetjp_6208_;
}
else
{
lean_inc(v_a_6207_);
lean_dec(v___x_6206_);
v___x_6209_ = lean_box(0);
v_isShared_6210_ = v_isSharedCheck_6214_;
goto v_resetjp_6208_;
}
v_resetjp_6208_:
{
lean_object* v___x_6212_; 
if (v_isShared_6210_ == 0)
{
v___x_6212_ = v___x_6209_;
goto v_reusejp_6211_;
}
else
{
lean_object* v_reuseFailAlloc_6213_; 
v_reuseFailAlloc_6213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6213_, 0, v_a_6207_);
v___x_6212_ = v_reuseFailAlloc_6213_;
goto v_reusejp_6211_;
}
v_reusejp_6211_:
{
return v___x_6212_;
}
}
}
}
else
{
lean_dec(v_a_6202_);
lean_dec_ref(v___x_6188_);
lean_dec(v_pre_6164_);
lean_dec_ref(v_name_6152_);
v_a_6195_ = v___x_6170_;
goto v___jp_6194_;
}
}
else
{
lean_object* v_a_6215_; lean_object* v___x_6217_; uint8_t v_isShared_6218_; uint8_t v_isSharedCheck_6222_; 
lean_dec(v___x_6193_);
lean_dec_ref(v___x_6188_);
lean_del_object(v___x_6175_);
lean_dec_ref(v_name_6152_);
lean_dec(v_pre_6164_);
v_a_6215_ = lean_ctor_get(v___x_6201_, 0);
v_isSharedCheck_6222_ = !lean_is_exclusive(v___x_6201_);
if (v_isSharedCheck_6222_ == 0)
{
v___x_6217_ = v___x_6201_;
v_isShared_6218_ = v_isSharedCheck_6222_;
goto v_resetjp_6216_;
}
else
{
lean_inc(v_a_6215_);
lean_dec(v___x_6201_);
v___x_6217_ = lean_box(0);
v_isShared_6218_ = v_isSharedCheck_6222_;
goto v_resetjp_6216_;
}
v_resetjp_6216_:
{
lean_object* v___x_6220_; 
if (v_isShared_6218_ == 0)
{
v___x_6220_ = v___x_6217_;
goto v_reusejp_6219_;
}
else
{
lean_object* v_reuseFailAlloc_6221_; 
v_reuseFailAlloc_6221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6221_, 0, v_a_6215_);
v___x_6220_ = v_reuseFailAlloc_6221_;
goto v_reusejp_6219_;
}
v_reusejp_6219_:
{
return v___x_6220_;
}
}
}
v___jp_6194_:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6199_; 
v___x_6196_ = lean_st_ref_get(v___x_6193_);
lean_dec(v___x_6193_);
lean_dec(v___x_6196_);
v___x_6197_ = lean_box(v_a_6195_);
if (v_isShared_6176_ == 0)
{
lean_ctor_set_tag(v___x_6175_, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6197_);
v___x_6199_ = v___x_6175_;
goto v_reusejp_6198_;
}
else
{
lean_object* v_reuseFailAlloc_6200_; 
v_reuseFailAlloc_6200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6200_, 0, v___x_6197_);
v___x_6199_ = v_reuseFailAlloc_6200_;
goto v_reusejp_6198_;
}
v_reusejp_6198_:
{
return v___x_6199_;
}
}
}
}
else
{
lean_dec(v_val_6172_);
lean_dec_ref(v_name_6152_);
lean_dec(v_pre_6164_);
lean_dec(v___x_6151_);
goto v___jp_6156_;
}
}
else
{
lean_dec(v___x_6171_);
lean_dec_ref(v_name_6152_);
lean_dec(v_pre_6164_);
lean_dec(v___x_6151_);
goto v___jp_6156_;
}
}
}
else
{
lean_dec(v_name_6152_);
lean_dec(v___x_6151_);
goto v___jp_6160_;
}
v___jp_6156_:
{
uint8_t v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; 
v___x_6157_ = 0;
v___x_6158_ = lean_box(v___x_6157_);
v___x_6159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6158_);
return v___x_6159_;
}
v___jp_6160_:
{
uint8_t v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; 
v___x_6161_ = 0;
v___x_6162_ = lean_box(v___x_6161_);
v___x_6163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6163_, 0, v___x_6162_);
return v___x_6163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6224_, lean_object* v_name_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_){
_start:
{
lean_object* v_res_6229_; 
v_res_6229_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6224_, v_name_6225_, v___y_6226_, v___y_6227_);
lean_dec(v___y_6227_);
lean_dec_ref(v___y_6226_);
return v_res_6229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6233_; lean_object* v___x_6234_; 
v___f_6233_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6234_ = l_Lean_registerReservedNameAction(v___f_6233_);
return v___x_6234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6235_){
_start:
{
lean_object* v_res_6236_; 
v_res_6236_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6236_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Injective(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
