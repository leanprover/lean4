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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
v___x_213_ = lean_st_ref_put(v_a_207_, v___x_212_);
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
lean_object* v___y_254_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; uint8_t v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v_fileName_284_; lean_object* v_fileMap_285_; lean_object* v_options_286_; lean_object* v_currRecDepth_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ref_289_; lean_object* v_currNamespace_290_; lean_object* v_openDecls_291_; lean_object* v_initHeartbeats_292_; lean_object* v_maxHeartbeats_293_; lean_object* v_quotContext_294_; lean_object* v_currMacroScope_295_; uint8_t v_diag_296_; lean_object* v_cancelTk_x3f_297_; uint8_t v_suppressElabErrors_298_; lean_object* v_inheritedTraceOptions_299_; 
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
v___x_281_ = lean_nat_add(v___y_277_, v___x_280_);
lean_inc_ref(v___y_276_);
lean_inc(v___y_279_);
lean_inc(v___y_268_);
lean_inc(v___y_274_);
lean_inc(v___y_275_);
lean_inc(v___y_264_);
lean_inc(v___y_270_);
lean_inc(v___y_266_);
lean_inc(v___y_278_);
lean_inc_ref(v___y_271_);
lean_inc_ref(v___y_273_);
lean_inc_ref(v___y_265_);
v___x_282_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_282_, 0, v___y_265_);
lean_ctor_set(v___x_282_, 1, v___y_273_);
lean_ctor_set(v___x_282_, 2, v___y_271_);
lean_ctor_set(v___x_282_, 3, v___x_281_);
lean_ctor_set(v___x_282_, 4, v___y_278_);
lean_ctor_set(v___x_282_, 5, v___y_269_);
lean_ctor_set(v___x_282_, 6, v___y_266_);
lean_ctor_set(v___x_282_, 7, v___y_270_);
lean_ctor_set(v___x_282_, 8, v___y_264_);
lean_ctor_set(v___x_282_, 9, v___y_275_);
lean_ctor_set(v___x_282_, 10, v___y_274_);
lean_ctor_set(v___x_282_, 11, v___y_268_);
lean_ctor_set(v___x_282_, 12, v___y_279_);
lean_ctor_set(v___x_282_, 13, v___y_276_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14, v___y_267_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14 + 1, v___y_272_);
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
v___y_264_ = v_initHeartbeats_292_;
v___y_265_ = v_fileName_284_;
v___y_266_ = v_currNamespace_290_;
v___y_267_ = v_diag_296_;
v___y_268_ = v_currMacroScope_295_;
v___y_269_ = v_ref_289_;
v___y_270_ = v_openDecls_291_;
v___y_271_ = v_options_286_;
v___y_272_ = v_suppressElabErrors_298_;
v___y_273_ = v_fileMap_285_;
v___y_274_ = v_quotContext_294_;
v___y_275_ = v_maxHeartbeats_293_;
v___y_276_ = v_inheritedTraceOptions_299_;
v___y_277_ = v_currRecDepth_287_;
v___y_278_ = v_maxRecDepth_288_;
v___y_279_ = v_cancelTk_x3f_297_;
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
v___y_264_ = v_initHeartbeats_292_;
v___y_265_ = v_fileName_284_;
v___y_266_ = v_currNamespace_290_;
v___y_267_ = v_diag_296_;
v___y_268_ = v_currMacroScope_295_;
v___y_269_ = v_ref_289_;
v___y_270_ = v_openDecls_291_;
v___y_271_ = v_options_286_;
v___y_272_ = v_suppressElabErrors_298_;
v___y_273_ = v_fileMap_285_;
v___y_274_ = v_quotContext_294_;
v___y_275_ = v_maxHeartbeats_293_;
v___y_276_ = v_inheritedTraceOptions_299_;
v___y_277_ = v_currRecDepth_287_;
v___y_278_ = v_maxRecDepth_288_;
v___y_279_ = v_cancelTk_x3f_297_;
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
lean_dec_ref_known(v___x_383_, 1);
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
lean_dec_ref_known(v_x_401_, 2);
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
lean_dec_ref_known(v___x_414_, 1);
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
lean_dec_ref_known(v___x_418_, 1);
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
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Core_checkSystem(v___x_430_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v___x_439_; 
lean_dec_ref_known(v___x_438_, 1);
lean_inc_ref(v_pre_431_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc_ref(v_e_432_);
v___x_439_ = lean_apply_4(v_pre_431_, v_e_432_, v___y_435_, v___y_436_, lean_box(0));
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_555_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_555_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_555_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_555_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___y_445_; 
switch(lean_obj_tag(v_a_440_))
{
case 0:
{
lean_object* v_e_545_; lean_object* v___x_547_; 
lean_dec_ref(v_post_433_);
lean_dec_ref(v_e_432_);
lean_dec_ref(v_pre_431_);
v_e_545_ = lean_ctor_get(v_a_440_, 0);
lean_inc_ref(v_e_545_);
lean_dec_ref_known(v_a_440_, 1);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v_e_545_);
v___x_547_ = v___x_442_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_e_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
case 1:
{
lean_object* v_e_549_; lean_object* v___x_550_; 
lean_del_object(v___x_442_);
lean_dec_ref(v_e_432_);
v_e_549_ = lean_ctor_get(v_a_440_, 0);
lean_inc_ref(v_e_549_);
lean_dec_ref_known(v_a_440_, 1);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_550_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_e_549_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v_a_551_, v___y_434_, v___y_435_, v___y_436_);
return v___x_552_;
}
else
{
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_550_;
}
}
default: 
{
lean_object* v_e_x3f_553_; 
lean_del_object(v___x_442_);
v_e_x3f_553_ = lean_ctor_get(v_a_440_, 0);
lean_inc(v_e_x3f_553_);
lean_dec_ref_known(v_a_440_, 1);
if (lean_obj_tag(v_e_x3f_553_) == 0)
{
v___y_445_ = v_e_432_;
goto v___jp_444_;
}
else
{
lean_object* v_val_554_; 
lean_dec_ref(v_e_432_);
v_val_554_ = lean_ctor_get(v_e_x3f_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v_e_x3f_553_, 1);
v___y_445_ = v_val_554_;
goto v___jp_444_;
}
}
}
v___jp_444_:
{
switch(lean_obj_tag(v___y_445_))
{
case 7:
{
lean_object* v_binderName_446_; lean_object* v_binderType_447_; lean_object* v_body_448_; uint8_t v_binderInfo_449_; lean_object* v___x_450_; 
v_binderName_446_ = lean_ctor_get(v___y_445_, 0);
v_binderType_447_ = lean_ctor_get(v___y_445_, 1);
v_body_448_ = lean_ctor_get(v___y_445_, 2);
v_binderInfo_449_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_447_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_binderType_447_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_452_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
lean_inc_ref(v_body_448_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_452_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_448_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; size_t v___x_454_; size_t v___x_455_; uint8_t v___x_456_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v___x_454_ = lean_ptr_addr(v_binderType_447_);
v___x_455_ = lean_ptr_addr(v_a_451_);
v___x_456_ = lean_usize_dec_eq(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_inc(v_binderName_446_);
lean_dec_ref_known(v___y_445_, 3);
v___x_457_ = l_Lean_Expr_forallE___override(v_binderName_446_, v_a_451_, v_a_453_, v_binderInfo_449_);
v___x_458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_457_, v___y_434_, v___y_435_, v___y_436_);
return v___x_458_;
}
else
{
size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_ptr_addr(v_body_448_);
v___x_460_ = lean_ptr_addr(v_a_453_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc(v_binderName_446_);
lean_dec_ref_known(v___y_445_, 3);
v___x_462_ = l_Lean_Expr_forallE___override(v_binderName_446_, v_a_451_, v_a_453_, v_binderInfo_449_);
v___x_463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_462_, v___y_434_, v___y_435_, v___y_436_);
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_449_, v_binderInfo_449_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_inc(v_binderName_446_);
lean_dec_ref_known(v___y_445_, 3);
v___x_465_ = l_Lean_Expr_forallE___override(v_binderName_446_, v_a_451_, v_a_453_, v_binderInfo_449_);
v___x_466_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_465_, v___y_434_, v___y_435_, v___y_436_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; 
lean_dec(v_a_453_);
lean_dec(v_a_451_);
v___x_467_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_445_, v___y_434_, v___y_435_, v___y_436_);
return v___x_467_;
}
}
}
}
else
{
lean_dec(v_a_451_);
lean_dec_ref_known(v___y_445_, 3);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_452_;
}
}
else
{
lean_dec_ref_known(v___y_445_, 3);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_450_;
}
}
case 6:
{
lean_object* v_binderName_468_; lean_object* v_binderType_469_; lean_object* v_body_470_; uint8_t v_binderInfo_471_; lean_object* v___x_472_; 
v_binderName_468_ = lean_ctor_get(v___y_445_, 0);
v_binderType_469_ = lean_ctor_get(v___y_445_, 1);
v_body_470_ = lean_ctor_get(v___y_445_, 2);
v_binderInfo_471_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_469_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_binderType_469_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
lean_inc_ref(v_body_470_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_474_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_470_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; size_t v___x_476_; size_t v___x_477_; uint8_t v___x_478_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = lean_ptr_addr(v_binderType_469_);
v___x_477_ = lean_ptr_addr(v_a_473_);
v___x_478_ = lean_usize_dec_eq(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_inc(v_binderName_468_);
lean_dec_ref_known(v___y_445_, 3);
v___x_479_ = l_Lean_Expr_lam___override(v_binderName_468_, v_a_473_, v_a_475_, v_binderInfo_471_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_479_, v___y_434_, v___y_435_, v___y_436_);
return v___x_480_;
}
else
{
size_t v___x_481_; size_t v___x_482_; uint8_t v___x_483_; 
v___x_481_ = lean_ptr_addr(v_body_470_);
v___x_482_ = lean_ptr_addr(v_a_475_);
v___x_483_ = lean_usize_dec_eq(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc(v_binderName_468_);
lean_dec_ref_known(v___y_445_, 3);
v___x_484_ = l_Lean_Expr_lam___override(v_binderName_468_, v_a_473_, v_a_475_, v_binderInfo_471_);
v___x_485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_484_, v___y_434_, v___y_435_, v___y_436_);
return v___x_485_;
}
else
{
uint8_t v___x_486_; 
v___x_486_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_471_, v_binderInfo_471_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_binderName_468_);
lean_dec_ref_known(v___y_445_, 3);
v___x_487_ = l_Lean_Expr_lam___override(v_binderName_468_, v_a_473_, v_a_475_, v_binderInfo_471_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_487_, v___y_434_, v___y_435_, v___y_436_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; 
lean_dec(v_a_475_);
lean_dec(v_a_473_);
v___x_489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_445_, v___y_434_, v___y_435_, v___y_436_);
return v___x_489_;
}
}
}
}
else
{
lean_dec(v_a_473_);
lean_dec_ref_known(v___y_445_, 3);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_474_;
}
}
else
{
lean_dec_ref_known(v___y_445_, 3);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_472_;
}
}
case 8:
{
lean_object* v_declName_490_; lean_object* v_type_491_; lean_object* v_value_492_; lean_object* v_body_493_; uint8_t v_nondep_494_; lean_object* v___x_495_; 
v_declName_490_ = lean_ctor_get(v___y_445_, 0);
v_type_491_ = lean_ctor_get(v___y_445_, 1);
v_value_492_ = lean_ctor_get(v___y_445_, 2);
v_body_493_ = lean_ctor_get(v___y_445_, 3);
v_nondep_494_ = lean_ctor_get_uint8(v___y_445_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_491_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_type_491_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
lean_inc_ref(v_value_492_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_value_492_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
lean_inc_ref(v_body_493_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_499_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_493_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; size_t v___x_501_; size_t v___x_502_; uint8_t v___x_503_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v___x_501_ = lean_ptr_addr(v_type_491_);
v___x_502_ = lean_ptr_addr(v_a_496_);
v___x_503_ = lean_usize_dec_eq(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_inc(v_declName_490_);
lean_dec_ref_known(v___y_445_, 4);
v___x_504_ = l_Lean_Expr_letE___override(v_declName_490_, v_a_496_, v_a_498_, v_a_500_, v_nondep_494_);
v___x_505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_504_, v___y_434_, v___y_435_, v___y_436_);
return v___x_505_;
}
else
{
size_t v___x_506_; size_t v___x_507_; uint8_t v___x_508_; 
v___x_506_ = lean_ptr_addr(v_value_492_);
v___x_507_ = lean_ptr_addr(v_a_498_);
v___x_508_ = lean_usize_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_inc(v_declName_490_);
lean_dec_ref_known(v___y_445_, 4);
v___x_509_ = l_Lean_Expr_letE___override(v_declName_490_, v_a_496_, v_a_498_, v_a_500_, v_nondep_494_);
v___x_510_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_509_, v___y_434_, v___y_435_, v___y_436_);
return v___x_510_;
}
else
{
size_t v___x_511_; size_t v___x_512_; uint8_t v___x_513_; 
v___x_511_ = lean_ptr_addr(v_body_493_);
v___x_512_ = lean_ptr_addr(v_a_500_);
v___x_513_ = lean_usize_dec_eq(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_inc(v_declName_490_);
lean_dec_ref_known(v___y_445_, 4);
v___x_514_ = l_Lean_Expr_letE___override(v_declName_490_, v_a_496_, v_a_498_, v_a_500_, v_nondep_494_);
v___x_515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_514_, v___y_434_, v___y_435_, v___y_436_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; 
lean_dec(v_a_500_);
lean_dec(v_a_498_);
lean_dec(v_a_496_);
v___x_516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_445_, v___y_434_, v___y_435_, v___y_436_);
return v___x_516_;
}
}
}
}
else
{
lean_dec(v_a_498_);
lean_dec(v_a_496_);
lean_dec_ref_known(v___y_445_, 4);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_499_;
}
}
else
{
lean_dec(v_a_496_);
lean_dec_ref_known(v___y_445_, 4);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_497_;
}
}
else
{
lean_dec_ref_known(v___y_445_, 4);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_495_;
}
}
case 5:
{
lean_object* v_dummy_517_; lean_object* v_nargs_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_dummy_517_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_518_ = l_Lean_Expr_getAppNumArgs(v___y_445_);
lean_inc(v_nargs_518_);
v___x_519_ = lean_mk_array(v_nargs_518_, v_dummy_517_);
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_sub(v_nargs_518_, v___x_520_);
lean_dec(v_nargs_518_);
v___x_522_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_431_, v_post_433_, v___y_445_, v___x_519_, v___x_521_, v___y_434_, v___y_435_, v___y_436_);
return v___x_522_;
}
case 10:
{
lean_object* v_data_523_; lean_object* v_expr_524_; lean_object* v___x_525_; 
v_data_523_ = lean_ctor_get(v___y_445_, 0);
v_expr_524_ = lean_ctor_get(v___y_445_, 1);
lean_inc_ref(v_expr_524_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_expr_524_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; size_t v___x_527_; size_t v___x_528_; uint8_t v___x_529_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = lean_ptr_addr(v_expr_524_);
v___x_528_ = lean_ptr_addr(v_a_526_);
v___x_529_ = lean_usize_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_inc(v_data_523_);
lean_dec_ref_known(v___y_445_, 2);
v___x_530_ = l_Lean_Expr_mdata___override(v_data_523_, v_a_526_);
v___x_531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_530_, v___y_434_, v___y_435_, v___y_436_);
return v___x_531_;
}
else
{
lean_object* v___x_532_; 
lean_dec(v_a_526_);
v___x_532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_445_, v___y_434_, v___y_435_, v___y_436_);
return v___x_532_;
}
}
else
{
lean_dec_ref_known(v___y_445_, 2);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_525_;
}
}
case 11:
{
lean_object* v_typeName_533_; lean_object* v_idx_534_; lean_object* v_struct_535_; lean_object* v___x_536_; 
v_typeName_533_ = lean_ctor_get(v___y_445_, 0);
v_idx_534_ = lean_ctor_get(v___y_445_, 1);
v_struct_535_ = lean_ctor_get(v___y_445_, 2);
lean_inc_ref(v_struct_535_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_536_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_struct_535_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; size_t v___x_538_; size_t v___x_539_; uint8_t v___x_540_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = lean_ptr_addr(v_struct_535_);
v___x_539_ = lean_ptr_addr(v_a_537_);
v___x_540_ = lean_usize_dec_eq(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_inc(v_idx_534_);
lean_inc(v_typeName_533_);
lean_dec_ref_known(v___y_445_, 3);
v___x_541_ = l_Lean_Expr_proj___override(v_typeName_533_, v_idx_534_, v_a_537_);
v___x_542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_541_, v___y_434_, v___y_435_, v___y_436_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
lean_dec(v_a_537_);
v___x_543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_445_, v___y_434_, v___y_435_, v___y_436_);
return v___x_543_;
}
}
else
{
lean_dec_ref_known(v___y_445_, 3);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_536_;
}
}
default: 
{
lean_object* v___x_544_; 
v___x_544_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_445_, v___y_434_, v___y_435_, v___y_436_);
return v___x_544_;
}
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v_post_433_);
lean_dec_ref(v_e_432_);
lean_dec_ref(v_pre_431_);
v_a_556_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_439_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_439_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v_post_433_);
lean_dec_ref(v_e_432_);
lean_dec_ref(v_pre_431_);
v_a_564_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_438_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_438_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_572_, lean_object* v_pre_573_, lean_object* v_e_574_, lean_object* v_post_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_572_, v_pre_573_, v_e_574_, v_post_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_581_, lean_object* v_post_582_, lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
lean_inc(v_a_584_);
v___x_588_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_588_, 0, lean_box(0));
lean_closure_set(v___x_588_, 1, lean_box(0));
lean_closure_set(v___x_588_, 2, v_a_584_);
v___x_589_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_588_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_621_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_621_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_621_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_621_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_590_, v_e_583_);
lean_dec(v_a_590_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_595_; lean_object* v___f_596_; lean_object* v___x_597_; 
lean_del_object(v___x_592_);
v___x_595_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_583_);
v___f_596_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_596_, 0, v___x_595_);
lean_closure_set(v___f_596_, 1, v_pre_581_);
lean_closure_set(v___f_596_, 2, v_e_583_);
lean_closure_set(v___f_596_, 3, v_post_582_);
v___x_597_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_596_, v_a_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___f_599_; lean_object* v___x_600_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc_n(v_a_598_, 2);
lean_dec_ref_known(v___x_597_, 1);
lean_inc(v_a_584_);
v___f_599_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_599_, 0, v_a_584_);
lean_closure_set(v___f_599_, 1, v_e_583_);
lean_closure_set(v___f_599_, 2, v_a_598_);
v___x_600_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_599_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v___x_600_, 0);
lean_dec(v_unused_608_);
v___x_602_ = v___x_600_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_dec(v___x_600_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v_a_598_);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_598_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_a_598_);
v_a_609_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_600_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_600_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_dec_ref(v_e_583_);
return v___x_597_;
}
}
else
{
lean_object* v_val_617_; lean_object* v___x_619_; 
lean_dec_ref(v_e_583_);
lean_dec_ref(v_post_582_);
lean_dec_ref(v_pre_581_);
v_val_617_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v___x_594_, 1);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v_val_617_);
v___x_619_ = v___x_592_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_val_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_e_583_);
lean_dec_ref(v_post_582_);
lean_dec_ref(v_pre_581_);
v_a_622_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_589_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_589_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_630_, lean_object* v_post_631_, lean_object* v_e_632_, lean_object* v_a_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; 
lean_inc_ref(v_post_631_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc_ref(v_e_632_);
v___x_637_ = lean_apply_4(v_post_631_, v_e_632_, v___y_634_, v___y_635_, lean_box(0));
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_656_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_656_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_656_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_656_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
switch(lean_obj_tag(v_a_638_))
{
case 0:
{
lean_object* v_e_642_; lean_object* v___x_644_; 
lean_dec_ref(v_e_632_);
lean_dec_ref(v_post_631_);
lean_dec_ref(v_pre_630_);
v_e_642_ = lean_ctor_get(v_a_638_, 0);
lean_inc_ref(v_e_642_);
lean_dec_ref_known(v_a_638_, 1);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_e_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_e_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
case 1:
{
lean_object* v_e_646_; lean_object* v___x_647_; 
lean_del_object(v___x_640_);
lean_dec_ref(v_e_632_);
v_e_646_ = lean_ctor_get(v_a_638_, 0);
lean_inc_ref(v_e_646_);
lean_dec_ref_known(v_a_638_, 1);
v___x_647_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_630_, v_post_631_, v_e_646_, v_a_633_, v___y_634_, v___y_635_);
return v___x_647_;
}
default: 
{
lean_object* v_e_x3f_648_; 
lean_dec_ref(v_post_631_);
lean_dec_ref(v_pre_630_);
v_e_x3f_648_ = lean_ctor_get(v_a_638_, 0);
lean_inc(v_e_x3f_648_);
lean_dec_ref_known(v_a_638_, 1);
if (lean_obj_tag(v_e_x3f_648_) == 0)
{
lean_object* v___x_650_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_e_632_);
v___x_650_ = v___x_640_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_e_632_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
else
{
lean_object* v_val_652_; lean_object* v___x_654_; 
lean_dec_ref(v_e_632_);
v_val_652_ = lean_ctor_get(v_e_x3f_648_, 0);
lean_inc(v_val_652_);
lean_dec_ref_known(v_e_x3f_648_, 1);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_val_652_);
v___x_654_ = v___x_640_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_val_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v_e_632_);
lean_dec_ref(v_post_631_);
lean_dec_ref(v_pre_630_);
v_a_657_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_637_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_637_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_665_, lean_object* v_post_666_, lean_object* v_e_667_, lean_object* v_a_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_665_, v_post_666_, v_e_667_, v_a_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v_a_668_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_673_, lean_object* v_post_674_, lean_object* v_sz_675_, lean_object* v_i_676_, lean_object* v_bs_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
size_t v_sz_boxed_682_; size_t v_i_boxed_683_; lean_object* v_res_684_; 
v_sz_boxed_682_ = lean_unbox_usize(v_sz_675_);
lean_dec(v_sz_675_);
v_i_boxed_683_ = lean_unbox_usize(v_i_676_);
lean_dec(v_i_676_);
v_res_684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_673_, v_post_674_, v_sz_boxed_682_, v_i_boxed_683_, v_bs_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_685_, lean_object* v_post_686_, lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_685_, v_post_686_, v_x_687_, v_x_688_, v_x_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_695_, lean_object* v_post_696_, lean_object* v_e_697_, lean_object* v_a_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_695_, v_post_696_, v_e_697_, v_a_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v_a_698_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_703_, lean_object* v_x_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_apply_1(v_x_704_, lean_box(0));
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_710_, lean_object* v_x_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_710_, v_x_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_715_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_box(0);
v___x_717_ = lean_unsigned_to_nat(16u);
v___x_718_ = lean_mk_array(v___x_717_, v___x_716_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___x_719_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_723_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_723_, 0, lean_box(0));
lean_closure_set(v___x_723_, 1, lean_box(0));
lean_closure_set(v___x_723_, 2, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_724_, lean_object* v_pre_725_, lean_object* v_post_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v_a_732_; lean_object* v___x_733_; 
v___x_730_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_731_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_730_, v___y_727_, v___y_728_);
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
v___x_733_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_725_, v_post_726_, v_input_724_, v_a_732_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_735_, 0, lean_box(0));
lean_closure_set(v___x_735_, 1, lean_box(0));
lean_closure_set(v___x_735_, 2, v_a_732_);
v___x_736_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_735_, v___y_727_, v___y_728_);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v___x_736_, 0);
lean_dec(v_unused_744_);
v___x_738_ = v___x_736_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_dec(v___x_736_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_a_734_);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_734_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
else
{
lean_dec(v_a_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_745_, lean_object* v_pre_746_, lean_object* v_post_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_745_, v_pre_746_, v_post_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___f_758_; lean_object* v___f_759_; lean_object* v___x_760_; 
v___f_758_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_759_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_760_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_754_, v___f_758_, v___f_759_, v_a_755_, v_a_756_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_elimOptParam(v_type_761_, v_a_762_, v_a_763_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_766_, lean_object* v_m_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_767_, v_a_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_770_, lean_object* v_m_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_770_, v_m_771_, v_a_772_);
lean_dec_ref(v_a_772_);
lean_dec_ref(v_m_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_774_, lean_object* v_ref_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_780_, lean_object* v_ref_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_780_, v_ref_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_796_, lean_object* v_x_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_803_, lean_object* v_x_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_803_, v_x_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_810_, lean_object* v_m_811_, lean_object* v_a_812_, lean_object* v_b_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_811_, v_a_812_, v_b_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_815_, lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_819_, lean_object* v_a_820_, lean_object* v_x_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_819_, v_a_820_, v_x_821_);
lean_dec(v_x_821_);
lean_dec_ref(v_a_820_);
return v_res_822_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_823_, lean_object* v_a_824_, lean_object* v_x_825_){
_start:
{
uint8_t v___x_826_; 
v___x_826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_824_, v_x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_827_, lean_object* v_a_828_, lean_object* v_x_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_827_, v_a_828_, v_x_829_);
lean_dec(v_x_829_);
lean_dec_ref(v_a_828_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_832_, lean_object* v_data_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_835_, lean_object* v_a_836_, lean_object* v_b_837_, lean_object* v_x_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_836_, v_b_837_, v_x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_840_, lean_object* v_i_841_, lean_object* v_source_842_, lean_object* v_target_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_841_, v_source_842_, v_target_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_845_, lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_846_, v_x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_849_, lean_object* v_as_850_, size_t v_sz_851_, size_t v_i_852_, lean_object* v_b_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_a_860_; uint8_t v___x_864_; 
v___x_864_ = lean_usize_dec_lt(v_i_852_, v_sz_851_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_b_853_);
return v___x_865_;
}
else
{
lean_object* v_snd_866_; lean_object* v_fst_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_945_; 
v_snd_866_ = lean_ctor_get(v_b_853_, 1);
v_fst_867_ = lean_ctor_get(v_b_853_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_b_853_);
if (v_isSharedCheck_945_ == 0)
{
v___x_869_ = v_b_853_;
v_isShared_870_ = v_isSharedCheck_945_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_snd_866_);
lean_inc(v_fst_867_);
lean_dec(v_b_853_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_945_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_array_871_; lean_object* v_start_872_; lean_object* v_stop_873_; uint8_t v___x_874_; 
v_array_871_ = lean_ctor_get(v_snd_866_, 0);
v_start_872_ = lean_ctor_get(v_snd_866_, 1);
v_stop_873_ = lean_ctor_get(v_snd_866_, 2);
v___x_874_ = lean_nat_dec_lt(v_start_872_, v_stop_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_876_; 
if (v_isShared_870_ == 0)
{
v___x_876_ = v___x_869_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_fst_867_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_snd_866_);
v___x_876_ = v_reuseFailAlloc_878_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
else
{
lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_941_; 
lean_inc(v_stop_873_);
lean_inc(v_start_872_);
lean_inc_ref(v_array_871_);
v_isSharedCheck_941_ = !lean_is_exclusive(v_snd_866_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; lean_object* v_unused_943_; lean_object* v_unused_944_; 
v_unused_942_ = lean_ctor_get(v_snd_866_, 2);
lean_dec(v_unused_942_);
v_unused_943_ = lean_ctor_get(v_snd_866_, 1);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_snd_866_, 0);
lean_dec(v_unused_944_);
v___x_880_ = v_snd_866_;
v_isShared_881_ = v_isSharedCheck_941_;
goto v_resetjp_879_;
}
else
{
lean_dec(v_snd_866_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_941_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_a_882_; lean_object* v___x_883_; 
v_a_882_ = lean_array_uget_borrowed(v_as_850_, v_i_852_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
lean_inc(v___y_855_);
lean_inc_ref(v___y_854_);
lean_inc(v_a_882_);
v___x_883_ = lean_infer_type(v_a_882_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v___x_885_ = lean_array_fget(v_array_871_, v_start_872_);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_nat_add(v_start_872_, v___x_886_);
lean_dec(v_start_872_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_887_);
v___x_889_ = v___x_880_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_array_871_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_stop_873_);
v___x_889_ = v_reuseFailAlloc_932_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
if (v_skipIfPropOrEq_849_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v_a_884_);
lean_inc(v_a_882_);
v___x_890_ = l_Lean_Meta_mkEqHEq(v_a_882_, v___x_885_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = lean_array_push(v_fst_867_, v_a_891_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v___x_889_);
lean_ctor_set(v___x_869_, 0, v___x_892_);
v___x_894_ = v___x_869_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
v_a_860_ = v___x_894_;
goto v___jp_859_;
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v___x_889_);
lean_del_object(v___x_869_);
lean_dec(v_fst_867_);
v_a_896_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_890_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_890_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_isProp(v_a_884_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; uint8_t v___x_910_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_910_ = lean_unbox(v_a_905_);
lean_dec(v_a_905_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; 
v___x_911_ = lean_expr_eqv(v_a_882_, v___x_885_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
lean_del_object(v___x_869_);
lean_inc(v_a_882_);
v___x_912_ = l_Lean_Meta_mkEqHEq(v_a_882_, v___x_885_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = lean_array_push(v_fst_867_, v_a_913_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_889_);
v_a_860_ = v___x_915_;
goto v___jp_859_;
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v___x_889_);
lean_dec(v_fst_867_);
v_a_916_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_912_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_912_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
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
else
{
lean_dec(v___x_885_);
goto v___jp_906_;
}
}
else
{
lean_dec(v___x_885_);
goto v___jp_906_;
}
v___jp_906_:
{
lean_object* v___x_908_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v___x_889_);
v___x_908_ = v___x_869_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_fst_867_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_889_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
v_a_860_ = v___x_908_;
goto v___jp_859_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v___x_889_);
lean_dec(v___x_885_);
lean_del_object(v___x_869_);
lean_dec(v_fst_867_);
v_a_924_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_904_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_904_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_del_object(v___x_880_);
lean_dec(v_stop_873_);
lean_dec(v_start_872_);
lean_dec_ref(v_array_871_);
lean_del_object(v___x_869_);
lean_dec(v_fst_867_);
v_a_933_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_883_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_883_);
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
}
}
}
v___jp_859_:
{
size_t v___x_861_; size_t v___x_862_; 
v___x_861_ = ((size_t)1ULL);
v___x_862_ = lean_usize_add(v_i_852_, v___x_861_);
v_i_852_ = v___x_862_;
v_b_853_ = v_a_860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_946_, lean_object* v_as_947_, lean_object* v_sz_948_, lean_object* v_i_949_, lean_object* v_b_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_956_; size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_skipIfPropOrEq_boxed_956_ = lean_unbox(v_skipIfPropOrEq_946_);
v_sz_boxed_957_ = lean_unbox_usize(v_sz_948_);
lean_dec(v_sz_948_);
v_i_boxed_958_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_956_, v_as_947_, v_sz_boxed_957_, v_i_boxed_958_, v_b_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec_ref(v_as_947_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_962_, lean_object* v_args2_963_, uint8_t v_skipIfPropOrEq_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_eqs_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; size_t v_sz_975_; size_t v___x_976_; lean_object* v___x_977_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v_eqs_971_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_972_ = lean_array_get_size(v_args2_963_);
v___x_973_ = l_Array_toSubarray___redArg(v_args2_963_, v___x_970_, v___x_972_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_eqs_971_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v_sz_975_ = lean_array_size(v_args1_962_);
v___x_976_ = ((size_t)0ULL);
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_964_, v_args1_962_, v_sz_975_, v___x_976_, v___x_974_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_fst_982_; lean_object* v___x_984_; 
v_fst_982_ = lean_ctor_get(v_a_978_, 0);
lean_inc(v_fst_982_);
lean_dec(v_a_978_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v_fst_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_fst_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
v_a_987_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_977_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_977_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_995_, lean_object* v_args2_996_, lean_object* v_skipIfPropOrEq_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_1003_; lean_object* v_res_1004_; 
v_skipIfPropOrEq_boxed_1003_ = lean_unbox(v_skipIfPropOrEq_997_);
v_res_1004_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_995_, v_args2_996_, v_skipIfPropOrEq_boxed_1003_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec_ref(v_args1_995_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_1005_, lean_object* v_b_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
v___x_1012_ = lean_apply_6(v_k_1005_, v_b_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, lean_box(0));
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_1013_, lean_object* v_b_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_1013_, v_b_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1021_, uint8_t v_bi_1022_, lean_object* v_type_1023_, lean_object* v_k_1024_, uint8_t v_kind_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___f_1031_; lean_object* v___x_1032_; 
v___f_1031_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1031_, 0, v_k_1024_);
v___x_1032_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1021_, v_bi_1022_, v_type_1023_, v___f_1031_, v_kind_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v_a_1041_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1032_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1032_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1049_, lean_object* v_bi_1050_, lean_object* v_type_1051_, lean_object* v_k_1052_, lean_object* v_kind_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
uint8_t v_bi_boxed_1059_; uint8_t v_kind_boxed_1060_; lean_object* v_res_1061_; 
v_bi_boxed_1059_ = lean_unbox(v_bi_1050_);
v_kind_boxed_1060_ = lean_unbox(v_kind_1053_);
v_res_1061_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1049_, v_bi_boxed_1059_, v_type_1051_, v_k_1052_, v_kind_boxed_1060_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1062_, lean_object* v_name_1063_, uint8_t v_bi_1064_, lean_object* v_type_1065_, lean_object* v_k_1066_, uint8_t v_kind_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1063_, v_bi_1064_, v_type_1065_, v_k_1066_, v_kind_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1074_, lean_object* v_name_1075_, lean_object* v_bi_1076_, lean_object* v_type_1077_, lean_object* v_k_1078_, lean_object* v_kind_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v_bi_boxed_1085_; uint8_t v_kind_boxed_1086_; lean_object* v_res_1087_; 
v_bi_boxed_1085_ = lean_unbox(v_bi_1076_);
v_kind_boxed_1086_ = lean_unbox(v_kind_1079_);
v_res_1087_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1074_, v_name_1075_, v_bi_boxed_1085_, v_type_1077_, v_k_1078_, v_kind_boxed_1086_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; lean_object* v_env_1095_; lean_object* v___x_1096_; lean_object* v_mctx_1097_; lean_object* v_lctx_1098_; lean_object* v_options_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1094_ = lean_st_ref_get(v___y_1092_);
v_env_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc_ref(v_env_1095_);
lean_dec(v___x_1094_);
v___x_1096_ = lean_st_ref_get(v___y_1090_);
v_mctx_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_ref(v_mctx_1097_);
lean_dec(v___x_1096_);
v_lctx_1098_ = lean_ctor_get(v___y_1089_, 2);
v_options_1099_ = lean_ctor_get(v___y_1091_, 2);
lean_inc_ref(v_options_1099_);
lean_inc_ref(v_lctx_1098_);
v___x_1100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1100_, 0, v_env_1095_);
lean_ctor_set(v___x_1100_, 1, v_mctx_1097_);
lean_ctor_set(v___x_1100_, 2, v_lctx_1098_);
lean_ctor_set(v___x_1100_, 3, v_options_1099_);
v___x_1101_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v_msgData_1088_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_ref_1116_; lean_object* v___x_1117_; lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1126_; 
v_ref_1116_ = lean_ctor_get(v___y_1113_, 5);
v___x_1117_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_inc(v_ref_1116_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_ref_1116_);
lean_ctor_set(v___x_1122_, 1, v_a_1118_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1134_, lean_object* v_body_1135_, lean_object* v_args2_1136_, lean_object* v_args2New_1137_, lean_object* v_ctorVal_1138_, lean_object* v_useEq_1139_, lean_object* v_args1_1140_, lean_object* v_resultType_1141_, lean_object* v_k_1142_, lean_object* v_arg2_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v_useEq_boxed_1149_; lean_object* v_res_1150_; 
v_useEq_boxed_1149_ = lean_unbox(v_useEq_1139_);
v_res_1150_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1134_, v_body_1135_, v_args2_1136_, v_args2New_1137_, v_ctorVal_1138_, v_useEq_boxed_1149_, v_args1_1140_, v_resultType_1141_, v_k_1142_, v_arg2_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec_ref(v_body_1135_);
lean_dec(v_i_1134_);
return v_res_1150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1157_, uint8_t v_useEq_1158_, lean_object* v_args1_1159_, lean_object* v_resultType_1160_, lean_object* v_k_1161_, lean_object* v_i_1162_, lean_object* v_type_1163_, lean_object* v_args2_1164_, lean_object* v_args2New_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_array_get_size(v_args1_1159_);
v___x_1172_ = lean_nat_dec_lt(v_i_1162_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec_ref(v_type_1163_);
lean_dec(v_i_1162_);
lean_dec_ref(v_resultType_1160_);
lean_dec_ref(v_args1_1159_);
lean_dec_ref(v_ctorVal_1157_);
lean_inc(v_a_1169_);
lean_inc_ref(v_a_1168_);
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
v___x_1173_ = lean_apply_7(v_k_1161_, v_args2_1164_, v_args2New_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, lean_box(0));
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
lean_inc(v_a_1169_);
lean_inc_ref(v_a_1168_);
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
v___x_1174_ = lean_whnf(v_type_1163_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
if (lean_obj_tag(v_a_1175_) == 7)
{
lean_object* v_binderName_1176_; lean_object* v_binderType_1177_; lean_object* v_body_1178_; lean_object* v_lctx_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_binderName_1176_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_binderName_1176_);
v_binderType_1177_ = lean_ctor_get(v_a_1175_, 1);
lean_inc_ref(v_binderType_1177_);
v_body_1178_ = lean_ctor_get(v_a_1175_, 2);
lean_inc_ref(v_body_1178_);
lean_dec_ref_known(v_a_1175_, 3);
v_lctx_1179_ = lean_ctor_get(v_a_1166_, 2);
v___x_1180_ = lean_array_fget_borrowed(v_args1_1159_, v_i_1162_);
lean_inc(v___x_1180_);
lean_inc_ref(v_lctx_1179_);
v___x_1181_ = l_Lean_Meta_occursOrInType(v_lctx_1179_, v___x_1180_, v_resultType_1160_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___f_1183_; uint8_t v___y_1185_; 
v___x_1182_ = lean_box(v_useEq_1158_);
v___f_1183_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1183_, 0, v_i_1162_);
lean_closure_set(v___f_1183_, 1, v_body_1178_);
lean_closure_set(v___f_1183_, 2, v_args2_1164_);
lean_closure_set(v___f_1183_, 3, v_args2New_1165_);
lean_closure_set(v___f_1183_, 4, v_ctorVal_1157_);
lean_closure_set(v___f_1183_, 5, v___x_1182_);
lean_closure_set(v___f_1183_, 6, v_args1_1159_);
lean_closure_set(v___f_1183_, 7, v_resultType_1160_);
lean_closure_set(v___f_1183_, 8, v_k_1161_);
if (v_useEq_1158_ == 0)
{
uint8_t v___x_1188_; 
v___x_1188_ = 1;
v___y_1185_ = v___x_1188_;
goto v___jp_1184_;
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = 0;
v___y_1185_ = v___x_1189_;
goto v___jp_1184_;
}
v___jp_1184_:
{
uint8_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = 0;
v___x_1187_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1176_, v___y_1185_, v_binderType_1177_, v___f_1183_, v___x_1186_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1187_;
}
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v_binderType_1177_);
lean_dec(v_binderName_1176_);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_i_1162_, v___x_1190_);
lean_dec(v_i_1162_);
v___x_1192_ = lean_expr_instantiate1(v_body_1178_, v___x_1180_);
lean_dec_ref(v_body_1178_);
lean_inc(v___x_1180_);
v___x_1193_ = lean_array_push(v_args2_1164_, v___x_1180_);
v_i_1162_ = v___x_1191_;
v_type_1163_ = v___x_1192_;
v_args2_1164_ = v___x_1193_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1195_; lean_object* v_name_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v_a_1175_);
lean_dec_ref(v_args2New_1165_);
lean_dec_ref(v_args2_1164_);
lean_dec(v_i_1162_);
lean_dec_ref(v_k_1161_);
lean_dec_ref(v_resultType_1160_);
lean_dec_ref(v_args1_1159_);
v_toConstantVal_1195_ = lean_ctor_get(v_ctorVal_1157_, 0);
lean_inc_ref(v_toConstantVal_1195_);
lean_dec_ref(v_ctorVal_1157_);
v_name_1196_ = lean_ctor_get(v_toConstantVal_1195_, 0);
lean_inc(v_name_1196_);
lean_dec_ref(v_toConstantVal_1195_);
v___x_1197_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1198_ = l_Lean_MessageData_ofName(v_name_1196_);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1201_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1202_;
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_args2New_1165_);
lean_dec_ref(v_args2_1164_);
lean_dec(v_i_1162_);
lean_dec_ref(v_k_1161_);
lean_dec_ref(v_resultType_1160_);
lean_dec_ref(v_args1_1159_);
lean_dec_ref(v_ctorVal_1157_);
v_a_1203_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1174_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1174_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1211_, lean_object* v_body_1212_, lean_object* v_args2_1213_, lean_object* v_args2New_1214_, lean_object* v_ctorVal_1215_, uint8_t v_useEq_1216_, lean_object* v_args1_1217_, lean_object* v_resultType_1218_, lean_object* v_k_1219_, lean_object* v_arg2_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_add(v_i_1211_, v___x_1226_);
v___x_1228_ = lean_expr_instantiate1(v_body_1212_, v_arg2_1220_);
lean_inc_ref(v_arg2_1220_);
v___x_1229_ = lean_array_push(v_args2_1213_, v_arg2_1220_);
v___x_1230_ = lean_array_push(v_args2New_1214_, v_arg2_1220_);
v___x_1231_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1215_, v_useEq_1216_, v_args1_1217_, v_resultType_1218_, v_k_1219_, v___x_1227_, v___x_1228_, v___x_1229_, v___x_1230_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1232_, lean_object* v_useEq_1233_, lean_object* v_args1_1234_, lean_object* v_resultType_1235_, lean_object* v_k_1236_, lean_object* v_i_1237_, lean_object* v_type_1238_, lean_object* v_args2_1239_, lean_object* v_args2New_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
uint8_t v_useEq_boxed_1246_; lean_object* v_res_1247_; 
v_useEq_boxed_1246_ = lean_unbox(v_useEq_1233_);
v_res_1247_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1232_, v_useEq_boxed_1246_, v_args1_1234_, v_resultType_1235_, v_k_1236_, v_i_1237_, v_type_1238_, v_args2_1239_, v_args2New_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1248_, lean_object* v_msg_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_msg_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1256_, v_msg_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1264_, lean_object* v_h__1_1265_, lean_object* v_h__2_1266_){
_start:
{
if (lean_obj_tag(v_____x_1264_) == 7)
{
lean_object* v_binderName_1267_; lean_object* v_binderType_1268_; lean_object* v_body_1269_; uint8_t v_binderInfo_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_dec(v_h__2_1266_);
v_binderName_1267_ = lean_ctor_get(v_____x_1264_, 0);
lean_inc(v_binderName_1267_);
v_binderType_1268_ = lean_ctor_get(v_____x_1264_, 1);
lean_inc_ref(v_binderType_1268_);
v_body_1269_ = lean_ctor_get(v_____x_1264_, 2);
lean_inc_ref(v_body_1269_);
v_binderInfo_1270_ = lean_ctor_get_uint8(v_____x_1264_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1264_, 3);
v___x_1271_ = lean_box(v_binderInfo_1270_);
v___x_1272_ = lean_apply_4(v_h__1_1265_, v_binderName_1267_, v_binderType_1268_, v_body_1269_, v___x_1271_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; 
lean_dec(v_h__1_1265_);
v___x_1273_ = lean_apply_2(v_h__2_1266_, v_____x_1264_, lean_box(0));
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1274_, lean_object* v_____x_1275_, lean_object* v_h__1_1276_, lean_object* v_h__2_1277_){
_start:
{
if (lean_obj_tag(v_____x_1275_) == 7)
{
lean_object* v_binderName_1278_; lean_object* v_binderType_1279_; lean_object* v_body_1280_; uint8_t v_binderInfo_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec(v_h__2_1277_);
v_binderName_1278_ = lean_ctor_get(v_____x_1275_, 0);
lean_inc(v_binderName_1278_);
v_binderType_1279_ = lean_ctor_get(v_____x_1275_, 1);
lean_inc_ref(v_binderType_1279_);
v_body_1280_ = lean_ctor_get(v_____x_1275_, 2);
lean_inc_ref(v_body_1280_);
v_binderInfo_1281_ = lean_ctor_get_uint8(v_____x_1275_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1275_, 3);
v___x_1282_ = lean_box(v_binderInfo_1281_);
v___x_1283_ = lean_apply_4(v_h__1_1276_, v_binderName_1278_, v_binderType_1279_, v_body_1280_, v___x_1282_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; 
lean_dec(v_h__1_1276_);
v___x_1284_ = lean_apply_2(v_h__2_1277_, v_____x_1275_, lean_box(0));
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1285_, lean_object* v_b_1286_, lean_object* v_c_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
v___x_1293_ = lean_apply_7(v_k_1285_, v_b_1286_, v_c_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, lean_box(0));
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1294_, lean_object* v_b_1295_, lean_object* v_c_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1294_, v_b_1295_, v_c_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1303_, lean_object* v_k_1304_, uint8_t v_cleanupAnnotations_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___f_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1311_, 0, v_k_1304_);
v___x_1312_ = 0;
v___x_1313_ = lean_box(0);
v___x_1314_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1312_, v___x_1313_, v_type_1303_, v___f_1311_, v_cleanupAnnotations_1305_, v___x_1312_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_a_1323_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1314_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1314_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1331_, lean_object* v_k_1332_, lean_object* v_cleanupAnnotations_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1339_; lean_object* v_res_1340_; 
v_cleanupAnnotations_boxed_1339_ = lean_unbox(v_cleanupAnnotations_1333_);
v_res_1340_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1331_, v_k_1332_, v_cleanupAnnotations_boxed_1339_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1341_, lean_object* v_type_1342_, lean_object* v_k_1343_, uint8_t v_cleanupAnnotations_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1342_, v_k_1343_, v_cleanupAnnotations_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_type_1352_, lean_object* v_k_1353_, lean_object* v_cleanupAnnotations_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1360_; lean_object* v_res_1361_; 
v_cleanupAnnotations_boxed_1360_ = lean_unbox(v_cleanupAnnotations_1354_);
v_res_1361_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1351_, v_type_1352_, v_k_1353_, v_cleanupAnnotations_boxed_1360_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1362_, lean_object* v_maxFVars_x3f_1363_, lean_object* v_k_1364_, uint8_t v_cleanupAnnotations_1365_, uint8_t v_whnfType_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___f_1372_; lean_object* v___x_1373_; 
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1372_, 0, v_k_1364_);
v___x_1373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1362_, v_maxFVars_x3f_1363_, v___f_1372_, v_cleanupAnnotations_1365_, v_whnfType_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
v_a_1382_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1373_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1373_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1390_, lean_object* v_maxFVars_x3f_1391_, lean_object* v_k_1392_, lean_object* v_cleanupAnnotations_1393_, lean_object* v_whnfType_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1400_; uint8_t v_whnfType_boxed_1401_; lean_object* v_res_1402_; 
v_cleanupAnnotations_boxed_1400_ = lean_unbox(v_cleanupAnnotations_1393_);
v_whnfType_boxed_1401_ = lean_unbox(v_whnfType_1394_);
v_res_1402_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1390_, v_maxFVars_x3f_1391_, v_k_1392_, v_cleanupAnnotations_boxed_1400_, v_whnfType_boxed_1401_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1403_, lean_object* v_type_1404_, lean_object* v_maxFVars_x3f_1405_, lean_object* v_k_1406_, uint8_t v_cleanupAnnotations_1407_, uint8_t v_whnfType_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1404_, v_maxFVars_x3f_1405_, v_k_1406_, v_cleanupAnnotations_1407_, v_whnfType_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_type_1416_, lean_object* v_maxFVars_x3f_1417_, lean_object* v_k_1418_, lean_object* v_cleanupAnnotations_1419_, lean_object* v_whnfType_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1426_; uint8_t v_whnfType_boxed_1427_; lean_object* v_res_1428_; 
v_cleanupAnnotations_boxed_1426_ = lean_unbox(v_cleanupAnnotations_1419_);
v_whnfType_boxed_1427_ = lean_unbox(v_whnfType_1420_);
v_res_1428_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1415_, v_type_1416_, v_maxFVars_x3f_1417_, v_k_1418_, v_cleanupAnnotations_boxed_1426_, v_whnfType_boxed_1427_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1429_, lean_object* v_us_1430_, lean_object* v_params_1431_, lean_object* v_args1_1432_, uint8_t v_useEq_1433_, lean_object* v_args2_1434_, lean_object* v_args2New_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1441_ = l_Lean_mkConst(v_name_1429_, v_us_1430_);
v___x_1442_ = l_Lean_mkAppN(v___x_1441_, v_params_1431_);
lean_inc_ref(v___x_1442_);
v___x_1443_ = l_Lean_mkAppN(v___x_1442_, v_args1_1432_);
v___x_1444_ = l_Lean_mkAppN(v___x_1442_, v_args2_1434_);
v___x_1445_ = l_Lean_Meta_mkEq(v___x_1443_, v___x_1444_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; uint8_t v___x_1447_; lean_object* v_result_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___x_1494_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = 1;
v___x_1494_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1432_, v_args2_1434_, v___x_1447_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1526_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1526_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1526_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; 
v___x_1499_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1495_);
if (lean_obj_tag(v___x_1499_) == 1)
{
lean_del_object(v___x_1497_);
if (v_useEq_1433_ == 0)
{
lean_object* v_val_1500_; lean_object* v___x_1501_; 
v_val_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1501_ = l_Lean_mkArrow(v_a_1446_, v_val_1500_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v_result_1449_ = v_a_1502_;
v___y_1450_ = v___y_1436_;
v___y_1451_ = v___y_1437_;
v___y_1452_ = v___y_1438_;
v___y_1453_ = v___y_1439_;
goto v___jp_1448_;
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1501_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1501_);
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
else
{
lean_object* v_val_1511_; lean_object* v___x_1512_; 
v_val_1511_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1512_ = l_Lean_Meta_mkEq(v_a_1446_, v_val_1511_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v_result_1449_ = v_a_1513_;
v___y_1450_ = v___y_1436_;
v___y_1451_ = v___y_1437_;
v___y_1452_ = v___y_1438_;
v___y_1453_ = v___y_1439_;
goto v___jp_1448_;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_a_1514_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1512_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1512_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_dec(v___x_1499_);
lean_dec(v_a_1446_);
v___x_1522_ = lean_box(0);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1522_);
v___x_1524_ = v___x_1497_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_a_1446_);
v_a_1527_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1494_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1494_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
v___jp_1448_:
{
uint8_t v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = 0;
v___x_1455_ = 1;
v___x_1456_ = l_Lean_Meta_mkForallFVars(v_args2New_1435_, v_result_1449_, v___x_1454_, v___x_1447_, v___x_1447_, v___x_1455_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = l_Lean_Meta_mkForallFVars(v_args1_1432_, v_a_1457_, v___x_1454_, v___x_1447_, v___x_1447_, v___x_1455_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v___x_1460_ = l_Lean_Meta_mkForallFVars(v_params_1431_, v_a_1459_, v___x_1454_, v___x_1447_, v___x_1447_, v___x_1455_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_a_1461_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1470_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1460_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1460_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
v_a_1478_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1458_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1458_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_a_1486_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1456_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1456_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v_args2_1434_);
v_a_1535_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1445_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1445_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1543_, lean_object* v_us_1544_, lean_object* v_params_1545_, lean_object* v_args1_1546_, lean_object* v_useEq_1547_, lean_object* v_args2_1548_, lean_object* v_args2New_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v_useEq_boxed_1555_; lean_object* v_res_1556_; 
v_useEq_boxed_1555_ = lean_unbox(v_useEq_1547_);
v_res_1556_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1543_, v_us_1544_, v_params_1545_, v_args1_1546_, v_useEq_boxed_1555_, v_args2_1548_, v_args2New_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec_ref(v_args2New_1549_);
lean_dec_ref(v_args1_1546_);
lean_dec_ref(v_params_1545_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1557_, size_t v_i_1558_, lean_object* v_bs_1559_){
_start:
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_usize_dec_lt(v_i_1558_, v_sz_1557_);
if (v___x_1560_ == 0)
{
return v_bs_1559_;
}
else
{
lean_object* v_v_1561_; lean_object* v___x_1562_; lean_object* v_bs_x27_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; size_t v___x_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
v_v_1561_ = lean_array_uget(v_bs_1559_, v_i_1558_);
v___x_1562_ = lean_unsigned_to_nat(0u);
v_bs_x27_1563_ = lean_array_uset(v_bs_1559_, v_i_1558_, v___x_1562_);
v___x_1564_ = l_Lean_Expr_fvarId_x21(v_v_1561_);
lean_dec(v_v_1561_);
v___x_1565_ = 1;
v___x_1566_ = lean_box(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1564_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = ((size_t)1ULL);
v___x_1569_ = lean_usize_add(v_i_1558_, v___x_1568_);
v___x_1570_ = lean_array_uset(v_bs_x27_1563_, v_i_1558_, v___x_1567_);
v_i_1558_ = v___x_1569_;
v_bs_1559_ = v___x_1570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1572_, lean_object* v_i_1573_, lean_object* v_bs_1574_){
_start:
{
size_t v_sz_boxed_1575_; size_t v_i_boxed_1576_; lean_object* v_res_1577_; 
v_sz_boxed_1575_ = lean_unbox_usize(v_sz_1572_);
lean_dec(v_sz_1572_);
v_i_boxed_1576_ = lean_unbox_usize(v_i_1573_);
lean_dec(v_i_1573_);
v_res_1577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1575_, v_i_boxed_1576_, v_bs_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1578_, lean_object* v_k_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1578_, v_k_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_a_1594_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1585_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1585_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1602_, lean_object* v_k_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1602_, v_k_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec_ref(v_bs_1602_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1610_, lean_object* v_k_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
size_t v_sz_1617_; size_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_sz_1617_ = lean_array_size(v_bs_1610_);
v___x_1618_ = ((size_t)0ULL);
v___x_1619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1617_, v___x_1618_, v_bs_1610_);
v___x_1620_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1619_, v_k_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec_ref(v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1621_, lean_object* v_k_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1621_, v_k_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1629_, lean_object* v_us_1630_, lean_object* v_params_1631_, uint8_t v_useEq_1632_, lean_object* v_ctorVal_1633_, lean_object* v_type_1634_, lean_object* v_args1_1635_, lean_object* v_resultType_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; lean_object* v___f_1643_; 
v___x_1642_ = lean_box(v_useEq_1632_);
lean_inc_ref(v_args1_1635_);
lean_inc_ref(v_params_1631_);
v___f_1643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1643_, 0, v_name_1629_);
lean_closure_set(v___f_1643_, 1, v_us_1630_);
lean_closure_set(v___f_1643_, 2, v_params_1631_);
lean_closure_set(v___f_1643_, 3, v_args1_1635_);
lean_closure_set(v___f_1643_, 4, v___x_1642_);
if (v_useEq_1632_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1644_ = l_Array_append___redArg(v_params_1631_, v_args1_1635_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1647_ = lean_box(v_useEq_1632_);
v___x_1648_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1648_, 0, v_ctorVal_1633_);
lean_closure_set(v___x_1648_, 1, v___x_1647_);
lean_closure_set(v___x_1648_, 2, v_args1_1635_);
lean_closure_set(v___x_1648_, 3, v_resultType_1636_);
lean_closure_set(v___x_1648_, 4, v___f_1643_);
lean_closure_set(v___x_1648_, 5, v___x_1645_);
lean_closure_set(v___x_1648_, 6, v_type_1634_);
lean_closure_set(v___x_1648_, 7, v___x_1646_);
lean_closure_set(v___x_1648_, 8, v___x_1646_);
v___x_1649_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1644_, v___x_1648_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec_ref(v_params_1631_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1652_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1633_, v_useEq_1632_, v_args1_1635_, v_resultType_1636_, v___f_1643_, v___x_1650_, v_type_1634_, v___x_1651_, v___x_1651_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1653_, lean_object* v_us_1654_, lean_object* v_params_1655_, lean_object* v_useEq_1656_, lean_object* v_ctorVal_1657_, lean_object* v_type_1658_, lean_object* v_args1_1659_, lean_object* v_resultType_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
uint8_t v_useEq_boxed_1666_; lean_object* v_res_1667_; 
v_useEq_boxed_1666_ = lean_unbox(v_useEq_1656_);
v_res_1667_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1653_, v_us_1654_, v_params_1655_, v_useEq_boxed_1666_, v_ctorVal_1657_, v_type_1658_, v_args1_1659_, v_resultType_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1668_, lean_object* v_us_1669_, uint8_t v_useEq_1670_, lean_object* v_ctorVal_1671_, lean_object* v_params_1672_, lean_object* v_type_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v___f_1680_; uint8_t v___x_1681_; lean_object* v___x_1682_; 
v___x_1679_ = lean_box(v_useEq_1670_);
lean_inc_ref(v_type_1673_);
v___f_1680_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1680_, 0, v_name_1668_);
lean_closure_set(v___f_1680_, 1, v_us_1669_);
lean_closure_set(v___f_1680_, 2, v_params_1672_);
lean_closure_set(v___f_1680_, 3, v___x_1679_);
lean_closure_set(v___f_1680_, 4, v_ctorVal_1671_);
lean_closure_set(v___f_1680_, 5, v_type_1673_);
v___x_1681_ = 0;
v___x_1682_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1673_, v___f_1680_, v___x_1681_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1683_, lean_object* v_us_1684_, lean_object* v_useEq_1685_, lean_object* v_ctorVal_1686_, lean_object* v_params_1687_, lean_object* v_type_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
uint8_t v_useEq_boxed_1694_; lean_object* v_res_1695_; 
v_useEq_boxed_1694_ = lean_unbox(v_useEq_1685_);
v_res_1695_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1683_, v_us_1684_, v_useEq_boxed_1694_, v_ctorVal_1686_, v_params_1687_, v_type_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
if (lean_obj_tag(v_a_1696_) == 0)
{
lean_object* v___x_1698_; 
v___x_1698_ = l_List_reverse___redArg(v_a_1697_);
return v___x_1698_;
}
else
{
lean_object* v_head_1699_; lean_object* v_tail_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1709_; 
v_head_1699_ = lean_ctor_get(v_a_1696_, 0);
v_tail_1700_ = lean_ctor_get(v_a_1696_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_a_1696_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1702_ = v_a_1696_;
v_isShared_1703_ = v_isSharedCheck_1709_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_tail_1700_);
lean_inc(v_head_1699_);
lean_dec(v_a_1696_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1709_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = l_Lean_mkLevelParam(v_head_1699_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v_a_1697_);
lean_ctor_set(v___x_1702_, 0, v___x_1704_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_a_1697_);
v___x_1706_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
v_a_1696_ = v_tail_1700_;
v_a_1697_ = v___x_1706_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1710_, uint8_t v_useEq_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_toConstantVal_1717_; lean_object* v_numParams_1718_; lean_object* v_name_1719_; lean_object* v_levelParams_1720_; lean_object* v_type_1721_; lean_object* v___x_1722_; 
v_toConstantVal_1717_ = lean_ctor_get(v_ctorVal_1710_, 0);
v_numParams_1718_ = lean_ctor_get(v_ctorVal_1710_, 3);
lean_inc(v_numParams_1718_);
v_name_1719_ = lean_ctor_get(v_toConstantVal_1717_, 0);
lean_inc(v_name_1719_);
v_levelParams_1720_ = lean_ctor_get(v_toConstantVal_1717_, 1);
v_type_1721_ = lean_ctor_get(v_toConstantVal_1717_, 2);
lean_inc_ref(v_type_1721_);
v___x_1722_ = l_Lean_Meta_elimOptParam(v_type_1721_, v_a_1714_, v_a_1715_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; lean_object* v_us_1725_; lean_object* v___x_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = lean_box(0);
lean_inc(v_levelParams_1720_);
v_us_1725_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1720_, v___x_1724_);
v___x_1726_ = lean_box(v_useEq_1711_);
v___f_1727_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1727_, 0, v_name_1719_);
lean_closure_set(v___f_1727_, 1, v_us_1725_);
lean_closure_set(v___f_1727_, 2, v___x_1726_);
lean_closure_set(v___f_1727_, 3, v_ctorVal_1710_);
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v_numParams_1718_);
v___x_1729_ = 0;
v___x_1730_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1723_, v___x_1728_, v___f_1727_, v___x_1729_, v___x_1729_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
return v___x_1730_;
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_name_1719_);
lean_dec(v_numParams_1718_);
lean_dec_ref(v_ctorVal_1710_);
v_a_1731_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1722_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1722_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1739_, lean_object* v_useEq_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
uint8_t v_useEq_boxed_1746_; lean_object* v_res_1747_; 
v_useEq_boxed_1746_ = lean_unbox(v_useEq_1740_);
v_res_1747_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1739_, v_useEq_boxed_1746_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1748_, lean_object* v_bs_1749_, lean_object* v_k_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1749_, v_k_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_bs_1758_, lean_object* v_k_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1757_, v_bs_1758_, v_k_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v_bs_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1766_, lean_object* v_bs_1767_, lean_object* v_k_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1767_, v_k_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1775_, lean_object* v_bs_1776_, lean_object* v_k_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1775_, v_bs_1776_, v_k_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
uint8_t v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = 0;
v___x_1791_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1784_, v___x_1790_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
return v_res_1798_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1806_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1807_ = l_Lean_MessageData_ofName(v_ctorName_1805_);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1811_, lean_object* v_mvarId_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1818_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1811_);
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_mvarId_1812_);
v___x_1820_ = l_Lean_indentD(v___x_1819_);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1818_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1821_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1823_, lean_object* v_mvarId_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1823_, v_mvarId_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1831_, lean_object* v_ctorName_1832_, lean_object* v_mvarId_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1832_, v_mvarId_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1840_, lean_object* v_ctorName_1841_, lean_object* v_mvarId_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1840_, v_ctorName_1841_, v_mvarId_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1849_, lean_object* v_as_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
if (lean_obj_tag(v_as_1850_) == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v_ctorName_1849_);
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
else
{
lean_object* v_head_1858_; lean_object* v_tail_1859_; lean_object* v___x_1860_; 
v_head_1858_ = lean_ctor_get(v_as_1850_, 0);
lean_inc_n(v_head_1858_, 2);
v_tail_1859_ = lean_ctor_get(v_as_1850_, 1);
lean_inc(v_tail_1859_);
lean_dec_ref_known(v_as_1850_, 2);
v___x_1860_ = l_Lean_MVarId_assumptionCore(v_head_1858_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; uint8_t v___x_1862_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
v___x_1862_ = lean_unbox(v_a_1861_);
lean_dec(v_a_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; 
lean_dec(v_tail_1859_);
v___x_1863_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1849_, v_head_1858_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
return v___x_1863_;
}
else
{
lean_dec(v_head_1858_);
v_as_1850_ = v_tail_1859_;
goto _start;
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_tail_1859_);
lean_dec(v_head_1858_);
lean_dec(v_ctorName_1849_);
v_a_1865_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1860_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1860_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
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
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1873_, lean_object* v_as_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1873_, v_as_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1881_, lean_object* v_ctorName_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_MVarId_splitAndCore(v_mvarId_1881_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1890_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1882_, v_a_1889_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
return v___x_1890_;
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_ctorName_1882_);
v_a_1891_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1888_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1888_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1899_, lean_object* v_ctorName_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1899_, v_ctorName_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___f_1914_; lean_object* v___x_897__overap_1915_; lean_object* v___x_1916_; 
v___f_1914_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_897__overap_1915_ = lean_panic_fn_borrowed(v___f_1914_, v_msg_1908_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
v___x_1916_ = lean_apply_5(v___x_897__overap_1915_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, lean_box(0));
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1923_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1924_; double v___x_1925_; 
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = lean_float_of_nat(v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1929_, lean_object* v_msg_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_ref_1936_; lean_object* v___x_1937_; lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1982_; 
v_ref_1936_ = lean_ctor_get(v___y_1933_, 5);
v___x_1937_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1982_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1982_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v_traceState_1943_; lean_object* v_env_1944_; lean_object* v_nextMacroScope_1945_; lean_object* v_ngen_1946_; lean_object* v_auxDeclNGen_1947_; lean_object* v_cache_1948_; lean_object* v_messages_1949_; lean_object* v_infoState_1950_; lean_object* v_snapshotTasks_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1981_; 
v___x_1942_ = lean_st_ref_take(v___y_1934_);
v_traceState_1943_ = lean_ctor_get(v___x_1942_, 4);
v_env_1944_ = lean_ctor_get(v___x_1942_, 0);
v_nextMacroScope_1945_ = lean_ctor_get(v___x_1942_, 1);
v_ngen_1946_ = lean_ctor_get(v___x_1942_, 2);
v_auxDeclNGen_1947_ = lean_ctor_get(v___x_1942_, 3);
v_cache_1948_ = lean_ctor_get(v___x_1942_, 5);
v_messages_1949_ = lean_ctor_get(v___x_1942_, 6);
v_infoState_1950_ = lean_ctor_get(v___x_1942_, 7);
v_snapshotTasks_1951_ = lean_ctor_get(v___x_1942_, 8);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1953_ = v___x_1942_;
v_isShared_1954_ = v_isSharedCheck_1981_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_snapshotTasks_1951_);
lean_inc(v_infoState_1950_);
lean_inc(v_messages_1949_);
lean_inc(v_cache_1948_);
lean_inc(v_traceState_1943_);
lean_inc(v_auxDeclNGen_1947_);
lean_inc(v_ngen_1946_);
lean_inc(v_nextMacroScope_1945_);
lean_inc(v_env_1944_);
lean_dec(v___x_1942_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1981_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
uint64_t v_tid_1955_; lean_object* v_traces_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1980_; 
v_tid_1955_ = lean_ctor_get_uint64(v_traceState_1943_, sizeof(void*)*1);
v_traces_1956_ = lean_ctor_get(v_traceState_1943_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_traceState_1943_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1958_ = v_traceState_1943_;
v_isShared_1959_ = v_isSharedCheck_1980_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_traces_1956_);
lean_dec(v_traceState_1943_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1980_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; double v___x_1961_; uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1962_ = 0;
v___x_1963_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1964_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1964_, 0, v_cls_1929_);
lean_ctor_set(v___x_1964_, 1, v___x_1960_);
lean_ctor_set(v___x_1964_, 2, v___x_1963_);
lean_ctor_set_float(v___x_1964_, sizeof(void*)*3, v___x_1961_);
lean_ctor_set_float(v___x_1964_, sizeof(void*)*3 + 8, v___x_1961_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*3 + 16, v___x_1962_);
v___x_1965_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1966_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v_a_1938_);
lean_ctor_set(v___x_1966_, 2, v___x_1965_);
lean_inc(v_ref_1936_);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_ref_1936_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = l_Lean_PersistentArray_push___redArg(v_traces_1956_, v___x_1967_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1968_);
v___x_1970_ = v___x_1958_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1968_);
lean_ctor_set_uint64(v_reuseFailAlloc_1979_, sizeof(void*)*1, v_tid_1955_);
v___x_1970_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 4, v___x_1970_);
v___x_1972_ = v___x_1953_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_env_1944_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_nextMacroScope_1945_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_ngen_1946_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_auxDeclNGen_1947_);
lean_ctor_set(v_reuseFailAlloc_1978_, 4, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1978_, 5, v_cache_1948_);
lean_ctor_set(v_reuseFailAlloc_1978_, 6, v_messages_1949_);
lean_ctor_set(v_reuseFailAlloc_1978_, 7, v_infoState_1950_);
lean_ctor_set(v_reuseFailAlloc_1978_, 8, v_snapshotTasks_1951_);
v___x_1972_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1973_ = lean_st_ref_put(v___y_1934_, v___x_1972_);
v___x_1974_ = lean_box(0);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1974_);
v___x_1976_ = v___x_1940_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1983_, lean_object* v_msg_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1983_, v_msg_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1990_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1994_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1995_ = lean_unsigned_to_nat(30u);
v___x_1996_ = lean_unsigned_to_nat(96u);
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1998_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1999_ = l_mkPanicMessageWithDecl(v___x_1998_, v___x_1997_, v___x_1996_, v___x_1995_, v___x_1994_);
return v___x_1999_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_cls_2008_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2009_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_2010_ = l_Lean_Name_append(v___x_2009_, v_cls_2008_);
return v___x_2010_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_2013_ = l_Lean_stringToMessageData(v___x_2012_);
return v___x_2013_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_2016_ = l_Lean_stringToMessageData(v___x_2015_);
return v___x_2016_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2019_ = l_Lean_stringToMessageData(v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2020_, lean_object* v_mvarId_2021_, lean_object* v_h_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v_options_2048_; uint8_t v_hasTrace_2049_; 
v_options_2048_ = lean_ctor_get(v_a_2025_, 2);
v_hasTrace_2049_ = lean_ctor_get_uint8(v_options_2048_, sizeof(void*)*1);
if (v_hasTrace_2049_ == 0)
{
v___y_2029_ = v_a_2023_;
v___y_2030_ = v_a_2024_;
v___y_2031_ = v_a_2025_;
v___y_2032_ = v_a_2026_;
goto v___jp_2028_;
}
else
{
lean_object* v_inheritedTraceOptions_2050_; lean_object* v_cls_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_inheritedTraceOptions_2050_ = lean_ctor_get(v_a_2025_, 13);
v_cls_2051_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2052_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2053_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2050_, v_options_2048_, v___x_2052_);
if (v___x_2053_ == 0)
{
v___y_2029_ = v_a_2023_;
v___y_2030_ = v_a_2024_;
v___y_2031_ = v_a_2025_;
v___y_2032_ = v_a_2026_;
goto v___jp_2028_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2054_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2020_);
v___x_2055_ = l_Lean_MessageData_ofName(v_ctorName_2020_);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2054_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2056_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
lean_inc(v_h_2022_);
v___x_2059_ = l_Lean_mkFVar(v_h_2022_);
v___x_2060_ = l_Lean_MessageData_ofExpr(v___x_2059_);
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2058_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2061_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
lean_inc(v_mvarId_2021_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_mvarId_2021_);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2051_, v___x_2065_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_dec_ref_known(v___x_2066_, 1);
v___y_2029_ = v_a_2023_;
v___y_2030_ = v_a_2024_;
v___y_2031_ = v_a_2025_;
v___y_2032_ = v_a_2026_;
goto v___jp_2028_;
}
else
{
lean_dec(v_h_2022_);
lean_dec(v_mvarId_2021_);
lean_dec(v_ctorName_2020_);
return v___x_2066_;
}
}
}
v___jp_2028_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_box(0);
v___x_2034_ = l_Lean_Meta_injection(v_mvarId_2021_, v_h_2022_, v___x_2033_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
if (lean_obj_tag(v_a_2035_) == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec(v_ctorName_2020_);
v___x_2036_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2037_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2036_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2037_;
}
else
{
lean_object* v_mvarId_2038_; lean_object* v___x_2039_; 
v_mvarId_2038_ = lean_ctor_get(v_a_2035_, 0);
lean_inc(v_mvarId_2038_);
lean_dec_ref_known(v_a_2035_, 3);
v___x_2039_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2038_, v_ctorName_2020_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2039_;
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_ctorName_2020_);
v_a_2040_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2034_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2034_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2067_, lean_object* v_mvarId_2068_, lean_object* v_h_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2067_, v_mvarId_2068_, v_h_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2076_, lean_object* v_k_2077_, uint8_t v_cleanupAnnotations_2078_, uint8_t v_whnfType_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___f_2085_; lean_object* v___x_2086_; 
v___f_2085_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2085_, 0, v_k_2077_);
v___x_2086_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2076_, v___f_2085_, v_cleanupAnnotations_2078_, v_whnfType_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
v_a_2095_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2086_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2086_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2103_, lean_object* v_k_2104_, lean_object* v_cleanupAnnotations_2105_, lean_object* v_whnfType_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2112_; uint8_t v_whnfType_boxed_2113_; lean_object* v_res_2114_; 
v_cleanupAnnotations_boxed_2112_ = lean_unbox(v_cleanupAnnotations_2105_);
v_whnfType_boxed_2113_ = lean_unbox(v_whnfType_2106_);
v_res_2114_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2103_, v_k_2104_, v_cleanupAnnotations_boxed_2112_, v_whnfType_boxed_2113_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2115_, lean_object* v_type_2116_, lean_object* v_k_2117_, uint8_t v_cleanupAnnotations_2118_, uint8_t v_whnfType_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2116_, v_k_2117_, v_cleanupAnnotations_2118_, v_whnfType_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2126_, lean_object* v_type_2127_, lean_object* v_k_2128_, lean_object* v_cleanupAnnotations_2129_, lean_object* v_whnfType_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2136_; uint8_t v_whnfType_boxed_2137_; lean_object* v_res_2138_; 
v_cleanupAnnotations_boxed_2136_ = lean_unbox(v_cleanupAnnotations_2129_);
v_whnfType_boxed_2137_ = lean_unbox(v_whnfType_2130_);
v_res_2138_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2126_, v_type_2127_, v_k_2128_, v_cleanupAnnotations_boxed_2136_, v_whnfType_boxed_2137_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2139_, lean_object* v_ctorName_2140_, lean_object* v_xs_2141_, lean_object* v_type_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2142_, v___x_2148_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = l_Lean_Expr_mvarId_x21(v_a_2150_);
v___x_2152_ = lean_array_get_size(v_xs_2141_);
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = lean_nat_sub(v___x_2152_, v___x_2153_);
v___x_2155_ = lean_array_get_borrowed(v___x_2139_, v_xs_2141_, v___x_2154_);
lean_dec(v___x_2154_);
v___x_2156_ = l_Lean_Expr_fvarId_x21(v___x_2155_);
v___x_2157_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2140_, v___x_2151_, v___x_2156_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2157_) == 0)
{
uint8_t v___x_2158_; uint8_t v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref_known(v___x_2157_, 1);
v___x_2158_ = 0;
v___x_2159_ = 1;
v___x_2160_ = 1;
v___x_2161_ = l_Lean_Meta_mkLambdaFVars(v_xs_2141_, v_a_2150_, v___x_2158_, v___x_2159_, v___x_2158_, v___x_2159_, v___x_2160_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2161_;
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_a_2150_);
v_a_2162_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2157_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2157_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_dec(v_ctorName_2140_);
return v___x_2149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2170_, lean_object* v_ctorName_2171_, lean_object* v_xs_2172_, lean_object* v_type_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2170_, v_ctorName_2171_, v_xs_2172_, v_type_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec_ref(v_xs_2172_);
lean_dec_ref(v___x_2170_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2180_, lean_object* v_targetType_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v___x_2187_; lean_object* v___f_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = l_Lean_instInhabitedExpr;
v___f_2188_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2188_, 0, v___x_2187_);
lean_closure_set(v___f_2188_, 1, v_ctorName_2180_);
v___x_2189_ = 0;
v___x_2190_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2181_, v___f_2188_, v___x_2189_, v___x_2189_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2191_, lean_object* v_targetType_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2191_, v_targetType_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2202_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2204_ = l_Lean_Name_append(v_ctorName_2202_, v___x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v___x_2208_; 
v___x_2208_ = l_Lean_Expr_hasMVar(v_e_2205_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_e_2205_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v_mctx_2211_; lean_object* v___x_2212_; lean_object* v_fst_2213_; lean_object* v_snd_2214_; lean_object* v___x_2215_; lean_object* v_cache_2216_; lean_object* v_zetaDeltaFVarIds_2217_; lean_object* v_postponed_2218_; lean_object* v_diag_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2228_; 
v___x_2210_ = lean_st_ref_get(v___y_2206_);
v_mctx_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc_ref(v_mctx_2211_);
lean_dec(v___x_2210_);
v___x_2212_ = l_Lean_instantiateMVarsCore(v_mctx_2211_, v_e_2205_);
v_fst_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_fst_2213_);
v_snd_2214_ = lean_ctor_get(v___x_2212_, 1);
lean_inc(v_snd_2214_);
lean_dec_ref(v___x_2212_);
v___x_2215_ = lean_st_ref_take(v___y_2206_);
v_cache_2216_ = lean_ctor_get(v___x_2215_, 1);
v_zetaDeltaFVarIds_2217_ = lean_ctor_get(v___x_2215_, 2);
v_postponed_2218_ = lean_ctor_get(v___x_2215_, 3);
v_diag_2219_ = lean_ctor_get(v___x_2215_, 4);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2215_, 0);
lean_dec(v_unused_2229_);
v___x_2221_ = v___x_2215_;
v_isShared_2222_ = v_isSharedCheck_2228_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_diag_2219_);
lean_inc(v_postponed_2218_);
lean_inc(v_zetaDeltaFVarIds_2217_);
lean_inc(v_cache_2216_);
lean_dec(v___x_2215_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2228_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v_snd_2214_);
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_snd_2214_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_cache_2216_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_zetaDeltaFVarIds_2217_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_postponed_2218_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_diag_2219_);
v___x_2224_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_st_ref_put(v___y_2206_, v___x_2224_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_fst_2213_);
return v___x_2226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2230_, v___y_2231_);
lean_dec(v___y_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2234_, v___y_2236_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_unsigned_to_nat(32u);
v___x_2249_ = lean_mk_empty_array_with_capacity(v___x_2248_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2251_ = ((size_t)5ULL);
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_unsigned_to_nat(32u);
v___x_2254_ = lean_mk_empty_array_with_capacity(v___x_2253_);
v___x_2255_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2256_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v___x_2254_);
lean_ctor_set(v___x_2256_, 2, v___x_2252_);
lean_ctor_set(v___x_2256_, 3, v___x_2252_);
lean_ctor_set_usize(v___x_2256_, 4, v___x_2251_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; lean_object* v_traceState_2260_; lean_object* v_traces_2261_; lean_object* v___x_2262_; lean_object* v_traceState_2263_; lean_object* v_env_2264_; lean_object* v_nextMacroScope_2265_; lean_object* v_ngen_2266_; lean_object* v_auxDeclNGen_2267_; lean_object* v_cache_2268_; lean_object* v_messages_2269_; lean_object* v_infoState_2270_; lean_object* v_snapshotTasks_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2290_; 
v___x_2259_ = lean_st_ref_get(v___y_2257_);
v_traceState_2260_ = lean_ctor_get(v___x_2259_, 4);
lean_inc_ref(v_traceState_2260_);
lean_dec(v___x_2259_);
v_traces_2261_ = lean_ctor_get(v_traceState_2260_, 0);
lean_inc_ref(v_traces_2261_);
lean_dec_ref(v_traceState_2260_);
v___x_2262_ = lean_st_ref_take(v___y_2257_);
v_traceState_2263_ = lean_ctor_get(v___x_2262_, 4);
v_env_2264_ = lean_ctor_get(v___x_2262_, 0);
v_nextMacroScope_2265_ = lean_ctor_get(v___x_2262_, 1);
v_ngen_2266_ = lean_ctor_get(v___x_2262_, 2);
v_auxDeclNGen_2267_ = lean_ctor_get(v___x_2262_, 3);
v_cache_2268_ = lean_ctor_get(v___x_2262_, 5);
v_messages_2269_ = lean_ctor_get(v___x_2262_, 6);
v_infoState_2270_ = lean_ctor_get(v___x_2262_, 7);
v_snapshotTasks_2271_ = lean_ctor_get(v___x_2262_, 8);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2273_ = v___x_2262_;
v_isShared_2274_ = v_isSharedCheck_2290_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_snapshotTasks_2271_);
lean_inc(v_infoState_2270_);
lean_inc(v_messages_2269_);
lean_inc(v_cache_2268_);
lean_inc(v_traceState_2263_);
lean_inc(v_auxDeclNGen_2267_);
lean_inc(v_ngen_2266_);
lean_inc(v_nextMacroScope_2265_);
lean_inc(v_env_2264_);
lean_dec(v___x_2262_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2290_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
uint64_t v_tid_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2288_; 
v_tid_2275_ = lean_ctor_get_uint64(v_traceState_2263_, sizeof(void*)*1);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_traceState_2263_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; 
v_unused_2289_ = lean_ctor_get(v_traceState_2263_, 0);
lean_dec(v_unused_2289_);
v___x_2277_ = v_traceState_2263_;
v_isShared_2278_ = v_isSharedCheck_2288_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_traceState_2263_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2288_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2279_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2279_);
v___x_2281_ = v___x_2277_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2279_);
lean_ctor_set_uint64(v_reuseFailAlloc_2287_, sizeof(void*)*1, v_tid_2275_);
v___x_2281_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
lean_object* v___x_2283_; 
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 4, v___x_2281_);
v___x_2283_ = v___x_2273_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_env_2264_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_nextMacroScope_2265_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v_ngen_2266_);
lean_ctor_set(v_reuseFailAlloc_2286_, 3, v_auxDeclNGen_2267_);
lean_ctor_set(v_reuseFailAlloc_2286_, 4, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2286_, 5, v_cache_2268_);
lean_ctor_set(v_reuseFailAlloc_2286_, 6, v_messages_2269_);
lean_ctor_set(v_reuseFailAlloc_2286_, 7, v_infoState_2270_);
lean_ctor_set(v_reuseFailAlloc_2286_, 8, v_snapshotTasks_2271_);
v___x_2283_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = lean_st_ref_put(v___y_2257_, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v_traces_2261_);
return v___x_2285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2291_);
lean_dec(v___y_2291_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2305_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2306_, lean_object* v_opt_2307_){
_start:
{
lean_object* v_name_2308_; lean_object* v_defValue_2309_; lean_object* v_map_2310_; lean_object* v___x_2311_; 
v_name_2308_ = lean_ctor_get(v_opt_2307_, 0);
v_defValue_2309_ = lean_ctor_get(v_opt_2307_, 1);
v_map_2310_ = lean_ctor_get(v_opts_2306_, 0);
v___x_2311_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2310_, v_name_2308_);
if (lean_obj_tag(v___x_2311_) == 0)
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_unbox(v_defValue_2309_);
return v___x_2312_;
}
else
{
lean_object* v_val_2313_; 
v_val_2313_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_val_2313_);
lean_dec_ref_known(v___x_2311_, 1);
if (lean_obj_tag(v_val_2313_) == 1)
{
uint8_t v_v_2314_; 
v_v_2314_ = lean_ctor_get_uint8(v_val_2313_, 0);
lean_dec_ref_known(v_val_2313_, 0);
return v_v_2314_;
}
else
{
uint8_t v___x_2315_; 
lean_dec(v_val_2313_);
v___x_2315_ = lean_unbox(v_defValue_2309_);
return v___x_2315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2316_, lean_object* v_opt_2317_){
_start:
{
uint8_t v_res_2318_; lean_object* v_r_2319_; 
v_res_2318_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2316_, v_opt_2317_);
lean_dec_ref(v_opt_2317_);
lean_dec_ref(v_opts_2316_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2323_, lean_object* v_x_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2330_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2331_ = l_Lean_MessageData_ofName(v_name_2323_);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2336_, lean_object* v_x_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2336_, v_x_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec_ref(v_x_2337_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2344_, lean_object* v_val_2345_, lean_object* v_name_2346_, lean_object* v_levelParams_2347_, uint8_t v___x_2348_, lean_object* v_____r_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
lean_inc_ref(v_val_2345_);
v___x_2355_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2344_, v_val_2345_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2357_; lean_object* v_a_2358_; lean_object* v___x_2359_; lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2372_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v___x_2357_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2345_, v___y_2351_);
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2357_);
v___x_2359_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2356_, v___y_2351_);
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2372_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_inc(v_name_2346_);
v___x_2364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2364_, 0, v_name_2346_);
lean_ctor_set(v___x_2364_, 1, v_levelParams_2347_);
lean_ctor_set(v___x_2364_, 2, v_a_2358_);
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_name_2346_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2364_);
lean_ctor_set(v___x_2367_, 1, v_a_2360_);
lean_ctor_set(v___x_2367_, 2, v___x_2366_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set_tag(v___x_2362_, 2);
lean_ctor_set(v___x_2362_, 0, v___x_2367_);
v___x_2369_ = v___x_2362_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_addDecl(v___x_2369_, v___x_2348_, v___y_2352_, v___y_2353_);
return v___x_2370_;
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_levelParams_2347_);
lean_dec(v_name_2346_);
lean_dec_ref(v_val_2345_);
v_a_2373_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2355_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2355_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2381_, lean_object* v_val_2382_, lean_object* v_name_2383_, lean_object* v_levelParams_2384_, lean_object* v___x_2385_, lean_object* v_____r_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
uint8_t v___x_12438__boxed_2392_; lean_object* v_res_2393_; 
v___x_12438__boxed_2392_ = lean_unbox(v___x_2385_);
v_res_2393_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2381_, v_val_2382_, v_name_2383_, v_levelParams_2384_, v___x_12438__boxed_2392_, v_____r_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2394_, lean_object* v_val_2395_, lean_object* v_name_2396_, lean_object* v_levelParams_2397_, lean_object* v_____r_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
lean_inc_ref(v_val_2395_);
v___x_2404_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2394_, v_val_2395_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; lean_object* v_a_2407_; lean_object* v___x_2408_; lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2422_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2395_, v___y_2400_);
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2406_);
v___x_2408_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2405_, v___y_2400_);
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2422_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2422_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
lean_inc(v_name_2396_);
v___x_2413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2413_, 0, v_name_2396_);
lean_ctor_set(v___x_2413_, 1, v_levelParams_2397_);
lean_ctor_set(v___x_2413_, 2, v_a_2407_);
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2415_, 0, v_name_2396_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2413_);
lean_ctor_set(v___x_2416_, 1, v_a_2409_);
lean_ctor_set(v___x_2416_, 2, v___x_2415_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 2);
lean_ctor_set(v___x_2411_, 0, v___x_2416_);
v___x_2418_ = v___x_2411_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
uint8_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = 0;
v___x_2420_ = l_Lean_addDecl(v___x_2418_, v___x_2419_, v___y_2401_, v___y_2402_);
return v___x_2420_;
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v_levelParams_2397_);
lean_dec(v_name_2396_);
lean_dec_ref(v_val_2395_);
v_a_2423_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2404_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2404_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2431_, lean_object* v_val_2432_, lean_object* v_name_2433_, lean_object* v_levelParams_2434_, lean_object* v_____r_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2431_, v_val_2432_, v_name_2433_, v_levelParams_2434_, v_____r_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t v_sz_2442_, size_t v_i_2443_, lean_object* v_bs_2444_){
_start:
{
uint8_t v___x_2445_; 
v___x_2445_ = lean_usize_dec_lt(v_i_2443_, v_sz_2442_);
if (v___x_2445_ == 0)
{
return v_bs_2444_;
}
else
{
lean_object* v_v_2446_; lean_object* v_msg_2447_; lean_object* v___x_2448_; lean_object* v_bs_x27_2449_; size_t v___x_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
v_v_2446_ = lean_array_uget_borrowed(v_bs_2444_, v_i_2443_);
v_msg_2447_ = lean_ctor_get(v_v_2446_, 1);
lean_inc_ref(v_msg_2447_);
v___x_2448_ = lean_unsigned_to_nat(0u);
v_bs_x27_2449_ = lean_array_uset(v_bs_2444_, v_i_2443_, v___x_2448_);
v___x_2450_ = ((size_t)1ULL);
v___x_2451_ = lean_usize_add(v_i_2443_, v___x_2450_);
v___x_2452_ = lean_array_uset(v_bs_x27_2449_, v_i_2443_, v_msg_2447_);
v_i_2443_ = v___x_2451_;
v_bs_2444_ = v___x_2452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2454_, lean_object* v_i_2455_, lean_object* v_bs_2456_){
_start:
{
size_t v_sz_boxed_2457_; size_t v_i_boxed_2458_; lean_object* v_res_2459_; 
v_sz_boxed_2457_ = lean_unbox_usize(v_sz_2454_);
lean_dec(v_sz_2454_);
v_i_boxed_2458_ = lean_unbox_usize(v_i_2455_);
lean_dec(v_i_2455_);
v_res_2459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_boxed_2457_, v_i_boxed_2458_, v_bs_2456_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_oldTraces_2460_, lean_object* v_data_2461_, lean_object* v_ref_2462_, lean_object* v_msg_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_fileName_2469_; lean_object* v_fileMap_2470_; lean_object* v_options_2471_; lean_object* v_currRecDepth_2472_; lean_object* v_maxRecDepth_2473_; lean_object* v_ref_2474_; lean_object* v_currNamespace_2475_; lean_object* v_openDecls_2476_; lean_object* v_initHeartbeats_2477_; lean_object* v_maxHeartbeats_2478_; lean_object* v_quotContext_2479_; lean_object* v_currMacroScope_2480_; uint8_t v_diag_2481_; lean_object* v_cancelTk_x3f_2482_; uint8_t v_suppressElabErrors_2483_; lean_object* v_inheritedTraceOptions_2484_; lean_object* v___x_2485_; lean_object* v_traceState_2486_; lean_object* v_traces_2487_; lean_object* v_ref_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; size_t v_sz_2491_; size_t v___x_2492_; lean_object* v___x_2493_; lean_object* v_msg_2494_; lean_object* v___x_2495_; lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2533_; 
v_fileName_2469_ = lean_ctor_get(v___y_2466_, 0);
v_fileMap_2470_ = lean_ctor_get(v___y_2466_, 1);
v_options_2471_ = lean_ctor_get(v___y_2466_, 2);
v_currRecDepth_2472_ = lean_ctor_get(v___y_2466_, 3);
v_maxRecDepth_2473_ = lean_ctor_get(v___y_2466_, 4);
v_ref_2474_ = lean_ctor_get(v___y_2466_, 5);
v_currNamespace_2475_ = lean_ctor_get(v___y_2466_, 6);
v_openDecls_2476_ = lean_ctor_get(v___y_2466_, 7);
v_initHeartbeats_2477_ = lean_ctor_get(v___y_2466_, 8);
v_maxHeartbeats_2478_ = lean_ctor_get(v___y_2466_, 9);
v_quotContext_2479_ = lean_ctor_get(v___y_2466_, 10);
v_currMacroScope_2480_ = lean_ctor_get(v___y_2466_, 11);
v_diag_2481_ = lean_ctor_get_uint8(v___y_2466_, sizeof(void*)*14);
v_cancelTk_x3f_2482_ = lean_ctor_get(v___y_2466_, 12);
v_suppressElabErrors_2483_ = lean_ctor_get_uint8(v___y_2466_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2484_ = lean_ctor_get(v___y_2466_, 13);
v___x_2485_ = lean_st_ref_get(v___y_2467_);
v_traceState_2486_ = lean_ctor_get(v___x_2485_, 4);
lean_inc_ref(v_traceState_2486_);
lean_dec(v___x_2485_);
v_traces_2487_ = lean_ctor_get(v_traceState_2486_, 0);
lean_inc_ref(v_traces_2487_);
lean_dec_ref(v_traceState_2486_);
v_ref_2488_ = l_Lean_replaceRef(v_ref_2462_, v_ref_2474_);
lean_inc_ref(v_inheritedTraceOptions_2484_);
lean_inc(v_cancelTk_x3f_2482_);
lean_inc(v_currMacroScope_2480_);
lean_inc(v_quotContext_2479_);
lean_inc(v_maxHeartbeats_2478_);
lean_inc(v_initHeartbeats_2477_);
lean_inc(v_openDecls_2476_);
lean_inc(v_currNamespace_2475_);
lean_inc(v_maxRecDepth_2473_);
lean_inc(v_currRecDepth_2472_);
lean_inc_ref(v_options_2471_);
lean_inc_ref(v_fileMap_2470_);
lean_inc_ref(v_fileName_2469_);
v___x_2489_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2489_, 0, v_fileName_2469_);
lean_ctor_set(v___x_2489_, 1, v_fileMap_2470_);
lean_ctor_set(v___x_2489_, 2, v_options_2471_);
lean_ctor_set(v___x_2489_, 3, v_currRecDepth_2472_);
lean_ctor_set(v___x_2489_, 4, v_maxRecDepth_2473_);
lean_ctor_set(v___x_2489_, 5, v_ref_2488_);
lean_ctor_set(v___x_2489_, 6, v_currNamespace_2475_);
lean_ctor_set(v___x_2489_, 7, v_openDecls_2476_);
lean_ctor_set(v___x_2489_, 8, v_initHeartbeats_2477_);
lean_ctor_set(v___x_2489_, 9, v_maxHeartbeats_2478_);
lean_ctor_set(v___x_2489_, 10, v_quotContext_2479_);
lean_ctor_set(v___x_2489_, 11, v_currMacroScope_2480_);
lean_ctor_set(v___x_2489_, 12, v_cancelTk_x3f_2482_);
lean_ctor_set(v___x_2489_, 13, v_inheritedTraceOptions_2484_);
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*14, v_diag_2481_);
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*14 + 1, v_suppressElabErrors_2483_);
v___x_2490_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2487_);
lean_dec_ref(v_traces_2487_);
v_sz_2491_ = lean_array_size(v___x_2490_);
v___x_2492_ = ((size_t)0ULL);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_2491_, v___x_2492_, v___x_2490_);
v_msg_2494_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2494_, 0, v_data_2461_);
lean_ctor_set(v_msg_2494_, 1, v_msg_2463_);
lean_ctor_set(v_msg_2494_, 2, v___x_2493_);
v___x_2495_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2494_, v___y_2464_, v___y_2465_, v___x_2489_, v___y_2467_);
lean_dec_ref_known(v___x_2489_, 14);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2533_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2533_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v_traceState_2501_; lean_object* v_env_2502_; lean_object* v_nextMacroScope_2503_; lean_object* v_ngen_2504_; lean_object* v_auxDeclNGen_2505_; lean_object* v_cache_2506_; lean_object* v_messages_2507_; lean_object* v_infoState_2508_; lean_object* v_snapshotTasks_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2532_; 
v___x_2500_ = lean_st_ref_take(v___y_2467_);
v_traceState_2501_ = lean_ctor_get(v___x_2500_, 4);
v_env_2502_ = lean_ctor_get(v___x_2500_, 0);
v_nextMacroScope_2503_ = lean_ctor_get(v___x_2500_, 1);
v_ngen_2504_ = lean_ctor_get(v___x_2500_, 2);
v_auxDeclNGen_2505_ = lean_ctor_get(v___x_2500_, 3);
v_cache_2506_ = lean_ctor_get(v___x_2500_, 5);
v_messages_2507_ = lean_ctor_get(v___x_2500_, 6);
v_infoState_2508_ = lean_ctor_get(v___x_2500_, 7);
v_snapshotTasks_2509_ = lean_ctor_get(v___x_2500_, 8);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2511_ = v___x_2500_;
v_isShared_2512_ = v_isSharedCheck_2532_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_snapshotTasks_2509_);
lean_inc(v_infoState_2508_);
lean_inc(v_messages_2507_);
lean_inc(v_cache_2506_);
lean_inc(v_traceState_2501_);
lean_inc(v_auxDeclNGen_2505_);
lean_inc(v_ngen_2504_);
lean_inc(v_nextMacroScope_2503_);
lean_inc(v_env_2502_);
lean_dec(v___x_2500_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2532_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
uint64_t v_tid_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2530_; 
v_tid_2513_ = lean_ctor_get_uint64(v_traceState_2501_, sizeof(void*)*1);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_traceState_2501_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_traceState_2501_, 0);
lean_dec(v_unused_2531_);
v___x_2515_ = v_traceState_2501_;
v_isShared_2516_ = v_isSharedCheck_2530_;
goto v_resetjp_2514_;
}
else
{
lean_dec(v_traceState_2501_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2530_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_ref_2462_);
lean_ctor_set(v___x_2517_, 1, v_a_2496_);
v___x_2518_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2460_, v___x_2517_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2518_);
v___x_2520_ = v___x_2515_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2518_);
lean_ctor_set_uint64(v_reuseFailAlloc_2529_, sizeof(void*)*1, v_tid_2513_);
v___x_2520_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 4, v___x_2520_);
v___x_2522_ = v___x_2511_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_env_2502_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_nextMacroScope_2503_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_ngen_2504_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v_auxDeclNGen_2505_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2528_, 5, v_cache_2506_);
lean_ctor_set(v_reuseFailAlloc_2528_, 6, v_messages_2507_);
lean_ctor_set(v_reuseFailAlloc_2528_, 7, v_infoState_2508_);
lean_ctor_set(v_reuseFailAlloc_2528_, 8, v_snapshotTasks_2509_);
v___x_2522_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2523_ = lean_st_ref_put(v___y_2467_, v___x_2522_);
v___x_2524_ = lean_box(0);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2524_);
v___x_2526_ = v___x_2498_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2524_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_oldTraces_2534_, lean_object* v_data_2535_, lean_object* v_ref_2536_, lean_object* v_msg_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2534_, v_data_2535_, v_ref_2536_, v_msg_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2544_, lean_object* v_opt_2545_){
_start:
{
lean_object* v_name_2546_; lean_object* v_defValue_2547_; lean_object* v_map_2548_; lean_object* v___x_2549_; 
v_name_2546_ = lean_ctor_get(v_opt_2545_, 0);
v_defValue_2547_ = lean_ctor_get(v_opt_2545_, 1);
v_map_2548_ = lean_ctor_get(v_opts_2544_, 0);
v___x_2549_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2548_, v_name_2546_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_inc(v_defValue_2547_);
return v_defValue_2547_;
}
else
{
lean_object* v_val_2550_; 
v_val_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_val_2550_);
lean_dec_ref_known(v___x_2549_, 1);
if (lean_obj_tag(v_val_2550_) == 3)
{
lean_object* v_v_2551_; 
v_v_2551_ = lean_ctor_get(v_val_2550_, 0);
lean_inc(v_v_2551_);
lean_dec_ref_known(v_val_2550_, 1);
return v_v_2551_;
}
else
{
lean_dec(v_val_2550_);
lean_inc(v_defValue_2547_);
return v_defValue_2547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2552_, lean_object* v_opt_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2552_, v_opt_2553_);
lean_dec_ref(v_opt_2553_);
lean_dec_ref(v_opts_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_e_2555_){
_start:
{
if (lean_obj_tag(v_e_2555_) == 0)
{
uint8_t v___x_2556_; 
v___x_2556_ = 2;
return v___x_2556_;
}
else
{
uint8_t v___x_2557_; 
v___x_2557_ = 0;
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_e_2558_){
_start:
{
uint8_t v_res_2559_; lean_object* v_r_2560_; 
v_res_2559_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_e_2558_);
lean_dec_ref(v_e_2558_);
v_r_2560_ = lean_box(v_res_2559_);
return v_r_2560_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object* v_x_2561_){
_start:
{
if (lean_obj_tag(v_x_2561_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_a_2563_ = lean_ctor_get(v_x_2561_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_x_2561_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v_x_2561_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v_x_2561_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set_tag(v___x_2565_, 1);
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
v_a_2571_ = lean_ctor_get(v_x_2561_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_x_2561_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v_x_2561_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v_x_2561_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 0);
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object* v_x_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2579_);
return v_res_2581_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2584_ = l_Lean_stringToMessageData(v___x_2583_);
return v___x_2584_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2585_; double v___x_2586_; 
v___x_2585_ = lean_unsigned_to_nat(1000u);
v___x_2586_ = lean_float_of_nat(v___x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2587_, uint8_t v_collapsed_2588_, lean_object* v_tag_2589_, lean_object* v_opts_2590_, uint8_t v_clsEnabled_2591_, lean_object* v_oldTraces_2592_, lean_object* v_msg_2593_, lean_object* v_resStartStop_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_fst_2600_; lean_object* v_snd_2601_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v_data_2605_; lean_object* v_fst_2608_; lean_object* v_snd_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; lean_object* v___y_2613_; lean_object* v_a_2614_; uint8_t v___y_2629_; double v___y_2660_; 
v_fst_2600_ = lean_ctor_get(v_resStartStop_2594_, 0);
lean_inc(v_fst_2600_);
v_snd_2601_ = lean_ctor_get(v_resStartStop_2594_, 1);
lean_inc(v_snd_2601_);
lean_dec_ref(v_resStartStop_2594_);
v_fst_2608_ = lean_ctor_get(v_snd_2601_, 0);
lean_inc(v_fst_2608_);
v_snd_2609_ = lean_ctor_get(v_snd_2601_, 1);
lean_inc(v_snd_2609_);
lean_dec(v_snd_2601_);
v___x_2610_ = l_Lean_trace_profiler;
v___x_2611_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2590_, v___x_2610_);
if (v___x_2611_ == 0)
{
v___y_2629_ = v___x_2611_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2666_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2590_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; double v___x_2669_; double v___x_2670_; double v___x_2671_; 
v___x_2667_ = l_Lean_trace_profiler_threshold;
v___x_2668_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2590_, v___x_2667_);
v___x_2669_ = lean_float_of_nat(v___x_2668_);
v___x_2670_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2);
v___x_2671_ = lean_float_div(v___x_2669_, v___x_2670_);
v___y_2660_ = v___x_2671_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; double v___x_2674_; 
v___x_2672_ = l_Lean_trace_profiler_threshold;
v___x_2673_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2590_, v___x_2672_);
v___x_2674_ = lean_float_of_nat(v___x_2673_);
v___y_2660_ = v___x_2674_;
goto v___jp_2659_;
}
}
v___jp_2602_:
{
lean_object* v___x_2606_; 
lean_inc(v___y_2603_);
v___x_2606_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2592_, v_data_2605_, v___y_2603_, v___y_2604_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v___x_2607_; 
lean_dec_ref_known(v___x_2606_, 1);
v___x_2607_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2600_);
return v___x_2607_;
}
else
{
lean_dec(v_fst_2600_);
return v___x_2606_;
}
}
v___jp_2612_:
{
uint8_t v_result_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; double v___x_2618_; lean_object* v_data_2619_; 
v_result_2615_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_fst_2600_);
v___x_2616_ = lean_box(v_result_2615_);
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
v___x_2618_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2589_);
lean_inc_ref(v___x_2617_);
lean_inc(v_cls_2587_);
v_data_2619_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2619_, 0, v_cls_2587_);
lean_ctor_set(v_data_2619_, 1, v___x_2617_);
lean_ctor_set(v_data_2619_, 2, v_tag_2589_);
lean_ctor_set_float(v_data_2619_, sizeof(void*)*3, v___x_2618_);
lean_ctor_set_float(v_data_2619_, sizeof(void*)*3 + 8, v___x_2618_);
lean_ctor_set_uint8(v_data_2619_, sizeof(void*)*3 + 16, v_collapsed_2588_);
if (v___x_2611_ == 0)
{
lean_dec_ref_known(v___x_2617_, 1);
lean_dec(v_snd_2609_);
lean_dec(v_fst_2608_);
lean_dec_ref(v_tag_2589_);
lean_dec(v_cls_2587_);
v___y_2603_ = v___y_2613_;
v___y_2604_ = v_a_2614_;
v_data_2605_ = v_data_2619_;
goto v___jp_2602_;
}
else
{
lean_object* v_data_2620_; double v___x_2621_; double v___x_2622_; 
lean_dec_ref_known(v_data_2619_, 3);
v_data_2620_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2620_, 0, v_cls_2587_);
lean_ctor_set(v_data_2620_, 1, v___x_2617_);
lean_ctor_set(v_data_2620_, 2, v_tag_2589_);
v___x_2621_ = lean_unbox_float(v_fst_2608_);
lean_dec(v_fst_2608_);
lean_ctor_set_float(v_data_2620_, sizeof(void*)*3, v___x_2621_);
v___x_2622_ = lean_unbox_float(v_snd_2609_);
lean_dec(v_snd_2609_);
lean_ctor_set_float(v_data_2620_, sizeof(void*)*3 + 8, v___x_2622_);
lean_ctor_set_uint8(v_data_2620_, sizeof(void*)*3 + 16, v_collapsed_2588_);
v___y_2603_ = v___y_2613_;
v___y_2604_ = v_a_2614_;
v_data_2605_ = v_data_2620_;
goto v___jp_2602_;
}
}
v___jp_2623_:
{
lean_object* v_ref_2624_; lean_object* v___x_2625_; 
v_ref_2624_ = lean_ctor_get(v___y_2597_, 5);
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
lean_inc(v___y_2596_);
lean_inc_ref(v___y_2595_);
lean_inc(v_fst_2600_);
v___x_2625_ = lean_apply_6(v_msg_2593_, v_fst_2600_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, lean_box(0));
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___y_2613_ = v_ref_2624_;
v_a_2614_ = v_a_2626_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2627_; 
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
v___y_2613_ = v_ref_2624_;
v_a_2614_ = v___x_2627_;
goto v___jp_2612_;
}
}
v___jp_2628_:
{
if (v_clsEnabled_2591_ == 0)
{
if (v___y_2629_ == 0)
{
lean_object* v___x_2630_; lean_object* v_traceState_2631_; lean_object* v_env_2632_; lean_object* v_nextMacroScope_2633_; lean_object* v_ngen_2634_; lean_object* v_auxDeclNGen_2635_; lean_object* v_cache_2636_; lean_object* v_messages_2637_; lean_object* v_infoState_2638_; lean_object* v_snapshotTasks_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v_snd_2609_);
lean_dec(v_fst_2608_);
lean_dec_ref(v_msg_2593_);
lean_dec_ref(v_tag_2589_);
lean_dec(v_cls_2587_);
v___x_2630_ = lean_st_ref_take(v___y_2598_);
v_traceState_2631_ = lean_ctor_get(v___x_2630_, 4);
v_env_2632_ = lean_ctor_get(v___x_2630_, 0);
v_nextMacroScope_2633_ = lean_ctor_get(v___x_2630_, 1);
v_ngen_2634_ = lean_ctor_get(v___x_2630_, 2);
v_auxDeclNGen_2635_ = lean_ctor_get(v___x_2630_, 3);
v_cache_2636_ = lean_ctor_get(v___x_2630_, 5);
v_messages_2637_ = lean_ctor_get(v___x_2630_, 6);
v_infoState_2638_ = lean_ctor_get(v___x_2630_, 7);
v_snapshotTasks_2639_ = lean_ctor_get(v___x_2630_, 8);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2641_ = v___x_2630_;
v_isShared_2642_ = v_isSharedCheck_2658_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_snapshotTasks_2639_);
lean_inc(v_infoState_2638_);
lean_inc(v_messages_2637_);
lean_inc(v_cache_2636_);
lean_inc(v_traceState_2631_);
lean_inc(v_auxDeclNGen_2635_);
lean_inc(v_ngen_2634_);
lean_inc(v_nextMacroScope_2633_);
lean_inc(v_env_2632_);
lean_dec(v___x_2630_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2658_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
uint64_t v_tid_2643_; lean_object* v_traces_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2657_; 
v_tid_2643_ = lean_ctor_get_uint64(v_traceState_2631_, sizeof(void*)*1);
v_traces_2644_ = lean_ctor_get(v_traceState_2631_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_traceState_2631_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2646_ = v_traceState_2631_;
v_isShared_2647_ = v_isSharedCheck_2657_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_traces_2644_);
lean_dec(v_traceState_2631_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2657_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2648_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2592_, v_traces_2644_);
lean_dec_ref(v_traces_2644_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2648_);
v___x_2650_ = v___x_2646_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2648_);
lean_ctor_set_uint64(v_reuseFailAlloc_2656_, sizeof(void*)*1, v_tid_2643_);
v___x_2650_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2652_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 4, v___x_2650_);
v___x_2652_ = v___x_2641_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_env_2632_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_nextMacroScope_2633_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_ngen_2634_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_auxDeclNGen_2635_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2655_, 5, v_cache_2636_);
lean_ctor_set(v_reuseFailAlloc_2655_, 6, v_messages_2637_);
lean_ctor_set(v_reuseFailAlloc_2655_, 7, v_infoState_2638_);
lean_ctor_set(v_reuseFailAlloc_2655_, 8, v_snapshotTasks_2639_);
v___x_2652_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_st_ref_put(v___y_2598_, v___x_2652_);
v___x_2654_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2600_);
return v___x_2654_;
}
}
}
}
}
else
{
goto v___jp_2623_;
}
}
else
{
goto v___jp_2623_;
}
}
v___jp_2659_:
{
double v___x_2661_; double v___x_2662_; double v___x_2663_; uint8_t v___x_2664_; 
v___x_2661_ = lean_unbox_float(v_snd_2609_);
v___x_2662_ = lean_unbox_float(v_fst_2608_);
v___x_2663_ = lean_float_sub(v___x_2661_, v___x_2662_);
v___x_2664_ = lean_float_decLt(v___y_2660_, v___x_2663_);
v___y_2629_ = v___x_2664_;
goto v___jp_2628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2675_, lean_object* v_collapsed_2676_, lean_object* v_tag_2677_, lean_object* v_opts_2678_, lean_object* v_clsEnabled_2679_, lean_object* v_oldTraces_2680_, lean_object* v_msg_2681_, lean_object* v_resStartStop_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v_collapsed_boxed_2688_; uint8_t v_clsEnabled_boxed_2689_; lean_object* v_res_2690_; 
v_collapsed_boxed_2688_ = lean_unbox(v_collapsed_2676_);
v_clsEnabled_boxed_2689_ = lean_unbox(v_clsEnabled_2679_);
v_res_2690_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2675_, v_collapsed_boxed_2688_, v_tag_2677_, v_opts_2678_, v_clsEnabled_boxed_2689_, v_oldTraces_2680_, v_msg_2681_, v_resStartStop_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec_ref(v_opts_2678_);
return v_res_2690_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2691_; double v___x_2692_; 
v___x_2691_ = lean_unsigned_to_nat(1000000000u);
v___x_2692_ = lean_float_of_nat(v___x_2691_);
return v___x_2692_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2695_ = l_Lean_stringToMessageData(v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_toConstantVal_2702_; lean_object* v_options_2703_; lean_object* v_name_2704_; lean_object* v_levelParams_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2916_; 
v_toConstantVal_2702_ = lean_ctor_get(v_ctorVal_2696_, 0);
lean_inc_ref(v_toConstantVal_2702_);
v_options_2703_ = lean_ctor_get(v_a_2699_, 2);
v_name_2704_ = lean_ctor_get(v_toConstantVal_2702_, 0);
v_levelParams_2705_ = lean_ctor_get(v_toConstantVal_2702_, 1);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_toConstantVal_2702_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v_toConstantVal_2702_, 2);
lean_dec(v_unused_2917_);
v___x_2707_ = v_toConstantVal_2702_;
v_isShared_2708_ = v_isSharedCheck_2916_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_levelParams_2705_);
lean_inc(v_name_2704_);
lean_dec(v_toConstantVal_2702_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2916_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v_inheritedTraceOptions_2709_; uint8_t v_hasTrace_2710_; lean_object* v_name_2711_; 
v_inheritedTraceOptions_2709_ = lean_ctor_get(v_a_2699_, 13);
v_hasTrace_2710_ = lean_ctor_get_uint8(v_options_2703_, sizeof(void*)*1);
lean_inc(v_name_2704_);
v_name_2711_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2704_);
if (v_hasTrace_2710_ == 0)
{
lean_object* v___x_2712_; 
v___x_2712_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2750_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2750_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2750_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
if (lean_obj_tag(v_a_2713_) == 1)
{
lean_object* v_val_2717_; lean_object* v___x_2718_; 
lean_del_object(v___x_2715_);
v_val_2717_ = lean_ctor_get(v_a_2713_, 0);
lean_inc_n(v_val_2717_, 2);
lean_dec_ref_known(v_a_2713_, 1);
v___x_2718_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2704_, v_val_2717_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2720_; lean_object* v_a_2721_; lean_object* v___x_2722_; lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2737_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2718_, 1);
v___x_2720_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2717_, v_a_2698_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref(v___x_2720_);
v___x_2722_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2719_, v_a_2698_);
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2737_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2737_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
lean_inc(v_name_2711_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 2, v_a_2721_);
lean_ctor_set(v___x_2707_, 0, v_name_2711_);
v___x_2728_ = v___x_2707_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_name_2711_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_levelParams_2705_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_a_2721_);
v___x_2728_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2730_, 0, v_name_2711_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2728_);
lean_ctor_set(v___x_2731_, 1, v_a_2723_);
lean_ctor_set(v___x_2731_, 2, v___x_2730_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 2);
lean_ctor_set(v___x_2725_, 0, v___x_2731_);
v___x_2733_ = v___x_2725_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_addDecl(v___x_2733_, v_hasTrace_2710_, v_a_2699_, v_a_2700_);
return v___x_2734_;
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_val_2717_);
lean_dec(v_name_2711_);
lean_del_object(v___x_2707_);
lean_dec(v_levelParams_2705_);
v_a_2738_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2718_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2718_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
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
else
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_dec(v_a_2713_);
lean_dec(v_name_2711_);
lean_del_object(v___x_2707_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v___x_2746_ = lean_box(0);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2746_);
v___x_2748_ = v___x_2715_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_name_2711_);
lean_del_object(v___x_2707_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v_a_2751_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2712_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2712_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
else
{
lean_object* v___f_2759_; lean_object* v_cls_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v_a_2767_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v_a_2779_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v_a_2784_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v_a_2795_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v_a_2810_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v_a_2815_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; 
lean_inc(v_name_2711_);
v___f_2759_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2759_, 0, v_name_2711_);
v_cls_2760_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2761_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2762_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2763_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2709_, v_options_2703_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2858_ = l_Lean_trace_profiler;
v___x_2859_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2703_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v___f_2759_);
v___x_2860_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2907_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2907_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2907_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
if (lean_obj_tag(v_a_2861_) == 1)
{
lean_object* v_val_2865_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; 
lean_del_object(v___x_2863_);
v_val_2865_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_val_2865_);
lean_dec_ref_known(v_a_2861_, 1);
if (v___x_2763_ == 0)
{
v___y_2867_ = v_a_2697_;
v___y_2868_ = v_a_2698_;
v___y_2869_ = v_a_2699_;
v___y_2870_ = v_a_2700_;
goto v___jp_2866_;
}
else
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2899_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2865_);
v___x_2900_ = l_Lean_MessageData_ofExpr(v_val_2865_);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2760_, v___x_2901_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_dec_ref_known(v___x_2902_, 1);
v___y_2867_ = v_a_2697_;
v___y_2868_ = v_a_2698_;
v___y_2869_ = v_a_2699_;
v___y_2870_ = v_a_2700_;
goto v___jp_2866_;
}
else
{
lean_dec(v_val_2865_);
lean_dec(v_name_2711_);
lean_del_object(v___x_2707_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
return v___x_2902_;
}
}
v___jp_2866_:
{
lean_object* v___x_2871_; 
lean_inc(v_val_2865_);
v___x_2871_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2704_, v_val_2865_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v_a_2874_; lean_object* v___x_2875_; lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2890_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2865_, v___y_2868_);
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref(v___x_2873_);
v___x_2875_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2872_, v___y_2868_);
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
lean_object* v___x_2881_; 
lean_inc(v_name_2711_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 2, v_a_2874_);
lean_ctor_set(v___x_2707_, 0, v_name_2711_);
v___x_2881_ = v___x_2707_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_name_2711_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_levelParams_2705_);
lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_a_2874_);
v___x_2881_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_name_2711_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2881_);
lean_ctor_set(v___x_2884_, 1, v_a_2876_);
lean_ctor_set(v___x_2884_, 2, v___x_2883_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 2);
lean_ctor_set(v___x_2878_, 0, v___x_2884_);
v___x_2886_ = v___x_2878_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_addDecl(v___x_2886_, v___x_2859_, v___y_2869_, v___y_2870_);
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_val_2865_);
lean_dec(v_name_2711_);
lean_del_object(v___x_2707_);
lean_dec(v_levelParams_2705_);
v_a_2891_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2871_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2871_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
else
{
lean_object* v___x_2903_; lean_object* v___x_2905_; 
lean_dec(v_a_2861_);
lean_dec(v_name_2711_);
lean_del_object(v___x_2707_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v___x_2903_ = lean_box(0);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2903_);
v___x_2905_ = v___x_2863_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_name_2711_);
lean_del_object(v___x_2707_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v_a_2908_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2860_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2860_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_del_object(v___x_2707_);
goto v___jp_2823_;
}
}
else
{
lean_del_object(v___x_2707_);
goto v___jp_2823_;
}
v___jp_2764_:
{
lean_object* v___x_2768_; double v___x_2769_; double v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2768_ = lean_io_get_num_heartbeats();
v___x_2769_ = lean_float_of_nat(v___y_2765_);
v___x_2770_ = lean_float_of_nat(v___x_2768_);
v___x_2771_ = lean_box_float(v___x_2769_);
v___x_2772_ = lean_box_float(v___x_2770_);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v_a_2767_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2760_, v_hasTrace_2710_, v___x_2761_, v_options_2703_, v___x_2763_, v___y_2766_, v___f_2759_, v___x_2774_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
return v___x_2775_;
}
v___jp_2776_:
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_a_2779_);
v___y_2765_ = v___y_2777_;
v___y_2766_ = v___y_2778_;
v_a_2767_ = v___x_2780_;
goto v___jp_2764_;
}
v___jp_2781_:
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2785_, 0, v_a_2784_);
v___y_2765_ = v___y_2782_;
v___y_2766_ = v___y_2783_;
v_a_2767_ = v___x_2785_;
goto v___jp_2764_;
}
v___jp_2786_:
{
if (lean_obj_tag(v___y_2789_) == 0)
{
lean_object* v_a_2790_; 
v_a_2790_ = lean_ctor_get(v___y_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___y_2789_, 1);
v___y_2782_ = v___y_2787_;
v___y_2783_ = v___y_2788_;
v_a_2784_ = v_a_2790_;
goto v___jp_2781_;
}
else
{
lean_object* v_a_2791_; 
v_a_2791_ = lean_ctor_get(v___y_2789_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___y_2789_, 1);
v___y_2777_ = v___y_2787_;
v___y_2778_ = v___y_2788_;
v_a_2779_ = v_a_2791_;
goto v___jp_2776_;
}
}
v___jp_2792_:
{
lean_object* v___x_2796_; double v___x_2797_; double v___x_2798_; double v___x_2799_; double v___x_2800_; double v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2796_ = lean_io_mono_nanos_now();
v___x_2797_ = lean_float_of_nat(v___y_2793_);
v___x_2798_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2799_ = lean_float_div(v___x_2797_, v___x_2798_);
v___x_2800_ = lean_float_of_nat(v___x_2796_);
v___x_2801_ = lean_float_div(v___x_2800_, v___x_2798_);
v___x_2802_ = lean_box_float(v___x_2799_);
v___x_2803_ = lean_box_float(v___x_2801_);
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v_a_2795_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2760_, v_hasTrace_2710_, v___x_2761_, v_options_2703_, v___x_2763_, v___y_2794_, v___f_2759_, v___x_2805_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
return v___x_2806_;
}
v___jp_2807_:
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2810_);
v___y_2793_ = v___y_2808_;
v___y_2794_ = v___y_2809_;
v_a_2795_ = v___x_2811_;
goto v___jp_2792_;
}
v___jp_2812_:
{
lean_object* v___x_2816_; 
v___x_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2816_, 0, v_a_2815_);
v___y_2793_ = v___y_2813_;
v___y_2794_ = v___y_2814_;
v_a_2795_ = v___x_2816_;
goto v___jp_2792_;
}
v___jp_2817_:
{
if (lean_obj_tag(v___y_2820_) == 0)
{
lean_object* v_a_2821_; 
v_a_2821_ = lean_ctor_get(v___y_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___y_2820_, 1);
v___y_2808_ = v___y_2818_;
v___y_2809_ = v___y_2819_;
v_a_2810_ = v_a_2821_;
goto v___jp_2807_;
}
else
{
lean_object* v_a_2822_; 
v_a_2822_ = lean_ctor_get(v___y_2820_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___y_2820_, 1);
v___y_2813_ = v___y_2818_;
v___y_2814_ = v___y_2819_;
v_a_2815_ = v_a_2822_;
goto v___jp_2812_;
}
}
v___jp_2823_:
{
lean_object* v___x_2824_; lean_object* v_a_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2824_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2700_);
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2827_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2703_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_io_mono_nanos_now();
v___x_2829_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
if (lean_obj_tag(v_a_2830_) == 1)
{
if (v___x_2763_ == 0)
{
lean_object* v_val_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v_val_2831_ = lean_ctor_get(v_a_2830_, 0);
lean_inc(v_val_2831_);
lean_dec_ref_known(v_a_2830_, 1);
v___x_2832_ = lean_box(0);
v___x_2833_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2704_, v_val_2831_, v_name_2711_, v_levelParams_2705_, v___x_2827_, v___x_2832_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
v___y_2818_ = v___x_2828_;
v___y_2819_ = v_a_2825_;
v___y_2820_ = v___x_2833_;
goto v___jp_2817_;
}
else
{
lean_object* v_val_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_val_2834_ = lean_ctor_get(v_a_2830_, 0);
lean_inc_n(v_val_2834_, 2);
lean_dec_ref_known(v_a_2830_, 1);
v___x_2835_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2836_ = l_Lean_MessageData_ofExpr(v_val_2834_);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2760_, v___x_2837_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2704_, v_val_2834_, v_name_2711_, v_levelParams_2705_, v___x_2827_, v_a_2839_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
v___y_2818_ = v___x_2828_;
v___y_2819_ = v_a_2825_;
v___y_2820_ = v___x_2840_;
goto v___jp_2817_;
}
else
{
lean_dec(v_val_2834_);
lean_dec(v_name_2711_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v___y_2818_ = v___x_2828_;
v___y_2819_ = v_a_2825_;
v___y_2820_ = v___x_2838_;
goto v___jp_2817_;
}
}
}
else
{
lean_object* v___x_2841_; 
lean_dec(v_a_2830_);
lean_dec(v_name_2711_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v___x_2841_ = lean_box(0);
v___y_2808_ = v___x_2828_;
v___y_2809_ = v_a_2825_;
v_a_2810_ = v___x_2841_;
goto v___jp_2807_;
}
}
else
{
lean_object* v_a_2842_; 
lean_dec(v_name_2711_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v_a_2842_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2829_, 1);
v___y_2813_ = v___x_2828_;
v___y_2814_ = v_a_2825_;
v_a_2815_ = v_a_2842_;
goto v___jp_2812_;
}
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_io_get_num_heartbeats();
v___x_2844_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
if (lean_obj_tag(v_a_2845_) == 1)
{
if (v___x_2763_ == 0)
{
lean_object* v_val_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_val_2846_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_val_2846_);
lean_dec_ref_known(v_a_2845_, 1);
v___x_2847_ = lean_box(0);
v___x_2848_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2704_, v_val_2846_, v_name_2711_, v_levelParams_2705_, v___x_2847_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
v___y_2787_ = v___x_2843_;
v___y_2788_ = v_a_2825_;
v___y_2789_ = v___x_2848_;
goto v___jp_2786_;
}
else
{
lean_object* v_val_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_val_2849_ = lean_ctor_get(v_a_2845_, 0);
lean_inc_n(v_val_2849_, 2);
lean_dec_ref_known(v_a_2845_, 1);
v___x_2850_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2851_ = l_Lean_MessageData_ofExpr(v_val_2849_);
v___x_2852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2760_, v___x_2852_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2855_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2855_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2704_, v_val_2849_, v_name_2711_, v_levelParams_2705_, v_a_2854_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
v___y_2787_ = v___x_2843_;
v___y_2788_ = v_a_2825_;
v___y_2789_ = v___x_2855_;
goto v___jp_2786_;
}
else
{
lean_dec(v_val_2849_);
lean_dec(v_name_2711_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v___y_2787_ = v___x_2843_;
v___y_2788_ = v_a_2825_;
v___y_2789_ = v___x_2853_;
goto v___jp_2786_;
}
}
}
else
{
lean_object* v___x_2856_; 
lean_dec(v_a_2845_);
lean_dec(v_name_2711_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v___x_2856_ = lean_box(0);
v___y_2782_ = v___x_2843_;
v___y_2783_ = v_a_2825_;
v_a_2784_ = v___x_2856_;
goto v___jp_2781_;
}
}
else
{
lean_object* v_a_2857_; 
lean_dec(v_name_2711_);
lean_dec(v_levelParams_2705_);
lean_dec(v_name_2704_);
v_a_2857_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2844_, 1);
v___y_2777_ = v___x_2843_;
v___y_2778_ = v_a_2825_;
v_a_2779_ = v_a_2857_;
goto v___jp_2776_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_00_u03b1_2925_, lean_object* v_x_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2926_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2933_, lean_object* v_x_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_00_u03b1_2933_, v_x_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2944_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2946_ = l_Lean_Name_append(v_ctorName_2944_, v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
uint8_t v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = 1;
v___x_2954_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2947_, v___x_2953_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2962_, lean_object* v_t_2963_, lean_object* v_acc_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2963_, v_a_2965_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2991_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2991_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2991_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2977_ = l_Lean_Expr_cleanupAnnotations(v_a_2968_);
v___x_2978_ = l_Lean_Expr_isApp(v___x_2977_);
if (v___x_2978_ == 0)
{
lean_dec_ref(v___x_2977_);
goto v___jp_2972_;
}
else
{
lean_object* v_arg_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_arg_2979_ = lean_ctor_get(v___x_2977_, 1);
lean_inc_ref(v_arg_2979_);
v___x_2980_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2977_);
v___x_2981_ = l_Lean_Expr_isApp(v___x_2980_);
if (v___x_2981_ == 0)
{
lean_dec_ref(v___x_2980_);
lean_dec_ref(v_arg_2979_);
goto v___jp_2972_;
}
else
{
lean_object* v_arg_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v_arg_2982_ = lean_ctor_get(v___x_2980_, 1);
lean_inc_ref(v_arg_2982_);
v___x_2983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2980_);
v___x_2984_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_2985_ = l_Lean_Expr_isConstOf(v___x_2983_, v___x_2984_);
lean_dec_ref(v___x_2983_);
if (v___x_2985_ == 0)
{
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_arg_2979_);
goto v___jp_2972_;
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_del_object(v___x_2970_);
v___x_2986_ = lean_unsigned_to_nat(0u);
v___x_2987_ = l_Lean_mkProj(v___x_2984_, v___x_2986_, v_e_2962_);
lean_inc_ref(v___x_2987_);
v___x_2988_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2987_, v_arg_2982_, v_acc_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v_e_2962_ = v___x_2987_;
v_t_2963_ = v_arg_2979_;
v_acc_2964_ = v_a_2989_;
goto _start;
}
else
{
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_arg_2979_);
return v___x_2988_;
}
}
}
}
v___jp_2972_:
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2973_ = lean_array_push(v_acc_2964_, v_e_2962_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2973_);
v___x_2975_ = v___x_2970_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref(v_acc_2964_);
lean_dec_ref(v_e_2962_);
v_a_2992_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2967_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2967_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_3000_, lean_object* v_t_3001_, lean_object* v_acc_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3000_, v_t_3001_, v_acc_3002_, v_a_3003_);
lean_dec(v_a_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_3006_, lean_object* v_t_3007_, lean_object* v_acc_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3006_, v_t_3007_, v_acc_3008_, v_a_3010_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3015_, lean_object* v_t_3016_, lean_object* v_acc_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3015_, v_t_3016_, v_acc_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v___x_3030_; 
lean_inc(v_a_3028_);
lean_inc_ref(v_a_3027_);
lean_inc(v_a_3026_);
lean_inc_ref(v_a_3025_);
lean_inc_ref(v_e_3024_);
v___x_3030_ = lean_infer_type(v_e_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3032_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3033_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3024_, v_a_3031_, v___x_3032_, v_a_3026_);
return v___x_3033_;
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v_e_3024_);
v_a_3034_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3030_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3030_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3049_, lean_object* v_x_3050_, lean_object* v_x_3051_, lean_object* v_x_3052_){
_start:
{
lean_object* v_ks_3053_; lean_object* v_vs_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3078_; 
v_ks_3053_ = lean_ctor_get(v_x_3049_, 0);
v_vs_3054_ = lean_ctor_get(v_x_3049_, 1);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_x_3049_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3056_ = v_x_3049_;
v_isShared_3057_ = v_isSharedCheck_3078_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_vs_3054_);
lean_inc(v_ks_3053_);
lean_dec(v_x_3049_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3078_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3058_ = lean_array_get_size(v_ks_3053_);
v___x_3059_ = lean_nat_dec_lt(v_x_3050_, v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_dec(v_x_3050_);
v___x_3060_ = lean_array_push(v_ks_3053_, v_x_3051_);
v___x_3061_ = lean_array_push(v_vs_3054_, v_x_3052_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 1, v___x_3061_);
lean_ctor_set(v___x_3056_, 0, v___x_3060_);
v___x_3063_ = v___x_3056_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
else
{
lean_object* v_k_x27_3065_; uint8_t v___x_3066_; 
v_k_x27_3065_ = lean_array_fget_borrowed(v_ks_3053_, v_x_3050_);
v___x_3066_ = l_Lean_instBEqMVarId_beq(v_x_3051_, v_k_x27_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3068_; 
if (v_isShared_3057_ == 0)
{
v___x_3068_ = v___x_3056_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_ks_3053_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_vs_3054_);
v___x_3068_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_unsigned_to_nat(1u);
v___x_3070_ = lean_nat_add(v_x_3050_, v___x_3069_);
lean_dec(v_x_3050_);
v_x_3049_ = v___x_3068_;
v_x_3050_ = v___x_3070_;
goto _start;
}
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3076_; 
v___x_3073_ = lean_array_fset(v_ks_3053_, v_x_3050_, v_x_3051_);
v___x_3074_ = lean_array_fset(v_vs_3054_, v_x_3050_, v_x_3052_);
lean_dec(v_x_3050_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 1, v___x_3074_);
lean_ctor_set(v___x_3056_, 0, v___x_3073_);
v___x_3076_ = v___x_3056_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3074_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3079_, lean_object* v_k_3080_, lean_object* v_v_3081_){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3079_, v___x_3082_, v_k_3080_, v_v_3081_);
return v___x_3083_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3085_, size_t v_x_3086_, size_t v_x_3087_, lean_object* v_x_3088_, lean_object* v_x_3089_){
_start:
{
if (lean_obj_tag(v_x_3085_) == 0)
{
lean_object* v_es_3090_; size_t v___x_3091_; size_t v___x_3092_; lean_object* v_j_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v_es_3090_ = lean_ctor_get(v_x_3085_, 0);
v___x_3091_ = ((size_t)31ULL);
v___x_3092_ = lean_usize_land(v_x_3086_, v___x_3091_);
v_j_3093_ = lean_usize_to_nat(v___x_3092_);
v___x_3094_ = lean_array_get_size(v_es_3090_);
v___x_3095_ = lean_nat_dec_lt(v_j_3093_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_dec(v_j_3093_);
lean_dec(v_x_3089_);
lean_dec(v_x_3088_);
return v_x_3085_;
}
else
{
lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3134_; 
lean_inc_ref(v_es_3090_);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_x_3085_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v_x_3085_, 0);
lean_dec(v_unused_3135_);
v___x_3097_ = v_x_3085_;
v_isShared_3098_ = v_isSharedCheck_3134_;
goto v_resetjp_3096_;
}
else
{
lean_dec(v_x_3085_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3134_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_v_3099_; lean_object* v___x_3100_; lean_object* v_xs_x27_3101_; lean_object* v___y_3103_; 
v_v_3099_ = lean_array_fget(v_es_3090_, v_j_3093_);
v___x_3100_ = lean_box(0);
v_xs_x27_3101_ = lean_array_fset(v_es_3090_, v_j_3093_, v___x_3100_);
switch(lean_obj_tag(v_v_3099_))
{
case 0:
{
lean_object* v_key_3108_; lean_object* v_val_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3119_; 
v_key_3108_ = lean_ctor_get(v_v_3099_, 0);
v_val_3109_ = lean_ctor_get(v_v_3099_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_v_3099_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3111_ = v_v_3099_;
v_isShared_3112_ = v_isSharedCheck_3119_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_val_3109_);
lean_inc(v_key_3108_);
lean_dec(v_v_3099_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3119_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
uint8_t v___x_3113_; 
v___x_3113_ = l_Lean_instBEqMVarId_beq(v_x_3088_, v_key_3108_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_del_object(v___x_3111_);
v___x_3114_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3108_, v_val_3109_, v_x_3088_, v_x_3089_);
v___x_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
v___y_3103_ = v___x_3115_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3117_; 
lean_dec(v_val_3109_);
lean_dec(v_key_3108_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v_x_3089_);
lean_ctor_set(v___x_3111_, 0, v_x_3088_);
v___x_3117_ = v___x_3111_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_x_3088_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_x_3089_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
v___y_3103_ = v___x_3117_;
goto v___jp_3102_;
}
}
}
}
case 1:
{
lean_object* v_node_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3132_; 
v_node_3120_ = lean_ctor_get(v_v_3099_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_v_3099_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3122_ = v_v_3099_;
v_isShared_3123_ = v_isSharedCheck_3132_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_node_3120_);
lean_dec(v_v_3099_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3132_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
size_t v___x_3124_; size_t v___x_3125_; size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3124_ = ((size_t)5ULL);
v___x_3125_ = lean_usize_shift_right(v_x_3086_, v___x_3124_);
v___x_3126_ = ((size_t)1ULL);
v___x_3127_ = lean_usize_add(v_x_3087_, v___x_3126_);
v___x_3128_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3120_, v___x_3125_, v___x_3127_, v_x_3088_, v_x_3089_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3128_);
v___x_3130_ = v___x_3122_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
v___y_3103_ = v___x_3130_;
goto v___jp_3102_;
}
}
}
default: 
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3133_, 0, v_x_3088_);
lean_ctor_set(v___x_3133_, 1, v_x_3089_);
v___y_3103_ = v___x_3133_;
goto v___jp_3102_;
}
}
v___jp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3104_ = lean_array_fset(v_xs_x27_3101_, v_j_3093_, v___y_3103_);
lean_dec(v_j_3093_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v___x_3104_);
v___x_3106_ = v___x_3097_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
else
{
lean_object* v_ks_3136_; lean_object* v_vs_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3155_; 
v_ks_3136_ = lean_ctor_get(v_x_3085_, 0);
v_vs_3137_ = lean_ctor_get(v_x_3085_, 1);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_x_3085_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3139_ = v_x_3085_;
v_isShared_3140_ = v_isSharedCheck_3155_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_vs_3137_);
lean_inc(v_ks_3136_);
lean_dec(v_x_3085_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3155_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_ks_3136_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_vs_3137_);
v___x_3142_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v_newNode_3143_; size_t v___x_3144_; uint8_t v___x_3145_; 
v_newNode_3143_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3142_, v_x_3088_, v_x_3089_);
v___x_3144_ = ((size_t)7ULL);
v___x_3145_ = lean_usize_dec_le(v___x_3144_, v_x_3087_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___x_3146_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3143_);
v___x_3147_ = lean_unsigned_to_nat(4u);
v___x_3148_ = lean_nat_dec_lt(v___x_3146_, v___x_3147_);
lean_dec(v___x_3146_);
if (v___x_3148_ == 0)
{
lean_object* v_ks_3149_; lean_object* v_vs_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_ks_3149_ = lean_ctor_get(v_newNode_3143_, 0);
lean_inc_ref(v_ks_3149_);
v_vs_3150_ = lean_ctor_get(v_newNode_3143_, 1);
lean_inc_ref(v_vs_3150_);
lean_dec_ref(v_newNode_3143_);
v___x_3151_ = lean_unsigned_to_nat(0u);
v___x_3152_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3087_, v_ks_3149_, v_vs_3150_, v___x_3151_, v___x_3152_);
lean_dec_ref(v_vs_3150_);
lean_dec_ref(v_ks_3149_);
return v___x_3153_;
}
else
{
return v_newNode_3143_;
}
}
else
{
return v_newNode_3143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3156_, lean_object* v_keys_3157_, lean_object* v_vals_3158_, lean_object* v_i_3159_, lean_object* v_entries_3160_){
_start:
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = lean_array_get_size(v_keys_3157_);
v___x_3162_ = lean_nat_dec_lt(v_i_3159_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_dec(v_i_3159_);
return v_entries_3160_;
}
else
{
lean_object* v_k_3163_; lean_object* v_v_3164_; uint64_t v___x_3165_; size_t v_h_3166_; size_t v___x_3167_; lean_object* v___x_3168_; size_t v___x_3169_; size_t v___x_3170_; size_t v___x_3171_; size_t v_h_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_k_3163_ = lean_array_fget_borrowed(v_keys_3157_, v_i_3159_);
v_v_3164_ = lean_array_fget_borrowed(v_vals_3158_, v_i_3159_);
v___x_3165_ = l_Lean_instHashableMVarId_hash(v_k_3163_);
v_h_3166_ = lean_uint64_to_usize(v___x_3165_);
v___x_3167_ = ((size_t)5ULL);
v___x_3168_ = lean_unsigned_to_nat(1u);
v___x_3169_ = ((size_t)1ULL);
v___x_3170_ = lean_usize_sub(v_depth_3156_, v___x_3169_);
v___x_3171_ = lean_usize_mul(v___x_3167_, v___x_3170_);
v_h_3172_ = lean_usize_shift_right(v_h_3166_, v___x_3171_);
v___x_3173_ = lean_nat_add(v_i_3159_, v___x_3168_);
lean_dec(v_i_3159_);
lean_inc(v_v_3164_);
lean_inc(v_k_3163_);
v___x_3174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3160_, v_h_3172_, v_depth_3156_, v_k_3163_, v_v_3164_);
v_i_3159_ = v___x_3173_;
v_entries_3160_ = v___x_3174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3176_, lean_object* v_keys_3177_, lean_object* v_vals_3178_, lean_object* v_i_3179_, lean_object* v_entries_3180_){
_start:
{
size_t v_depth_boxed_3181_; lean_object* v_res_3182_; 
v_depth_boxed_3181_ = lean_unbox_usize(v_depth_3176_);
lean_dec(v_depth_3176_);
v_res_3182_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3181_, v_keys_3177_, v_vals_3178_, v_i_3179_, v_entries_3180_);
lean_dec_ref(v_vals_3178_);
lean_dec_ref(v_keys_3177_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3183_, lean_object* v_x_3184_, lean_object* v_x_3185_, lean_object* v_x_3186_, lean_object* v_x_3187_){
_start:
{
size_t v_x_4985__boxed_3188_; size_t v_x_4986__boxed_3189_; lean_object* v_res_3190_; 
v_x_4985__boxed_3188_ = lean_unbox_usize(v_x_3184_);
lean_dec(v_x_3184_);
v_x_4986__boxed_3189_ = lean_unbox_usize(v_x_3185_);
lean_dec(v_x_3185_);
v_res_3190_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3183_, v_x_4985__boxed_3188_, v_x_4986__boxed_3189_, v_x_3186_, v_x_3187_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3191_, lean_object* v_x_3192_, lean_object* v_x_3193_){
_start:
{
uint64_t v___x_3194_; size_t v___x_3195_; size_t v___x_3196_; lean_object* v___x_3197_; 
v___x_3194_ = l_Lean_instHashableMVarId_hash(v_x_3192_);
v___x_3195_ = lean_uint64_to_usize(v___x_3194_);
v___x_3196_ = ((size_t)1ULL);
v___x_3197_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3191_, v___x_3195_, v___x_3196_, v_x_3192_, v_x_3193_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3198_, lean_object* v_val_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v___x_3202_; lean_object* v_mctx_3203_; lean_object* v_cache_3204_; lean_object* v_zetaDeltaFVarIds_3205_; lean_object* v_postponed_3206_; lean_object* v_diag_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3236_; 
v___x_3202_ = lean_st_ref_take(v___y_3200_);
v_mctx_3203_ = lean_ctor_get(v___x_3202_, 0);
v_cache_3204_ = lean_ctor_get(v___x_3202_, 1);
v_zetaDeltaFVarIds_3205_ = lean_ctor_get(v___x_3202_, 2);
v_postponed_3206_ = lean_ctor_get(v___x_3202_, 3);
v_diag_3207_ = lean_ctor_get(v___x_3202_, 4);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3209_ = v___x_3202_;
v_isShared_3210_ = v_isSharedCheck_3236_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_diag_3207_);
lean_inc(v_postponed_3206_);
lean_inc(v_zetaDeltaFVarIds_3205_);
lean_inc(v_cache_3204_);
lean_inc(v_mctx_3203_);
lean_dec(v___x_3202_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3236_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v_depth_3211_; lean_object* v_levelAssignDepth_3212_; lean_object* v_lmvarCounter_3213_; lean_object* v_mvarCounter_3214_; lean_object* v_lDecls_3215_; lean_object* v_decls_3216_; lean_object* v_userNames_3217_; lean_object* v_lAssignment_3218_; lean_object* v_eAssignment_3219_; lean_object* v_dAssignment_3220_; lean_object* v_instanceTypedMVars_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3235_; 
v_depth_3211_ = lean_ctor_get(v_mctx_3203_, 0);
v_levelAssignDepth_3212_ = lean_ctor_get(v_mctx_3203_, 1);
v_lmvarCounter_3213_ = lean_ctor_get(v_mctx_3203_, 2);
v_mvarCounter_3214_ = lean_ctor_get(v_mctx_3203_, 3);
v_lDecls_3215_ = lean_ctor_get(v_mctx_3203_, 4);
v_decls_3216_ = lean_ctor_get(v_mctx_3203_, 5);
v_userNames_3217_ = lean_ctor_get(v_mctx_3203_, 6);
v_lAssignment_3218_ = lean_ctor_get(v_mctx_3203_, 7);
v_eAssignment_3219_ = lean_ctor_get(v_mctx_3203_, 8);
v_dAssignment_3220_ = lean_ctor_get(v_mctx_3203_, 9);
v_instanceTypedMVars_3221_ = lean_ctor_get(v_mctx_3203_, 10);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_mctx_3203_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3223_ = v_mctx_3203_;
v_isShared_3224_ = v_isSharedCheck_3235_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_instanceTypedMVars_3221_);
lean_inc(v_dAssignment_3220_);
lean_inc(v_eAssignment_3219_);
lean_inc(v_lAssignment_3218_);
lean_inc(v_userNames_3217_);
lean_inc(v_decls_3216_);
lean_inc(v_lDecls_3215_);
lean_inc(v_mvarCounter_3214_);
lean_inc(v_lmvarCounter_3213_);
lean_inc(v_levelAssignDepth_3212_);
lean_inc(v_depth_3211_);
lean_dec(v_mctx_3203_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3235_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3225_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3219_, v_mvarId_3198_, v_val_3199_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 8, v___x_3225_);
v___x_3227_ = v___x_3223_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_depth_3211_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_levelAssignDepth_3212_);
lean_ctor_set(v_reuseFailAlloc_3234_, 2, v_lmvarCounter_3213_);
lean_ctor_set(v_reuseFailAlloc_3234_, 3, v_mvarCounter_3214_);
lean_ctor_set(v_reuseFailAlloc_3234_, 4, v_lDecls_3215_);
lean_ctor_set(v_reuseFailAlloc_3234_, 5, v_decls_3216_);
lean_ctor_set(v_reuseFailAlloc_3234_, 6, v_userNames_3217_);
lean_ctor_set(v_reuseFailAlloc_3234_, 7, v_lAssignment_3218_);
lean_ctor_set(v_reuseFailAlloc_3234_, 8, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3234_, 9, v_dAssignment_3220_);
lean_ctor_set(v_reuseFailAlloc_3234_, 10, v_instanceTypedMVars_3221_);
v___x_3227_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3229_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3227_);
v___x_3229_ = v___x_3209_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_cache_3204_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_zetaDeltaFVarIds_3205_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_postponed_3206_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v_diag_3207_);
v___x_3229_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_st_ref_put(v___y_3200_, v___x_3229_);
v___x_3231_ = lean_box(0);
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
return v___x_3232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3237_, lean_object* v_val_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3237_, v_val_3238_, v___y_3239_);
lean_dec(v___y_3239_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3242_, lean_object* v_a_3243_, lean_object* v_x_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_box(0);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc_ref(v___y_3245_);
v___x_3251_ = lean_apply_7(v___f_3242_, v___x_3250_, v_a_3243_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, lean_box(0));
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3252_, lean_object* v_a_3253_, lean_object* v_x_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3252_, v_a_3253_, v_x_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
return v_res_3260_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0));
v___x_3263_ = l_Lean_stringToMessageData(v___x_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3264_, lean_object* v_a_3265_, lean_object* v_x_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1);
v___x_3273_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3272_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3275_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
lean_inc(v___y_3270_);
lean_inc_ref(v___y_3269_);
lean_inc(v___y_3268_);
lean_inc_ref(v___y_3267_);
v___x_3275_ = lean_apply_7(v___f_3264_, v_a_3274_, v_a_3265_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, lean_box(0));
return v___x_3275_;
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec(v_a_3265_);
lean_dec_ref(v___f_3264_);
v_a_3276_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3273_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3273_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3284_, lean_object* v_a_3285_, lean_object* v_x_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3284_, v_a_3285_, v_x_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v_x_3286_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3293_, lean_object* v_____r_3294_, lean_object* v_mvarId_u2082_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3295_, v___x_3293_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3311_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3311_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3311_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_snd_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
v_snd_3306_ = lean_ctor_get(v_a_3302_, 1);
lean_inc(v_snd_3306_);
lean_dec(v_a_3302_);
v___x_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3307_, 0, v_snd_3306_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3307_);
v___x_3309_ = v___x_3304_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
v_a_3312_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3301_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3301_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3320_, lean_object* v_____r_3321_, lean_object* v_mvarId_u2082_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
uint8_t v___x_5273__boxed_3328_; lean_object* v_res_3329_; 
v___x_5273__boxed_3328_ = lean_unbox(v___x_3320_);
v_res_3329_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5273__boxed_3328_, v_____r_3321_, v_mvarId_u2082_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
return v_res_3329_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = lean_box(0);
v___x_3336_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2));
v___x_3337_ = l_Lean_mkConst(v___x_3336_, v___x_3335_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___y_3345_; lean_object* v___x_3365_; 
lean_inc(v_a_3338_);
v___x_3365_ = l_Lean_MVarId_getType(v_a_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3425_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3368_ = v___x_3365_;
v_isShared_3369_ = v_isSharedCheck_3425_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3365_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3425_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
if (lean_obj_tag(v_a_3366_) == 7)
{
lean_object* v_binderType_3370_; lean_object* v_body_3371_; uint8_t v___x_3372_; 
v_binderType_3370_ = lean_ctor_get(v_a_3366_, 1);
lean_inc_ref(v_binderType_3370_);
v_body_3371_ = lean_ctor_get(v_a_3366_, 2);
lean_inc_ref(v_body_3371_);
lean_dec_ref_known(v_a_3366_, 3);
v___x_3372_ = l_Lean_Expr_hasLooseBVars(v_body_3371_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; 
lean_del_object(v___x_3368_);
v___x_3373_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3370_, v___y_3340_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; lean_object* v___f_3376_; lean_object* v___x_3377_; uint8_t v___x_3378_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3373_, 1);
v___x_3375_ = lean_box(v___x_3372_);
v___f_3376_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3376_, 0, v___x_3375_);
v___x_3377_ = l_Lean_Expr_cleanupAnnotations(v_a_3374_);
v___x_3378_ = l_Lean_Expr_isApp(v___x_3377_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_dec_ref(v___x_3377_);
lean_dec_ref(v_body_3371_);
v___x_3379_ = lean_box(0);
v___x_3380_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3376_, v_a_3338_, v___x_3379_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
v___y_3345_ = v___x_3380_;
goto v___jp_3344_;
}
else
{
lean_object* v_arg_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v_arg_3381_ = lean_ctor_get(v___x_3377_, 1);
lean_inc_ref(v_arg_3381_);
v___x_3382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3377_);
v___x_3383_ = l_Lean_Expr_isApp(v___x_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_dec_ref(v___x_3382_);
lean_dec_ref(v_arg_3381_);
lean_dec_ref(v_body_3371_);
v___x_3384_ = lean_box(0);
v___x_3385_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3376_, v_a_3338_, v___x_3384_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
v___y_3345_ = v___x_3385_;
goto v___jp_3344_;
}
else
{
lean_object* v_arg_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v_arg_3386_ = lean_ctor_get(v___x_3382_, 1);
lean_inc_ref(v_arg_3386_);
v___x_3387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3382_);
v___x_3388_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3389_ = l_Lean_Expr_isConstOf(v___x_3387_, v___x_3388_);
lean_dec_ref(v___x_3387_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
lean_dec_ref(v_arg_3386_);
lean_dec_ref(v_arg_3381_);
lean_dec_ref(v_body_3371_);
v___x_3390_ = lean_box(0);
v___x_3391_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3376_, v_a_3338_, v___x_3390_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
v___y_3345_ = v___x_3391_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3392_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3);
v___x_3393_ = l_Lean_mkApp3(v___x_3392_, v_arg_3386_, v_arg_3381_, v_body_3371_);
v___x_3394_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3338_);
v___x_3395_ = l_Lean_MVarId_applyN(v_a_3338_, v___x_3393_, v___x_3394_, v___x_3389_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref_known(v___x_3395_, 1);
if (lean_obj_tag(v_a_3396_) == 1)
{
lean_object* v_tail_3397_; 
v_tail_3397_ = lean_ctor_get(v_a_3396_, 1);
if (lean_obj_tag(v_tail_3397_) == 0)
{
lean_object* v_head_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec_ref(v___f_3376_);
lean_dec(v_a_3338_);
v_head_3398_ = lean_ctor_get(v_a_3396_, 0);
lean_inc(v_head_3398_);
lean_dec_ref_known(v_a_3396_, 2);
v___x_3399_ = lean_box(0);
v___x_3400_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3372_, v___x_3399_, v_head_3398_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
v___y_3345_ = v___x_3400_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3401_; 
v___x_3401_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3376_, v_a_3338_, v_a_3396_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec_ref_known(v_a_3396_, 2);
v___y_3345_ = v___x_3401_;
goto v___jp_3344_;
}
}
else
{
lean_object* v___x_3402_; 
v___x_3402_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3376_, v_a_3338_, v_a_3396_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v_a_3396_);
v___y_3345_ = v___x_3402_;
goto v___jp_3344_;
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec_ref(v___f_3376_);
lean_dec(v_a_3338_);
v_a_3403_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3395_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3395_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v_body_3371_);
lean_dec(v_a_3338_);
v_a_3411_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3373_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3373_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
else
{
lean_object* v___x_3420_; 
lean_dec_ref(v_body_3371_);
lean_dec_ref(v_binderType_3370_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v_a_3338_);
v___x_3420_ = v___x_3368_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3338_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
else
{
lean_object* v___x_3423_; 
lean_dec(v_a_3366_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v_a_3338_);
v___x_3423_ = v___x_3368_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3338_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec(v_a_3338_);
v_a_3426_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3365_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3365_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
v___jp_3344_:
{
if (lean_obj_tag(v___y_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3356_; 
v_a_3346_ = lean_ctor_get(v___y_3345_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___y_3345_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3348_ = v___y_3345_;
v_isShared_3349_ = v_isSharedCheck_3356_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___y_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3356_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
if (lean_obj_tag(v_a_3346_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; 
v_a_3350_ = lean_ctor_get(v_a_3346_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v_a_3346_, 1);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_a_3350_);
v___x_3352_ = v___x_3348_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
else
{
lean_object* v_a_3354_; 
lean_del_object(v___x_3348_);
v_a_3354_ = lean_ctor_get(v_a_3346_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v_a_3346_, 1);
v_a_3338_ = v_a_3354_;
goto _start;
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
v_a_3357_ = lean_ctor_get(v___y_3345_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___y_3345_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___y_3345_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___y_3345_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
return v_res_3440_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_box(0);
v___x_3447_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3448_ = l_Lean_mkConst(v___x_3447_, v___x_3446_);
return v___x_3448_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3455_ = l_Lean_stringToMessageData(v___x_3454_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3456_, lean_object* v_xs_3457_, lean_object* v_type_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = lean_box(0);
v___x_3465_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3458_, v___x_3464_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; uint8_t v___x_3471_; lean_object* v___y_3473_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = l_Lean_Expr_mvarId_x21(v_a_3466_);
v___x_3468_ = lean_box(0);
v___x_3469_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3470_ = 1;
v___x_3471_ = 0;
v___x_3484_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3485_ = lean_box(0);
v___x_3486_ = l_Lean_MVarId_apply(v___x_3467_, v___x_3469_, v___x_3484_, v___x_3485_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
if (lean_obj_tag(v_a_3487_) == 1)
{
lean_object* v_tail_3501_; 
v_tail_3501_ = lean_ctor_get(v_a_3487_, 1);
lean_inc(v_tail_3501_);
if (lean_obj_tag(v_tail_3501_) == 1)
{
lean_object* v_tail_3502_; 
v_tail_3502_ = lean_ctor_get(v_tail_3501_, 1);
if (lean_obj_tag(v_tail_3502_) == 0)
{
lean_object* v_toConstantVal_3503_; lean_object* v_head_3504_; lean_object* v_head_3505_; lean_object* v_name_3506_; lean_object* v_levelParams_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_toConstantVal_3503_ = lean_ctor_get(v_ctorVal_3456_, 0);
lean_inc_ref(v_toConstantVal_3503_);
lean_dec_ref(v_ctorVal_3456_);
v_head_3504_ = lean_ctor_get(v_a_3487_, 0);
lean_inc(v_head_3504_);
lean_dec_ref_known(v_a_3487_, 2);
v_head_3505_ = lean_ctor_get(v_tail_3501_, 0);
lean_inc(v_head_3505_);
lean_dec_ref_known(v_tail_3501_, 2);
v_name_3506_ = lean_ctor_get(v_toConstantVal_3503_, 0);
lean_inc_n(v_name_3506_, 2);
v_levelParams_3507_ = lean_ctor_get(v_toConstantVal_3503_, 1);
lean_inc(v_levelParams_3507_);
lean_dec_ref(v_toConstantVal_3503_);
v___x_3508_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3506_);
v___x_3509_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3507_, v___x_3468_);
v___x_3510_ = l_Lean_mkConst(v___x_3508_, v___x_3509_);
v___x_3511_ = l_Lean_mkAppN(v___x_3510_, v_xs_3457_);
v___x_3512_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3504_, v___x_3511_, v___y_3460_);
lean_dec_ref(v___x_3512_);
v___x_3513_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3505_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = l_Lean_MVarId_refl(v_a_3514_, v___x_3470_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_dec(v_name_3506_);
v___y_3473_ = v___x_3515_;
goto v___jp_3472_;
}
else
{
lean_object* v_a_3516_; uint8_t v___y_3518_; uint8_t v___x_3521_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
v___x_3521_ = l_Lean_Exception_isInterrupt(v_a_3516_);
if (v___x_3521_ == 0)
{
uint8_t v___x_3522_; 
v___x_3522_ = l_Lean_Exception_isRuntime(v_a_3516_);
v___y_3518_ = v___x_3522_;
goto v___jp_3517_;
}
else
{
lean_dec(v_a_3516_);
v___y_3518_ = v___x_3521_;
goto v___jp_3517_;
}
v___jp_3517_:
{
if (v___y_3518_ == 0)
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_dec_ref_known(v___x_3515_, 1);
v___x_3519_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3506_);
v___x_3520_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3519_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
v___y_3473_ = v___x_3520_;
goto v___jp_3472_;
}
else
{
lean_dec(v_name_3506_);
v___y_3473_ = v___x_3515_;
goto v___jp_3472_;
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec(v_name_3506_);
lean_dec(v_a_3466_);
v_a_3523_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3513_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3513_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3501_, 2);
lean_dec_ref_known(v_a_3487_, 2);
lean_dec(v_a_3466_);
v___y_3489_ = v___y_3459_;
v___y_3490_ = v___y_3460_;
v___y_3491_ = v___y_3461_;
v___y_3492_ = v___y_3462_;
goto v___jp_3488_;
}
}
else
{
lean_dec(v_tail_3501_);
lean_dec_ref_known(v_a_3487_, 2);
lean_dec(v_a_3466_);
v___y_3489_ = v___y_3459_;
v___y_3490_ = v___y_3460_;
v___y_3491_ = v___y_3461_;
v___y_3492_ = v___y_3462_;
goto v___jp_3488_;
}
}
else
{
lean_dec(v_a_3487_);
lean_dec(v_a_3466_);
v___y_3489_ = v___y_3459_;
v___y_3490_ = v___y_3460_;
v___y_3491_ = v___y_3461_;
v___y_3492_ = v___y_3462_;
goto v___jp_3488_;
}
v___jp_3488_:
{
lean_object* v_toConstantVal_3493_; lean_object* v_name_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_toConstantVal_3493_ = lean_ctor_get(v_ctorVal_3456_, 0);
lean_inc_ref(v_toConstantVal_3493_);
lean_dec_ref(v_ctorVal_3456_);
v_name_3494_ = lean_ctor_get(v_toConstantVal_3493_, 0);
lean_inc(v_name_3494_);
lean_dec_ref(v_toConstantVal_3493_);
v___x_3495_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3496_ = l_Lean_MessageData_ofName(v_name_3494_);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3497_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3499_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
return v___x_3500_;
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec(v_a_3466_);
lean_dec_ref(v_ctorVal_3456_);
v_a_3531_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3486_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3486_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
v___jp_3472_:
{
if (lean_obj_tag(v___y_3473_) == 0)
{
uint8_t v___x_3474_; lean_object* v___x_3475_; 
lean_dec_ref_known(v___y_3473_, 1);
v___x_3474_ = 1;
v___x_3475_ = l_Lean_Meta_mkLambdaFVars(v_xs_3457_, v_a_3466_, v___x_3471_, v___x_3470_, v___x_3471_, v___x_3470_, v___x_3474_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
return v___x_3475_;
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec(v_a_3466_);
v_a_3476_ = lean_ctor_get(v___y_3473_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___y_3473_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___y_3473_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___y_3473_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorVal_3456_);
return v___x_3465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3539_, lean_object* v_xs_3540_, lean_object* v_type_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3539_, v_xs_3540_, v_type_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec_ref(v_xs_3540_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3548_, lean_object* v_targetType_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v___f_3555_; uint8_t v___x_3556_; lean_object* v___x_3557_; 
v___f_3555_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3555_, 0, v_ctorVal_3548_);
v___x_3556_ = 0;
v___x_3557_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3549_, v___f_3555_, v___x_3556_, v___x_3556_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3558_, lean_object* v_targetType_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3558_, v_targetType_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3566_, lean_object* v_val_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3566_, v_val_3567_, v___y_3569_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3574_, lean_object* v_val_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3574_, v_val_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3582_, lean_object* v_a_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3590_, lean_object* v_a_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3590_, v_a_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3598_, lean_object* v_x_3599_, lean_object* v_x_3600_, lean_object* v_x_3601_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3599_, v_x_3600_, v_x_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3603_, lean_object* v_x_3604_, size_t v_x_3605_, size_t v_x_3606_, lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3604_, v_x_3605_, v_x_3606_, v_x_3607_, v_x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3610_, lean_object* v_x_3611_, lean_object* v_x_3612_, lean_object* v_x_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
size_t v_x_5824__boxed_3616_; size_t v_x_5825__boxed_3617_; lean_object* v_res_3618_; 
v_x_5824__boxed_3616_ = lean_unbox_usize(v_x_3612_);
lean_dec(v_x_3612_);
v_x_5825__boxed_3617_ = lean_unbox_usize(v_x_3613_);
lean_dec(v_x_3613_);
v_res_3618_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3610_, v_x_3611_, v_x_5824__boxed_3616_, v_x_5825__boxed_3617_, v_x_3614_, v_x_3615_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3619_, lean_object* v_n_3620_, lean_object* v_k_3621_, lean_object* v_v_3622_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3620_, v_k_3621_, v_v_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3624_, size_t v_depth_3625_, lean_object* v_keys_3626_, lean_object* v_vals_3627_, lean_object* v_heq_3628_, lean_object* v_i_3629_, lean_object* v_entries_3630_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3625_, v_keys_3626_, v_vals_3627_, v_i_3629_, v_entries_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3632_, lean_object* v_depth_3633_, lean_object* v_keys_3634_, lean_object* v_vals_3635_, lean_object* v_heq_3636_, lean_object* v_i_3637_, lean_object* v_entries_3638_){
_start:
{
size_t v_depth_boxed_3639_; lean_object* v_res_3640_; 
v_depth_boxed_3639_ = lean_unbox_usize(v_depth_3633_);
lean_dec(v_depth_3633_);
v_res_3640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3632_, v_depth_boxed_3639_, v_keys_3634_, v_vals_3635_, v_heq_3636_, v_i_3637_, v_entries_3638_);
lean_dec_ref(v_vals_3635_);
lean_dec_ref(v_keys_3634_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3641_, lean_object* v_x_3642_, lean_object* v_x_3643_, lean_object* v_x_3644_, lean_object* v_x_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3642_, v_x_3643_, v_x_3644_, v_x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3647_, lean_object* v_val_3648_, lean_object* v_name_3649_, lean_object* v_levelParams_3650_, uint8_t v___x_3651_, uint8_t v_hasTrace_3652_, lean_object* v_____r_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v___x_3659_; 
lean_inc_ref(v_val_3648_);
v___x_3659_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3647_, v_val_3648_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v_a_3662_; lean_object* v___x_3663_; lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3680_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3659_, 1);
v___x_3661_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3648_, v___y_3655_);
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
v___x_3663_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3660_, v___y_3655_);
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3666_ = v___x_3663_;
v_isShared_3667_ = v_isSharedCheck_3680_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3680_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
lean_inc_n(v_name_3649_, 2);
v___x_3668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3668_, 0, v_name_3649_);
lean_ctor_set(v___x_3668_, 1, v_levelParams_3650_);
lean_ctor_set(v___x_3668_, 2, v_a_3662_);
v___x_3669_ = lean_box(0);
v___x_3670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3670_, 0, v_name_3649_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3668_);
lean_ctor_set(v___x_3671_, 1, v_a_3664_);
lean_ctor_set(v___x_3671_, 2, v___x_3670_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set_tag(v___x_3666_, 2);
lean_ctor_set(v___x_3666_, 0, v___x_3671_);
v___x_3673_ = v___x_3666_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_addDecl(v___x_3673_, v___x_3651_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v___x_3675_; uint8_t v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
lean_dec_ref_known(v___x_3674_, 1);
v___x_3675_ = l_Lean_Meta_simpExtension;
v___x_3676_ = 0;
v___x_3677_ = lean_unsigned_to_nat(1000u);
v___x_3678_ = l_Lean_Meta_addSimpTheorem(v___x_3675_, v_name_3649_, v_hasTrace_3652_, v___x_3651_, v___x_3676_, v___x_3677_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
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
v_a_3681_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3659_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3659_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3689_, lean_object* v_val_3690_, lean_object* v_name_3691_, lean_object* v_levelParams_3692_, lean_object* v___x_3693_, lean_object* v_hasTrace_3694_, lean_object* v_____r_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
uint8_t v___x_8586__boxed_3701_; uint8_t v_hasTrace_boxed_3702_; lean_object* v_res_3703_; 
v___x_8586__boxed_3701_ = lean_unbox(v___x_3693_);
v_hasTrace_boxed_3702_ = lean_unbox(v_hasTrace_3694_);
v_res_3703_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3689_, v_val_3690_, v_name_3691_, v_levelParams_3692_, v___x_8586__boxed_3701_, v_hasTrace_boxed_3702_, v_____r_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3704_, lean_object* v_val_3705_, lean_object* v_name_3706_, lean_object* v_levelParams_3707_, uint8_t v___x_3708_, lean_object* v_____r_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; 
lean_inc_ref(v_val_3705_);
v___x_3715_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3704_, v_val_3705_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3737_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3705_, v___y_3711_);
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v___x_3719_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3716_, v___y_3711_);
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3737_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3737_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
lean_inc_n(v_name_3706_, 2);
v___x_3724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3724_, 0, v_name_3706_);
lean_ctor_set(v___x_3724_, 1, v_levelParams_3707_);
lean_ctor_set(v___x_3724_, 2, v_a_3718_);
v___x_3725_ = lean_box(0);
v___x_3726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3726_, 0, v_name_3706_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3724_);
lean_ctor_set(v___x_3727_, 1, v_a_3720_);
lean_ctor_set(v___x_3727_, 2, v___x_3726_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set_tag(v___x_3722_, 2);
lean_ctor_set(v___x_3722_, 0, v___x_3727_);
v___x_3729_ = v___x_3722_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
uint8_t v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = 0;
v___x_3731_ = l_Lean_addDecl(v___x_3729_, v___x_3730_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v___x_3732_; uint8_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_dec_ref_known(v___x_3731_, 1);
v___x_3732_ = l_Lean_Meta_simpExtension;
v___x_3733_ = 0;
v___x_3734_ = lean_unsigned_to_nat(1000u);
v___x_3735_ = l_Lean_Meta_addSimpTheorem(v___x_3732_, v_name_3706_, v___x_3708_, v___x_3730_, v___x_3733_, v___x_3734_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3735_;
}
else
{
lean_dec(v_name_3706_);
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_levelParams_3707_);
lean_dec(v_name_3706_);
lean_dec_ref(v_val_3705_);
v_a_3738_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3715_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3715_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3746_, lean_object* v_val_3747_, lean_object* v_name_3748_, lean_object* v_levelParams_3749_, lean_object* v___x_3750_, lean_object* v_____r_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
uint8_t v___x_8674__boxed_3757_; lean_object* v_res_3758_; 
v___x_8674__boxed_3757_ = lean_unbox(v___x_3750_);
v_res_3758_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3746_, v_val_3747_, v_name_3748_, v_levelParams_3749_, v___x_8674__boxed_3757_, v_____r_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v_toConstantVal_3765_; lean_object* v_options_3766_; lean_object* v_name_3767_; lean_object* v_levelParams_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3988_; 
v_toConstantVal_3765_ = lean_ctor_get(v_ctorVal_3759_, 0);
lean_inc_ref(v_toConstantVal_3765_);
v_options_3766_ = lean_ctor_get(v_a_3762_, 2);
v_name_3767_ = lean_ctor_get(v_toConstantVal_3765_, 0);
v_levelParams_3768_ = lean_ctor_get(v_toConstantVal_3765_, 1);
v_isSharedCheck_3988_ = !lean_is_exclusive(v_toConstantVal_3765_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v_toConstantVal_3765_, 2);
lean_dec(v_unused_3989_);
v___x_3770_ = v_toConstantVal_3765_;
v_isShared_3771_ = v_isSharedCheck_3988_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_levelParams_3768_);
lean_inc(v_name_3767_);
lean_dec(v_toConstantVal_3765_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3988_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v_inheritedTraceOptions_3772_; uint8_t v_hasTrace_3773_; lean_object* v_name_3774_; 
v_inheritedTraceOptions_3772_ = lean_ctor_get(v_a_3762_, 13);
v_hasTrace_3773_ = lean_ctor_get_uint8(v_options_3766_, sizeof(void*)*1);
v_name_3774_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3767_);
if (v_hasTrace_3773_ == 0)
{
lean_object* v___x_3775_; 
lean_inc_ref(v_ctorVal_3759_);
v___x_3775_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3818_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3818_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3818_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
if (lean_obj_tag(v_a_3776_) == 1)
{
lean_object* v_val_3780_; lean_object* v___x_3781_; 
lean_del_object(v___x_3778_);
v_val_3780_ = lean_ctor_get(v_a_3776_, 0);
lean_inc_n(v_val_3780_, 2);
lean_dec_ref_known(v_a_3776_, 1);
v___x_3781_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3759_, v_val_3780_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v_a_3784_; lean_object* v___x_3785_; lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3805_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v___x_3783_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3780_, v_a_3761_);
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref(v___x_3783_);
v___x_3785_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3782_, v_a_3761_);
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3788_ = v___x_3785_;
v_isShared_3789_ = v_isSharedCheck_3805_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3805_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
lean_inc(v_name_3774_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 2, v_a_3784_);
lean_ctor_set(v___x_3770_, 0, v_name_3774_);
v___x_3791_ = v___x_3770_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_name_3774_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_levelParams_3768_);
lean_ctor_set(v_reuseFailAlloc_3804_, 2, v_a_3784_);
v___x_3791_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3796_; 
v___x_3792_ = lean_box(0);
lean_inc(v_name_3774_);
v___x_3793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3793_, 0, v_name_3774_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3791_);
lean_ctor_set(v___x_3794_, 1, v_a_3786_);
lean_ctor_set(v___x_3794_, 2, v___x_3793_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set_tag(v___x_3788_, 2);
lean_ctor_set(v___x_3788_, 0, v___x_3794_);
v___x_3796_ = v___x_3788_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lean_addDecl(v___x_3796_, v_hasTrace_3773_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v___x_3798_; uint8_t v___x_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_dec_ref_known(v___x_3797_, 1);
v___x_3798_ = l_Lean_Meta_simpExtension;
v___x_3799_ = 1;
v___x_3800_ = 0;
v___x_3801_ = lean_unsigned_to_nat(1000u);
v___x_3802_ = l_Lean_Meta_addSimpTheorem(v___x_3798_, v_name_3774_, v___x_3799_, v_hasTrace_3773_, v___x_3800_, v___x_3801_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
return v___x_3802_;
}
else
{
lean_dec(v_name_3774_);
return v___x_3797_;
}
}
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec(v_val_3780_);
lean_dec(v_name_3774_);
lean_del_object(v___x_3770_);
lean_dec(v_levelParams_3768_);
v_a_3806_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3781_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3781_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
else
{
lean_object* v___x_3814_; lean_object* v___x_3816_; 
lean_dec(v_a_3776_);
lean_dec(v_name_3774_);
lean_del_object(v___x_3770_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v___x_3814_ = lean_box(0);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v___x_3814_);
v___x_3816_ = v___x_3778_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec(v_name_3774_);
lean_del_object(v___x_3770_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v_a_3819_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3775_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3775_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v___f_3827_; lean_object* v_cls_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v_a_3835_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v_a_3847_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v_a_3852_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v_a_3863_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v_a_3878_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v_a_3883_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; 
lean_inc(v_name_3774_);
v___f_3827_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3827_, 0, v_name_3774_);
v_cls_3828_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3829_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3830_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3831_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3772_, v_options_3766_, v___x_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3926_; uint8_t v___x_3927_; 
v___x_3926_ = l_Lean_trace_profiler;
v___x_3927_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3766_, v___x_3926_);
if (v___x_3927_ == 0)
{
lean_object* v___x_3928_; 
lean_dec_ref(v___f_3827_);
lean_inc_ref(v_ctorVal_3759_);
v___x_3928_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3979_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3979_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3979_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
if (lean_obj_tag(v_a_3929_) == 1)
{
lean_object* v_val_3933_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; 
lean_del_object(v___x_3931_);
v_val_3933_ = lean_ctor_get(v_a_3929_, 0);
lean_inc(v_val_3933_);
lean_dec_ref_known(v_a_3929_, 1);
if (v___x_3831_ == 0)
{
v___y_3935_ = v_a_3760_;
v___y_3936_ = v_a_3761_;
v___y_3937_ = v_a_3762_;
v___y_3938_ = v_a_3763_;
goto v___jp_3934_;
}
else
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3971_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3933_);
v___x_3972_ = l_Lean_MessageData_ofExpr(v_val_3933_);
v___x_3973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3971_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3828_, v___x_3973_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_dec_ref_known(v___x_3974_, 1);
v___y_3935_ = v_a_3760_;
v___y_3936_ = v_a_3761_;
v___y_3937_ = v_a_3762_;
v___y_3938_ = v_a_3763_;
goto v___jp_3934_;
}
else
{
lean_dec(v_val_3933_);
lean_dec(v_name_3774_);
lean_del_object(v___x_3770_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
return v___x_3974_;
}
}
v___jp_3934_:
{
lean_object* v___x_3939_; 
lean_inc(v_val_3933_);
v___x_3939_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3759_, v_val_3933_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3941_; lean_object* v_a_3942_; lean_object* v___x_3943_; lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3962_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
v___x_3941_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3933_, v___y_3936_);
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref(v___x_3941_);
v___x_3943_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3940_, v___y_3936_);
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3946_ = v___x_3943_;
v_isShared_3947_ = v_isSharedCheck_3962_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3943_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3962_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
lean_inc(v_name_3774_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 2, v_a_3942_);
lean_ctor_set(v___x_3770_, 0, v_name_3774_);
v___x_3949_ = v___x_3770_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_name_3774_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_levelParams_3768_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_a_3942_);
v___x_3949_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3954_; 
v___x_3950_ = lean_box(0);
lean_inc(v_name_3774_);
v___x_3951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3951_, 0, v_name_3774_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3949_);
lean_ctor_set(v___x_3952_, 1, v_a_3944_);
lean_ctor_set(v___x_3952_, 2, v___x_3951_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set_tag(v___x_3946_, 2);
lean_ctor_set(v___x_3946_, 0, v___x_3952_);
v___x_3954_ = v___x_3946_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_Lean_addDecl(v___x_3954_, v___x_3927_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v___x_3956_; uint8_t v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_dec_ref_known(v___x_3955_, 1);
v___x_3956_ = l_Lean_Meta_simpExtension;
v___x_3957_ = 0;
v___x_3958_ = lean_unsigned_to_nat(1000u);
v___x_3959_ = l_Lean_Meta_addSimpTheorem(v___x_3956_, v_name_3774_, v_hasTrace_3773_, v___x_3927_, v___x_3957_, v___x_3958_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
return v___x_3959_;
}
else
{
lean_dec(v_name_3774_);
return v___x_3955_;
}
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec(v_val_3933_);
lean_dec(v_name_3774_);
lean_del_object(v___x_3770_);
lean_dec(v_levelParams_3768_);
v_a_3963_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3939_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3939_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3977_; 
lean_dec(v_a_3929_);
lean_dec(v_name_3774_);
lean_del_object(v___x_3770_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v___x_3975_ = lean_box(0);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3975_);
v___x_3977_ = v___x_3931_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
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
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v_name_3774_);
lean_del_object(v___x_3770_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v_a_3980_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3928_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3928_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_del_object(v___x_3770_);
goto v___jp_3891_;
}
}
else
{
lean_del_object(v___x_3770_);
goto v___jp_3891_;
}
v___jp_3832_:
{
lean_object* v___x_3836_; double v___x_3837_; double v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3836_ = lean_io_get_num_heartbeats();
v___x_3837_ = lean_float_of_nat(v___y_3833_);
v___x_3838_ = lean_float_of_nat(v___x_3836_);
v___x_3839_ = lean_box_float(v___x_3837_);
v___x_3840_ = lean_box_float(v___x_3838_);
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3839_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v_a_3835_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3828_, v_hasTrace_3773_, v___x_3829_, v_options_3766_, v___x_3831_, v___y_3834_, v___f_3827_, v___x_3842_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
return v___x_3843_;
}
v___jp_3844_:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3848_, 0, v_a_3847_);
v___y_3833_ = v___y_3845_;
v___y_3834_ = v___y_3846_;
v_a_3835_ = v___x_3848_;
goto v___jp_3832_;
}
v___jp_3849_:
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_a_3852_);
v___y_3833_ = v___y_3850_;
v___y_3834_ = v___y_3851_;
v_a_3835_ = v___x_3853_;
goto v___jp_3832_;
}
v___jp_3854_:
{
if (lean_obj_tag(v___y_3857_) == 0)
{
lean_object* v_a_3858_; 
v_a_3858_ = lean_ctor_get(v___y_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___y_3857_, 1);
v___y_3850_ = v___y_3855_;
v___y_3851_ = v___y_3856_;
v_a_3852_ = v_a_3858_;
goto v___jp_3849_;
}
else
{
lean_object* v_a_3859_; 
v_a_3859_ = lean_ctor_get(v___y_3857_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___y_3857_, 1);
v___y_3845_ = v___y_3855_;
v___y_3846_ = v___y_3856_;
v_a_3847_ = v_a_3859_;
goto v___jp_3844_;
}
}
v___jp_3860_:
{
lean_object* v___x_3864_; double v___x_3865_; double v___x_3866_; double v___x_3867_; double v___x_3868_; double v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3864_ = lean_io_mono_nanos_now();
v___x_3865_ = lean_float_of_nat(v___y_3862_);
v___x_3866_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3867_ = lean_float_div(v___x_3865_, v___x_3866_);
v___x_3868_ = lean_float_of_nat(v___x_3864_);
v___x_3869_ = lean_float_div(v___x_3868_, v___x_3866_);
v___x_3870_ = lean_box_float(v___x_3867_);
v___x_3871_ = lean_box_float(v___x_3869_);
v___x_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3870_);
lean_ctor_set(v___x_3872_, 1, v___x_3871_);
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v_a_3863_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
v___x_3874_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3828_, v_hasTrace_3773_, v___x_3829_, v_options_3766_, v___x_3831_, v___y_3861_, v___f_3827_, v___x_3873_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
return v___x_3874_;
}
v___jp_3875_:
{
lean_object* v___x_3879_; 
v___x_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3879_, 0, v_a_3878_);
v___y_3861_ = v___y_3876_;
v___y_3862_ = v___y_3877_;
v_a_3863_ = v___x_3879_;
goto v___jp_3860_;
}
v___jp_3880_:
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v_a_3883_);
v___y_3861_ = v___y_3881_;
v___y_3862_ = v___y_3882_;
v_a_3863_ = v___x_3884_;
goto v___jp_3860_;
}
v___jp_3885_:
{
if (lean_obj_tag(v___y_3888_) == 0)
{
lean_object* v_a_3889_; 
v_a_3889_ = lean_ctor_get(v___y_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___y_3888_, 1);
v___y_3876_ = v___y_3886_;
v___y_3877_ = v___y_3887_;
v_a_3878_ = v_a_3889_;
goto v___jp_3875_;
}
else
{
lean_object* v_a_3890_; 
v_a_3890_ = lean_ctor_get(v___y_3888_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___y_3888_, 1);
v___y_3881_ = v___y_3886_;
v___y_3882_ = v___y_3887_;
v_a_3883_ = v_a_3890_;
goto v___jp_3880_;
}
}
v___jp_3891_:
{
lean_object* v___x_3892_; lean_object* v_a_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3892_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3763_);
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref(v___x_3892_);
v___x_3894_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3895_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3766_, v___x_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3759_);
v___x_3897_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
if (lean_obj_tag(v_a_3898_) == 1)
{
if (v___x_3831_ == 0)
{
lean_object* v_val_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_val_3899_ = lean_ctor_get(v_a_3898_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v_a_3898_, 1);
v___x_3900_ = lean_box(0);
v___x_3901_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3759_, v_val_3899_, v_name_3774_, v_levelParams_3768_, v___x_3895_, v_hasTrace_3773_, v___x_3900_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
v___y_3886_ = v_a_3893_;
v___y_3887_ = v___x_3896_;
v___y_3888_ = v___x_3901_;
goto v___jp_3885_;
}
else
{
lean_object* v_val_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_val_3902_ = lean_ctor_get(v_a_3898_, 0);
lean_inc_n(v_val_3902_, 2);
lean_dec_ref_known(v_a_3898_, 1);
v___x_3903_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3904_ = l_Lean_MessageData_ofExpr(v_val_3902_);
v___x_3905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3903_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
v___x_3906_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3828_, v___x_3905_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3908_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3906_, 1);
v___x_3908_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3759_, v_val_3902_, v_name_3774_, v_levelParams_3768_, v___x_3895_, v_hasTrace_3773_, v_a_3907_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
v___y_3886_ = v_a_3893_;
v___y_3887_ = v___x_3896_;
v___y_3888_ = v___x_3908_;
goto v___jp_3885_;
}
else
{
lean_dec(v_val_3902_);
lean_dec(v_name_3774_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v___y_3886_ = v_a_3893_;
v___y_3887_ = v___x_3896_;
v___y_3888_ = v___x_3906_;
goto v___jp_3885_;
}
}
}
else
{
lean_object* v___x_3909_; 
lean_dec(v_a_3898_);
lean_dec(v_name_3774_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v___x_3909_ = lean_box(0);
v___y_3876_ = v_a_3893_;
v___y_3877_ = v___x_3896_;
v_a_3878_ = v___x_3909_;
goto v___jp_3875_;
}
}
else
{
lean_object* v_a_3910_; 
lean_dec(v_name_3774_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v_a_3910_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3897_, 1);
v___y_3881_ = v_a_3893_;
v___y_3882_ = v___x_3896_;
v_a_3883_ = v_a_3910_;
goto v___jp_3880_;
}
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3759_);
v___x_3912_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
if (lean_obj_tag(v_a_3913_) == 1)
{
if (v___x_3831_ == 0)
{
lean_object* v_val_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_val_3914_ = lean_ctor_get(v_a_3913_, 0);
lean_inc(v_val_3914_);
lean_dec_ref_known(v_a_3913_, 1);
v___x_3915_ = lean_box(0);
v___x_3916_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3759_, v_val_3914_, v_name_3774_, v_levelParams_3768_, v___x_3895_, v___x_3915_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
v___y_3855_ = v___x_3911_;
v___y_3856_ = v_a_3893_;
v___y_3857_ = v___x_3916_;
goto v___jp_3854_;
}
else
{
lean_object* v_val_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v_val_3917_ = lean_ctor_get(v_a_3913_, 0);
lean_inc_n(v_val_3917_, 2);
lean_dec_ref_known(v_a_3913_, 1);
v___x_3918_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3919_ = l_Lean_MessageData_ofExpr(v_val_3917_);
v___x_3920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3828_, v___x_3920_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3921_, 1);
v___x_3923_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3759_, v_val_3917_, v_name_3774_, v_levelParams_3768_, v___x_3895_, v_a_3922_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_);
v___y_3855_ = v___x_3911_;
v___y_3856_ = v_a_3893_;
v___y_3857_ = v___x_3923_;
goto v___jp_3854_;
}
else
{
lean_dec(v_val_3917_);
lean_dec(v_name_3774_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v___y_3855_ = v___x_3911_;
v___y_3856_ = v_a_3893_;
v___y_3857_ = v___x_3921_;
goto v___jp_3854_;
}
}
}
else
{
lean_object* v___x_3924_; 
lean_dec(v_a_3913_);
lean_dec(v_name_3774_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v___x_3924_ = lean_box(0);
v___y_3850_ = v___x_3911_;
v___y_3851_ = v_a_3893_;
v_a_3852_ = v___x_3924_;
goto v___jp_3849_;
}
}
else
{
lean_object* v_a_3925_; 
lean_dec(v_name_3774_);
lean_dec(v_levelParams_3768_);
lean_dec_ref(v_ctorVal_3759_);
v_a_3925_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3912_, 1);
v___y_3845_ = v___x_3911_;
v___y_3846_ = v_a_3893_;
v_a_3847_ = v_a_3925_;
goto v___jp_3844_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3997_, lean_object* v_decl_3998_, lean_object* v_ref_3999_){
_start:
{
lean_object* v_defValue_4001_; lean_object* v_descr_4002_; lean_object* v_deprecation_x3f_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v_defValue_4001_ = lean_ctor_get(v_decl_3998_, 0);
v_descr_4002_ = lean_ctor_get(v_decl_3998_, 1);
v_deprecation_x3f_4003_ = lean_ctor_get(v_decl_3998_, 2);
v___x_4004_ = lean_alloc_ctor(1, 0, 1);
v___x_4005_ = lean_unbox(v_defValue_4001_);
lean_ctor_set_uint8(v___x_4004_, 0, v___x_4005_);
lean_inc(v_deprecation_x3f_4003_);
lean_inc_ref(v_descr_4002_);
lean_inc_n(v_name_3997_, 2);
v___x_4006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4006_, 0, v_name_3997_);
lean_ctor_set(v___x_4006_, 1, v_ref_3999_);
lean_ctor_set(v___x_4006_, 2, v___x_4004_);
lean_ctor_set(v___x_4006_, 3, v_descr_4002_);
lean_ctor_set(v___x_4006_, 4, v_deprecation_x3f_4003_);
v___x_4007_ = lean_register_option(v_name_3997_, v___x_4006_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4015_; 
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4015_ == 0)
{
lean_object* v_unused_4016_; 
v_unused_4016_ = lean_ctor_get(v___x_4007_, 0);
lean_dec(v_unused_4016_);
v___x_4009_ = v___x_4007_;
v_isShared_4010_ = v_isSharedCheck_4015_;
goto v_resetjp_4008_;
}
else
{
lean_dec(v___x_4007_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4015_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4013_; 
lean_inc(v_defValue_4001_);
v___x_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4011_, 0, v_name_3997_);
lean_ctor_set(v___x_4011_, 1, v_defValue_4001_);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 0, v___x_4011_);
v___x_4013_ = v___x_4009_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec(v_name_3997_);
v_a_4017_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4007_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4007_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4025_, lean_object* v_decl_4026_, lean_object* v_ref_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4025_, v_decl_4026_, v_ref_4027_);
lean_dec_ref(v_decl_4026_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4044_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4045_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4046_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4047_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4044_, v___x_4045_, v___x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4050_, uint8_t v_isExporting_4051_, lean_object* v___x_4052_, lean_object* v___y_4053_, lean_object* v___x_4054_, lean_object* v_a_x3f_4055_){
_start:
{
lean_object* v___x_4057_; lean_object* v_env_4058_; lean_object* v_nextMacroScope_4059_; lean_object* v_ngen_4060_; lean_object* v_auxDeclNGen_4061_; lean_object* v_traceState_4062_; lean_object* v_messages_4063_; lean_object* v_infoState_4064_; lean_object* v_snapshotTasks_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4090_; 
v___x_4057_ = lean_st_ref_take(v___y_4050_);
v_env_4058_ = lean_ctor_get(v___x_4057_, 0);
v_nextMacroScope_4059_ = lean_ctor_get(v___x_4057_, 1);
v_ngen_4060_ = lean_ctor_get(v___x_4057_, 2);
v_auxDeclNGen_4061_ = lean_ctor_get(v___x_4057_, 3);
v_traceState_4062_ = lean_ctor_get(v___x_4057_, 4);
v_messages_4063_ = lean_ctor_get(v___x_4057_, 6);
v_infoState_4064_ = lean_ctor_get(v___x_4057_, 7);
v_snapshotTasks_4065_ = lean_ctor_get(v___x_4057_, 8);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v___x_4057_, 5);
lean_dec(v_unused_4091_);
v___x_4067_ = v___x_4057_;
v_isShared_4068_ = v_isSharedCheck_4090_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_snapshotTasks_4065_);
lean_inc(v_infoState_4064_);
lean_inc(v_messages_4063_);
lean_inc(v_traceState_4062_);
lean_inc(v_auxDeclNGen_4061_);
lean_inc(v_ngen_4060_);
lean_inc(v_nextMacroScope_4059_);
lean_inc(v_env_4058_);
lean_dec(v___x_4057_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4090_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4071_; 
v___x_4069_ = l_Lean_Environment_setExporting(v_env_4058_, v_isExporting_4051_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 5, v___x_4052_);
lean_ctor_set(v___x_4067_, 0, v___x_4069_);
v___x_4071_ = v___x_4067_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_nextMacroScope_4059_);
lean_ctor_set(v_reuseFailAlloc_4089_, 2, v_ngen_4060_);
lean_ctor_set(v_reuseFailAlloc_4089_, 3, v_auxDeclNGen_4061_);
lean_ctor_set(v_reuseFailAlloc_4089_, 4, v_traceState_4062_);
lean_ctor_set(v_reuseFailAlloc_4089_, 5, v___x_4052_);
lean_ctor_set(v_reuseFailAlloc_4089_, 6, v_messages_4063_);
lean_ctor_set(v_reuseFailAlloc_4089_, 7, v_infoState_4064_);
lean_ctor_set(v_reuseFailAlloc_4089_, 8, v_snapshotTasks_4065_);
v___x_4071_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v_mctx_4074_; lean_object* v_zetaDeltaFVarIds_4075_; lean_object* v_postponed_4076_; lean_object* v_diag_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4087_; 
v___x_4072_ = lean_st_ref_put(v___y_4050_, v___x_4071_);
v___x_4073_ = lean_st_ref_take(v___y_4053_);
v_mctx_4074_ = lean_ctor_get(v___x_4073_, 0);
v_zetaDeltaFVarIds_4075_ = lean_ctor_get(v___x_4073_, 2);
v_postponed_4076_ = lean_ctor_get(v___x_4073_, 3);
v_diag_4077_ = lean_ctor_get(v___x_4073_, 4);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; 
v_unused_4088_ = lean_ctor_get(v___x_4073_, 1);
lean_dec(v_unused_4088_);
v___x_4079_ = v___x_4073_;
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_diag_4077_);
lean_inc(v_postponed_4076_);
lean_inc(v_zetaDeltaFVarIds_4075_);
lean_inc(v_mctx_4074_);
lean_dec(v___x_4073_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 1, v___x_4054_);
v___x_4082_ = v___x_4079_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_mctx_4074_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v___x_4054_);
lean_ctor_set(v_reuseFailAlloc_4086_, 2, v_zetaDeltaFVarIds_4075_);
lean_ctor_set(v_reuseFailAlloc_4086_, 3, v_postponed_4076_);
lean_ctor_set(v_reuseFailAlloc_4086_, 4, v_diag_4077_);
v___x_4082_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4083_ = lean_st_ref_put(v___y_4053_, v___x_4082_);
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
return v___x_4085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4092_, lean_object* v_isExporting_4093_, lean_object* v___x_4094_, lean_object* v___y_4095_, lean_object* v___x_4096_, lean_object* v_a_x3f_4097_, lean_object* v___y_4098_){
_start:
{
uint8_t v_isExporting_boxed_4099_; lean_object* v_res_4100_; 
v_isExporting_boxed_4099_ = lean_unbox(v_isExporting_4093_);
v_res_4100_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4092_, v_isExporting_boxed_4099_, v___x_4094_, v___y_4095_, v___x_4096_, v_a_x3f_4097_);
lean_dec(v_a_x3f_4097_);
lean_dec(v___y_4095_);
lean_dec(v___y_4092_);
return v_res_4100_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4101_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4102_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
return v___x_4103_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4104_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
return v___x_4105_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4107_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
lean_ctor_set(v___x_4107_, 2, v___x_4106_);
lean_ctor_set(v___x_4107_, 3, v___x_4106_);
lean_ctor_set(v___x_4107_, 4, v___x_4106_);
lean_ctor_set(v___x_4107_, 5, v___x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4108_, uint8_t v_isExporting_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v___x_4115_; lean_object* v_env_4116_; lean_object* v___x_4117_; uint8_t v_isModule_4118_; 
v___x_4115_ = lean_st_ref_get(v___y_4113_);
v_env_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc_ref(v_env_4116_);
lean_dec(v___x_4115_);
v___x_4117_ = l_Lean_Environment_header(v_env_4116_);
v_isModule_4118_ = lean_ctor_get_uint8(v___x_4117_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4117_);
if (v_isModule_4118_ == 0)
{
lean_object* v___x_4119_; 
lean_dec_ref(v_env_4116_);
lean_inc(v___y_4113_);
lean_inc_ref(v___y_4112_);
lean_inc(v___y_4111_);
lean_inc_ref(v___y_4110_);
v___x_4119_ = lean_apply_5(v_x_4108_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, lean_box(0));
return v___x_4119_;
}
else
{
uint8_t v_isExporting_4120_; 
v_isExporting_4120_ = lean_ctor_get_uint8(v_env_4116_, sizeof(void*)*8);
lean_dec_ref(v_env_4116_);
if (v_isExporting_4109_ == 0)
{
if (v_isExporting_4120_ == 0)
{
lean_object* v___x_4186_; 
lean_inc(v___y_4113_);
lean_inc_ref(v___y_4112_);
lean_inc(v___y_4111_);
lean_inc_ref(v___y_4110_);
v___x_4186_ = lean_apply_5(v_x_4108_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, lean_box(0));
return v___x_4186_;
}
else
{
goto v___jp_4121_;
}
}
else
{
if (v_isExporting_4120_ == 0)
{
goto v___jp_4121_;
}
else
{
lean_object* v___x_4187_; 
lean_inc(v___y_4113_);
lean_inc_ref(v___y_4112_);
lean_inc(v___y_4111_);
lean_inc_ref(v___y_4110_);
v___x_4187_ = lean_apply_5(v_x_4108_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, lean_box(0));
return v___x_4187_;
}
}
v___jp_4121_:
{
lean_object* v___x_4122_; lean_object* v_env_4123_; lean_object* v_nextMacroScope_4124_; lean_object* v_ngen_4125_; lean_object* v_auxDeclNGen_4126_; lean_object* v_traceState_4127_; lean_object* v_messages_4128_; lean_object* v_infoState_4129_; lean_object* v_snapshotTasks_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4184_; 
v___x_4122_ = lean_st_ref_take(v___y_4113_);
v_env_4123_ = lean_ctor_get(v___x_4122_, 0);
v_nextMacroScope_4124_ = lean_ctor_get(v___x_4122_, 1);
v_ngen_4125_ = lean_ctor_get(v___x_4122_, 2);
v_auxDeclNGen_4126_ = lean_ctor_get(v___x_4122_, 3);
v_traceState_4127_ = lean_ctor_get(v___x_4122_, 4);
v_messages_4128_ = lean_ctor_get(v___x_4122_, 6);
v_infoState_4129_ = lean_ctor_get(v___x_4122_, 7);
v_snapshotTasks_4130_ = lean_ctor_get(v___x_4122_, 8);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4184_ == 0)
{
lean_object* v_unused_4185_; 
v_unused_4185_ = lean_ctor_get(v___x_4122_, 5);
lean_dec(v_unused_4185_);
v___x_4132_ = v___x_4122_;
v_isShared_4133_ = v_isSharedCheck_4184_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_snapshotTasks_4130_);
lean_inc(v_infoState_4129_);
lean_inc(v_messages_4128_);
lean_inc(v_traceState_4127_);
lean_inc(v_auxDeclNGen_4126_);
lean_inc(v_ngen_4125_);
lean_inc(v_nextMacroScope_4124_);
lean_inc(v_env_4123_);
lean_dec(v___x_4122_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4184_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
v___x_4134_ = l_Lean_Environment_setExporting(v_env_4123_, v_isExporting_4109_);
v___x_4135_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 5, v___x_4135_);
lean_ctor_set(v___x_4132_, 0, v___x_4134_);
v___x_4137_ = v___x_4132_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4134_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v_nextMacroScope_4124_);
lean_ctor_set(v_reuseFailAlloc_4183_, 2, v_ngen_4125_);
lean_ctor_set(v_reuseFailAlloc_4183_, 3, v_auxDeclNGen_4126_);
lean_ctor_set(v_reuseFailAlloc_4183_, 4, v_traceState_4127_);
lean_ctor_set(v_reuseFailAlloc_4183_, 5, v___x_4135_);
lean_ctor_set(v_reuseFailAlloc_4183_, 6, v_messages_4128_);
lean_ctor_set(v_reuseFailAlloc_4183_, 7, v_infoState_4129_);
lean_ctor_set(v_reuseFailAlloc_4183_, 8, v_snapshotTasks_4130_);
v___x_4137_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v_mctx_4140_; lean_object* v_zetaDeltaFVarIds_4141_; lean_object* v_postponed_4142_; lean_object* v_diag_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4181_; 
v___x_4138_ = lean_st_ref_put(v___y_4113_, v___x_4137_);
v___x_4139_ = lean_st_ref_take(v___y_4111_);
v_mctx_4140_ = lean_ctor_get(v___x_4139_, 0);
v_zetaDeltaFVarIds_4141_ = lean_ctor_get(v___x_4139_, 2);
v_postponed_4142_ = lean_ctor_get(v___x_4139_, 3);
v_diag_4143_ = lean_ctor_get(v___x_4139_, 4);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4181_ == 0)
{
lean_object* v_unused_4182_; 
v_unused_4182_ = lean_ctor_get(v___x_4139_, 1);
lean_dec(v_unused_4182_);
v___x_4145_ = v___x_4139_;
v_isShared_4146_ = v_isSharedCheck_4181_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_diag_4143_);
lean_inc(v_postponed_4142_);
lean_inc(v_zetaDeltaFVarIds_4141_);
lean_inc(v_mctx_4140_);
lean_dec(v___x_4139_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4181_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4147_; lean_object* v___x_4149_; 
v___x_4147_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 1, v___x_4147_);
v___x_4149_ = v___x_4145_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_mctx_4140_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v___x_4147_);
lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_zetaDeltaFVarIds_4141_);
lean_ctor_set(v_reuseFailAlloc_4180_, 3, v_postponed_4142_);
lean_ctor_set(v_reuseFailAlloc_4180_, 4, v_diag_4143_);
v___x_4149_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4150_; lean_object* v_r_4151_; 
v___x_4150_ = lean_st_ref_put(v___y_4111_, v___x_4149_);
lean_inc(v___y_4113_);
lean_inc_ref(v___y_4112_);
lean_inc(v___y_4111_);
lean_inc_ref(v___y_4110_);
v_r_4151_ = lean_apply_5(v_x_4108_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, lean_box(0));
if (lean_obj_tag(v_r_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4168_; 
v_a_4152_ = lean_ctor_get(v_r_4151_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v_r_4151_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4154_ = v_r_4151_;
v_isShared_4155_ = v_isSharedCheck_4168_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v_r_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4168_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
lean_inc(v_a_4152_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set_tag(v___x_4154_, 1);
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
v___x_4158_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4113_, v_isExporting_4120_, v___x_4135_, v___y_4111_, v___x_4147_, v___x_4157_);
lean_dec_ref(v___x_4157_);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4165_ == 0)
{
lean_object* v_unused_4166_; 
v_unused_4166_ = lean_ctor_get(v___x_4158_, 0);
lean_dec(v_unused_4166_);
v___x_4160_ = v___x_4158_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_dec(v___x_4158_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v_a_4152_);
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4152_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
v_a_4169_ = lean_ctor_get(v_r_4151_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v_r_4151_, 1);
v___x_4170_ = lean_box(0);
v___x_4171_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4113_, v_isExporting_4120_, v___x_4135_, v___y_4111_, v___x_4147_, v___x_4170_);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4178_ == 0)
{
lean_object* v_unused_4179_; 
v_unused_4179_ = lean_ctor_get(v___x_4171_, 0);
lean_dec(v_unused_4179_);
v___x_4173_ = v___x_4171_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_dec(v___x_4171_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
lean_ctor_set_tag(v___x_4173_, 1);
lean_ctor_set(v___x_4173_, 0, v_a_4169_);
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4169_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4188_, lean_object* v_isExporting_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
uint8_t v_isExporting_boxed_4195_; lean_object* v_res_4196_; 
v_isExporting_boxed_4195_ = lean_unbox(v_isExporting_4189_);
v_res_4196_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4188_, v_isExporting_boxed_4195_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4197_, lean_object* v_x_4198_, uint8_t v_isExporting_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4198_, v_isExporting_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4206_, lean_object* v_x_4207_, lean_object* v_isExporting_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
uint8_t v_isExporting_boxed_4214_; lean_object* v_res_4215_; 
v_isExporting_boxed_4214_ = lean_unbox(v_isExporting_4208_);
v_res_4215_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4206_, v_x_4207_, v_isExporting_boxed_4214_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4216_, lean_object* v_localInsts_4217_, lean_object* v_x_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4216_, v_localInsts_4217_, v_x_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
v_a_4233_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4224_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4224_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4241_, lean_object* v_localInsts_4242_, lean_object* v_x_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4241_, v_localInsts_4242_, v_x_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4250_, lean_object* v_lctx_4251_, lean_object* v_localInsts_4252_, lean_object* v_x_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v___x_4259_; 
v___x_4259_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4251_, v_localInsts_4252_, v_x_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4260_, lean_object* v_lctx_4261_, lean_object* v_localInsts_4262_, lean_object* v_x_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4260_, v_lctx_4261_, v_localInsts_4262_, v_x_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4270_, lean_object* v_x_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = l_Lean_MessageData_ofName(v_declName_4270_);
v___x_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4279_, lean_object* v_x_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4279_, v_x_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v_x_4280_);
return v_res_4286_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_instMonadEIO(lean_box(0));
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v_toApplicative_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4361_; 
v___x_4298_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4299_ = l_StateRefT_x27_instMonad___redArg(v___x_4298_);
v_toApplicative_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4361_ == 0)
{
lean_object* v_unused_4362_; 
v_unused_4362_ = lean_ctor_get(v___x_4299_, 1);
lean_dec(v_unused_4362_);
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4361_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_toApplicative_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4361_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v_toFunctor_4304_; lean_object* v_toSeq_4305_; lean_object* v_toSeqLeft_4306_; lean_object* v_toSeqRight_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4359_; 
v_toFunctor_4304_ = lean_ctor_get(v_toApplicative_4300_, 0);
v_toSeq_4305_ = lean_ctor_get(v_toApplicative_4300_, 2);
v_toSeqLeft_4306_ = lean_ctor_get(v_toApplicative_4300_, 3);
v_toSeqRight_4307_ = lean_ctor_get(v_toApplicative_4300_, 4);
v_isSharedCheck_4359_ = !lean_is_exclusive(v_toApplicative_4300_);
if (v_isSharedCheck_4359_ == 0)
{
lean_object* v_unused_4360_; 
v_unused_4360_ = lean_ctor_get(v_toApplicative_4300_, 1);
lean_dec(v_unused_4360_);
v___x_4309_ = v_toApplicative_4300_;
v_isShared_4310_ = v_isSharedCheck_4359_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_toSeqRight_4307_);
lean_inc(v_toSeqLeft_4306_);
lean_inc(v_toSeq_4305_);
lean_inc(v_toFunctor_4304_);
lean_dec(v_toApplicative_4300_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4359_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___f_4311_; lean_object* v___f_4312_; lean_object* v___f_4313_; lean_object* v___f_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___f_4317_; lean_object* v___f_4318_; lean_object* v___x_4320_; 
v___f_4311_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4312_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4304_);
v___f_4313_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4313_, 0, v_toFunctor_4304_);
v___f_4314_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4314_, 0, v_toFunctor_4304_);
v___x_4315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4315_, 0, v___f_4313_);
lean_ctor_set(v___x_4315_, 1, v___f_4314_);
v___f_4316_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4316_, 0, v_toSeqRight_4307_);
v___f_4317_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4317_, 0, v_toSeqLeft_4306_);
v___f_4318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4318_, 0, v_toSeq_4305_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 4, v___f_4316_);
lean_ctor_set(v___x_4309_, 3, v___f_4317_);
lean_ctor_set(v___x_4309_, 2, v___f_4318_);
lean_ctor_set(v___x_4309_, 1, v___f_4311_);
lean_ctor_set(v___x_4309_, 0, v___x_4315_);
v___x_4320_ = v___x_4309_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4315_);
lean_ctor_set(v_reuseFailAlloc_4358_, 1, v___f_4311_);
lean_ctor_set(v_reuseFailAlloc_4358_, 2, v___f_4318_);
lean_ctor_set(v_reuseFailAlloc_4358_, 3, v___f_4317_);
lean_ctor_set(v_reuseFailAlloc_4358_, 4, v___f_4316_);
v___x_4320_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
lean_object* v___x_4322_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 1, v___f_4312_);
lean_ctor_set(v___x_4302_, 0, v___x_4320_);
v___x_4322_ = v___x_4302_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4320_);
lean_ctor_set(v_reuseFailAlloc_4357_, 1, v___f_4312_);
v___x_4322_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
lean_object* v___x_4323_; lean_object* v_toApplicative_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4355_; 
v___x_4323_ = l_StateRefT_x27_instMonad___redArg(v___x_4322_);
v_toApplicative_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4355_ == 0)
{
lean_object* v_unused_4356_; 
v_unused_4356_ = lean_ctor_get(v___x_4323_, 1);
lean_dec(v_unused_4356_);
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4355_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_toApplicative_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4355_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v_toFunctor_4328_; lean_object* v_toSeq_4329_; lean_object* v_toSeqLeft_4330_; lean_object* v_toSeqRight_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4353_; 
v_toFunctor_4328_ = lean_ctor_get(v_toApplicative_4324_, 0);
v_toSeq_4329_ = lean_ctor_get(v_toApplicative_4324_, 2);
v_toSeqLeft_4330_ = lean_ctor_get(v_toApplicative_4324_, 3);
v_toSeqRight_4331_ = lean_ctor_get(v_toApplicative_4324_, 4);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_toApplicative_4324_);
if (v_isSharedCheck_4353_ == 0)
{
lean_object* v_unused_4354_; 
v_unused_4354_ = lean_ctor_get(v_toApplicative_4324_, 1);
lean_dec(v_unused_4354_);
v___x_4333_ = v_toApplicative_4324_;
v_isShared_4334_ = v_isSharedCheck_4353_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_toSeqRight_4331_);
lean_inc(v_toSeqLeft_4330_);
lean_inc(v_toSeq_4329_);
lean_inc(v_toFunctor_4328_);
lean_dec(v_toApplicative_4324_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4353_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___f_4335_; lean_object* v___f_4336_; lean_object* v___f_4337_; lean_object* v___f_4338_; lean_object* v___x_4339_; lean_object* v___f_4340_; lean_object* v___f_4341_; lean_object* v___f_4342_; lean_object* v___x_4344_; 
v___f_4335_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4336_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4328_);
v___f_4337_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4337_, 0, v_toFunctor_4328_);
v___f_4338_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4338_, 0, v_toFunctor_4328_);
v___x_4339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4339_, 0, v___f_4337_);
lean_ctor_set(v___x_4339_, 1, v___f_4338_);
v___f_4340_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4340_, 0, v_toSeqRight_4331_);
v___f_4341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4341_, 0, v_toSeqLeft_4330_);
v___f_4342_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4342_, 0, v_toSeq_4329_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 4, v___f_4340_);
lean_ctor_set(v___x_4333_, 3, v___f_4341_);
lean_ctor_set(v___x_4333_, 2, v___f_4342_);
lean_ctor_set(v___x_4333_, 1, v___f_4335_);
lean_ctor_set(v___x_4333_, 0, v___x_4339_);
v___x_4344_ = v___x_4333_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4339_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v___f_4335_);
lean_ctor_set(v_reuseFailAlloc_4352_, 2, v___f_4342_);
lean_ctor_set(v_reuseFailAlloc_4352_, 3, v___f_4341_);
lean_ctor_set(v_reuseFailAlloc_4352_, 4, v___f_4340_);
v___x_4344_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
lean_object* v___x_4346_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 1, v___f_4336_);
lean_ctor_set(v___x_4326_, 0, v___x_4344_);
v___x_4346_ = v___x_4326_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4344_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v___f_4336_);
v___x_4346_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_15640__overap_4349_; lean_object* v___x_4350_; 
v___x_4347_ = lean_box(0);
v___x_4348_ = l_instInhabitedOfMonad___redArg(v___x_4346_, v___x_4347_);
v___x_15640__overap_4349_ = lean_panic_fn_borrowed(v___x_4348_, v_msg_4292_);
lean_dec(v___x_4348_);
lean_inc(v___y_4296_);
lean_inc_ref(v___y_4295_);
lean_inc(v___y_4294_);
lean_inc_ref(v___y_4293_);
v___x_4350_ = lean_apply_5(v___x_15640__overap_4349_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, lean_box(0));
return v___x_4350_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
return v_res_4369_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4371_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4372_ = l_Lean_stringToMessageData(v___x_4371_);
return v___x_4372_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4375_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4376_ = lean_unsigned_to_nat(11u);
v___x_4377_ = lean_unsigned_to_nat(122u);
v___x_4378_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4379_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4380_ = l_mkPanicMessageWithDecl(v___x_4379_, v___x_4378_, v___x_4377_, v___x_4376_, v___x_4375_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___x_4395_; lean_object* v_env_4396_; uint8_t v___x_4397_; lean_object* v___x_4398_; 
v___x_4395_ = lean_st_ref_get(v___y_4385_);
v_env_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc_ref(v_env_4396_);
lean_dec(v___x_4395_);
v___x_4397_ = 0;
lean_inc(v_constName_4381_);
v___x_4398_ = l_Lean_Environment_findAsync_x3f(v_env_4396_, v_constName_4381_, v___x_4397_);
if (lean_obj_tag(v___x_4398_) == 1)
{
lean_object* v_val_4399_; uint8_t v_kind_4400_; 
v_val_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_val_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v_kind_4400_ = lean_ctor_get_uint8(v_val_4399_, sizeof(void*)*3);
if (v_kind_4400_ == 6)
{
lean_object* v___x_4401_; 
v___x_4401_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4399_);
if (lean_obj_tag(v___x_4401_) == 6)
{
lean_object* v_val_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec(v_constName_4381_);
v_val_4402_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4401_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_val_4402_);
lean_dec(v___x_4401_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
lean_ctor_set_tag(v___x_4404_, 0);
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_val_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
else
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_dec_ref(v___x_4401_);
v___x_4410_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4411_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4410_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4420_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4414_ = v___x_4411_;
v_isShared_4415_ = v_isSharedCheck_4420_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4411_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4420_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
if (lean_obj_tag(v_a_4412_) == 0)
{
lean_del_object(v___x_4414_);
goto v___jp_4387_;
}
else
{
lean_object* v_val_4416_; lean_object* v___x_4418_; 
lean_dec(v_constName_4381_);
v_val_4416_ = lean_ctor_get(v_a_4412_, 0);
lean_inc(v_val_4416_);
lean_dec_ref_known(v_a_4412_, 1);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v_val_4416_);
v___x_4418_ = v___x_4414_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_val_4416_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec(v_constName_4381_);
v_a_4421_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4411_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4411_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
else
{
lean_dec(v_val_4399_);
goto v___jp_4387_;
}
}
else
{
lean_dec(v___x_4398_);
goto v___jp_4387_;
}
v___jp_4387_:
{
lean_object* v___x_4388_; uint8_t v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4388_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4389_ = 0;
v___x_4390_ = l_Lean_MessageData_ofConstName(v_constName_4381_, v___x_4389_);
v___x_4391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4388_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4391_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4393_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
return v___x_4394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4436_, lean_object* v___x_4437_, lean_object* v___x_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4436_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4456_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4447_ = v___x_4444_;
v_isShared_4448_ = v_isSharedCheck_4456_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4444_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4456_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v_numFields_4449_; uint8_t v___x_4450_; 
v_numFields_4449_ = lean_ctor_get(v_a_4445_, 4);
v___x_4450_ = lean_nat_dec_lt(v___x_4437_, v_numFields_4449_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4452_; 
lean_dec(v_a_4445_);
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 0, v___x_4438_);
v___x_4452_ = v___x_4447_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4438_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
else
{
lean_object* v___x_4454_; 
lean_del_object(v___x_4447_);
lean_inc(v_a_4445_);
v___x_4454_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4445_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v___x_4455_; 
lean_dec_ref_known(v___x_4454_, 1);
v___x_4455_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4445_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
return v___x_4455_;
}
else
{
lean_dec(v_a_4445_);
return v___x_4454_;
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
v_a_4457_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4444_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4444_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4465_, lean_object* v___x_4466_, lean_object* v___x_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4465_, v___x_4466_, v___x_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___x_4466_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4474_, uint8_t v___x_4475_, lean_object* v_as_x27_4476_, lean_object* v_b_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
if (lean_obj_tag(v_as_x27_4476_) == 0)
{
lean_object* v___x_4483_; 
v___x_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4483_, 0, v_b_4477_);
return v___x_4483_;
}
else
{
lean_object* v_head_4484_; lean_object* v_tail_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___f_4488_; uint8_t v___y_4490_; uint8_t v___x_4493_; 
v_head_4484_ = lean_ctor_get(v_as_x27_4476_, 0);
v_tail_4485_ = lean_ctor_get(v_as_x27_4476_, 1);
v___x_4486_ = lean_unsigned_to_nat(0u);
v___x_4487_ = lean_box(0);
lean_inc(v_head_4484_);
v___f_4488_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4488_, 0, v_head_4484_);
lean_closure_set(v___f_4488_, 1, v___x_4486_);
lean_closure_set(v___f_4488_, 2, v___x_4487_);
v___x_4493_ = l_Lean_isPrivateName(v_head_4484_);
if (v___x_4493_ == 0)
{
v___y_4490_ = v___y_4474_;
goto v___jp_4489_;
}
else
{
v___y_4490_ = v___x_4475_;
goto v___jp_4489_;
}
v___jp_4489_:
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4488_, v___y_4490_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_dec_ref_known(v___x_4491_, 1);
v_as_x27_4476_ = v_tail_4485_;
v_b_4477_ = v___x_4487_;
goto _start;
}
else
{
return v___x_4491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4494_, lean_object* v___x_4495_, lean_object* v_as_x27_4496_, lean_object* v_b_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
uint8_t v___y_16747__boxed_4503_; uint8_t v___x_16748__boxed_4504_; lean_object* v_res_4505_; 
v___y_16747__boxed_4503_ = lean_unbox(v___y_4494_);
v___x_16748__boxed_4504_ = lean_unbox(v___x_4495_);
v_res_4505_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_16747__boxed_4503_, v___x_16748__boxed_4504_, v_as_x27_4496_, v_b_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v_as_x27_4496_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4506_, uint8_t v_isUnsafe_4507_, lean_object* v_ctors_4508_, lean_object* v___x_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4506_, v_isUnsafe_4507_, v_ctors_4508_, v___x_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4522_ == 0)
{
lean_object* v_unused_4523_; 
v_unused_4523_ = lean_ctor_get(v___x_4515_, 0);
lean_dec(v_unused_4523_);
v___x_4517_ = v___x_4515_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_dec(v___x_4515_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
lean_ctor_set(v___x_4517_, 0, v___x_4509_);
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4509_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
else
{
return v___x_4515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4524_, lean_object* v_isUnsafe_4525_, lean_object* v_ctors_4526_, lean_object* v___x_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
uint8_t v___y_16792__boxed_4533_; uint8_t v_isUnsafe_boxed_4534_; lean_object* v_res_4535_; 
v___y_16792__boxed_4533_ = lean_unbox(v___y_4524_);
v_isUnsafe_boxed_4534_ = lean_unbox(v_isUnsafe_4525_);
v_res_4535_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_16792__boxed_4533_, v_isUnsafe_boxed_4534_, v_ctors_4526_, v___x_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v_ctors_4526_);
return v_res_4535_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4538_ = l_Lean_stringToMessageData(v___x_4537_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v___x_4545_; lean_object* v_env_4546_; lean_object* v___x_4547_; 
v___x_4545_ = lean_st_ref_get(v___y_4543_);
v_env_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc_ref(v_env_4546_);
lean_dec(v___x_4545_);
lean_inc(v_constName_4539_);
v___x_4547_ = l_Lean_isInductiveCore_x3f(v_env_4546_, v_constName_4539_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v___x_4548_; uint8_t v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4548_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4549_ = 0;
v___x_4550_ = l_Lean_MessageData_ofConstName(v_constName_4539_, v___x_4549_);
v___x_4551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4548_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
v___x_4552_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4551_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
v___x_4554_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4553_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
return v___x_4554_;
}
else
{
lean_object* v_val_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_constName_4539_);
v_val_4555_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4547_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_val_4555_);
lean_dec(v___x_4547_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
lean_ctor_set_tag(v___x_4557_, 0);
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_val_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
return v_res_4569_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4570_; 
v___x_4570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4570_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4571_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
return v___x_4572_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4573_ = lean_unsigned_to_nat(32u);
v___x_4574_ = lean_mk_empty_array_with_capacity(v___x_4573_);
v___x_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
return v___x_4575_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4576_ = ((size_t)5ULL);
v___x_4577_ = lean_unsigned_to_nat(0u);
v___x_4578_ = lean_unsigned_to_nat(32u);
v___x_4579_ = lean_mk_empty_array_with_capacity(v___x_4578_);
v___x_4580_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4581_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4581_, 0, v___x_4580_);
lean_ctor_set(v___x_4581_, 1, v___x_4579_);
lean_ctor_set(v___x_4581_, 2, v___x_4577_);
lean_ctor_set(v___x_4581_, 3, v___x_4577_);
lean_ctor_set_usize(v___x_4581_, 4, v___x_4576_);
return v___x_4581_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4582_ = lean_box(1);
v___x_4583_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4584_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
lean_ctor_set(v___x_4585_, 1, v___x_4583_);
lean_ctor_set(v___x_4585_, 2, v___x_4582_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4594_ = lean_st_ref_get(v_a_4592_);
lean_inc(v_declName_4588_);
v___x_4595_ = l_Lean_Meta_isInductivePredicate(v_declName_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4792_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4598_ = v___x_4595_;
v_isShared_4599_ = v_isSharedCheck_4792_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4595_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4792_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v_env_4605_; lean_object* v___f_4606_; lean_object* v___x_4607_; uint8_t v___x_4608_; uint8_t v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v_a_4616_; uint8_t v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v_a_4632_; uint8_t v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v_a_4641_; lean_object* v___y_4644_; uint8_t v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v_a_4650_; lean_object* v___y_4663_; uint8_t v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v_a_4669_; lean_object* v___y_4672_; uint8_t v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v_a_4678_; uint8_t v___y_4681_; uint8_t v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; uint8_t v___y_4723_; uint8_t v___x_4788_; 
v_env_4605_ = lean_ctor_get(v___x_4594_, 0);
lean_inc_ref(v_env_4605_);
lean_dec(v___x_4594_);
lean_inc(v_declName_4588_);
v___f_4606_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4606_, 0, v_declName_4588_);
v___x_4607_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4608_ = 1;
v___x_4788_ = l_Lean_Environment_contains(v_env_4605_, v___x_4607_, v___x_4608_);
if (v___x_4788_ == 0)
{
v___y_4723_ = v___x_4788_;
goto v___jp_4722_;
}
else
{
lean_object* v_options_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; 
v_options_4789_ = lean_ctor_get(v_a_4591_, 2);
v___x_4790_ = l_Lean_Meta_genInjectivity;
v___x_4791_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4789_, v___x_4790_);
v___y_4723_ = v___x_4791_;
goto v___jp_4722_;
}
v___jp_4600_:
{
lean_object* v___x_4601_; lean_object* v___x_4603_; 
v___x_4601_ = lean_box(0);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v___x_4601_);
v___x_4603_ = v___x_4598_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4601_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
v___jp_4609_:
{
lean_object* v___x_4617_; double v___x_4618_; double v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4617_ = lean_io_get_num_heartbeats();
v___x_4618_ = lean_float_of_nat(v___y_4615_);
v___x_4619_ = lean_float_of_nat(v___x_4617_);
v___x_4620_ = lean_box_float(v___x_4618_);
v___x_4621_ = lean_box_float(v___x_4619_);
v___x_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4620_);
lean_ctor_set(v___x_4622_, 1, v___x_4621_);
v___x_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4623_, 0, v_a_4616_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
lean_inc_ref(v___y_4612_);
lean_inc(v___y_4614_);
v___x_4624_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4614_, v___x_4608_, v___y_4612_, v___y_4611_, v___y_4610_, v___y_4613_, v___f_4606_, v___x_4623_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4624_;
}
v___jp_4625_:
{
lean_object* v___x_4633_; 
v___x_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4633_, 0, v_a_4632_);
v___y_4610_ = v___y_4626_;
v___y_4611_ = v___y_4627_;
v___y_4612_ = v___y_4628_;
v___y_4613_ = v___y_4629_;
v___y_4614_ = v___y_4630_;
v___y_4615_ = v___y_4631_;
v_a_4616_ = v___x_4633_;
goto v___jp_4609_;
}
v___jp_4634_:
{
lean_object* v___x_4642_; 
v___x_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4642_, 0, v_a_4641_);
v___y_4610_ = v___y_4635_;
v___y_4611_ = v___y_4636_;
v___y_4612_ = v___y_4637_;
v___y_4613_ = v___y_4638_;
v___y_4614_ = v___y_4639_;
v___y_4615_ = v___y_4640_;
v_a_4616_ = v___x_4642_;
goto v___jp_4609_;
}
v___jp_4643_:
{
lean_object* v___x_4651_; double v___x_4652_; double v___x_4653_; double v___x_4654_; double v___x_4655_; double v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4651_ = lean_io_mono_nanos_now();
v___x_4652_ = lean_float_of_nat(v___y_4644_);
v___x_4653_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4654_ = lean_float_div(v___x_4652_, v___x_4653_);
v___x_4655_ = lean_float_of_nat(v___x_4651_);
v___x_4656_ = lean_float_div(v___x_4655_, v___x_4653_);
v___x_4657_ = lean_box_float(v___x_4654_);
v___x_4658_ = lean_box_float(v___x_4656_);
v___x_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4657_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v_a_4650_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
lean_inc_ref(v___y_4647_);
lean_inc(v___y_4649_);
v___x_4661_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4649_, v___x_4608_, v___y_4647_, v___y_4646_, v___y_4645_, v___y_4648_, v___f_4606_, v___x_4660_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4661_;
}
v___jp_4662_:
{
lean_object* v___x_4670_; 
v___x_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4670_, 0, v_a_4669_);
v___y_4644_ = v___y_4663_;
v___y_4645_ = v___y_4664_;
v___y_4646_ = v___y_4665_;
v___y_4647_ = v___y_4666_;
v___y_4648_ = v___y_4667_;
v___y_4649_ = v___y_4668_;
v_a_4650_ = v___x_4670_;
goto v___jp_4643_;
}
v___jp_4671_:
{
lean_object* v___x_4679_; 
v___x_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4679_, 0, v_a_4678_);
v___y_4644_ = v___y_4672_;
v___y_4645_ = v___y_4673_;
v___y_4646_ = v___y_4674_;
v___y_4647_ = v___y_4675_;
v___y_4648_ = v___y_4676_;
v___y_4649_ = v___y_4677_;
v_a_4650_ = v___x_4679_;
goto v___jp_4643_;
}
v___jp_4680_:
{
lean_object* v___x_4686_; lean_object* v_a_4687_; lean_object* v___x_4688_; uint8_t v___x_4689_; 
v___x_4686_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4592_);
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4687_);
lean_dec_ref(v___x_4686_);
v___x_4688_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4689_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4683_, v___x_4688_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4690_ = lean_io_mono_nanos_now();
v___x_4691_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; uint8_t v_isUnsafe_4693_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_a_4692_);
lean_dec_ref_known(v___x_4691_, 1);
v_isUnsafe_4693_ = lean_ctor_get_uint8(v_a_4692_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4693_ == 0)
{
lean_object* v_ctors_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___f_4700_; lean_object* v___x_4701_; 
v_ctors_4694_ = lean_ctor_get(v_a_4692_, 4);
lean_inc(v_ctors_4694_);
lean_dec(v_a_4692_);
v___x_4695_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4696_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4697_ = lean_box(0);
v___x_4698_ = lean_box(v___y_4681_);
v___x_4699_ = lean_box(v_isUnsafe_4693_);
v___f_4700_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4700_, 0, v___x_4698_);
lean_closure_set(v___f_4700_, 1, v___x_4699_);
lean_closure_set(v___f_4700_, 2, v_ctors_4694_);
lean_closure_set(v___f_4700_, 3, v___x_4697_);
v___x_4701_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4695_, v___x_4696_, v___f_4700_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4701_, 1);
v___y_4663_ = v___x_4690_;
v___y_4664_ = v___y_4682_;
v___y_4665_ = v___y_4683_;
v___y_4666_ = v___y_4684_;
v___y_4667_ = v_a_4687_;
v___y_4668_ = v___y_4685_;
v_a_4669_ = v_a_4702_;
goto v___jp_4662_;
}
else
{
lean_object* v_a_4703_; 
v_a_4703_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4703_);
lean_dec_ref_known(v___x_4701_, 1);
v___y_4672_ = v___x_4690_;
v___y_4673_ = v___y_4682_;
v___y_4674_ = v___y_4683_;
v___y_4675_ = v___y_4684_;
v___y_4676_ = v_a_4687_;
v___y_4677_ = v___y_4685_;
v_a_4678_ = v_a_4703_;
goto v___jp_4671_;
}
}
else
{
lean_object* v___x_4704_; 
lean_dec(v_a_4692_);
v___x_4704_ = lean_box(0);
v___y_4663_ = v___x_4690_;
v___y_4664_ = v___y_4682_;
v___y_4665_ = v___y_4683_;
v___y_4666_ = v___y_4684_;
v___y_4667_ = v_a_4687_;
v___y_4668_ = v___y_4685_;
v_a_4669_ = v___x_4704_;
goto v___jp_4662_;
}
}
else
{
lean_object* v_a_4705_; 
v_a_4705_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_a_4705_);
lean_dec_ref_known(v___x_4691_, 1);
v___y_4672_ = v___x_4690_;
v___y_4673_ = v___y_4682_;
v___y_4674_ = v___y_4683_;
v___y_4675_ = v___y_4684_;
v___y_4676_ = v_a_4687_;
v___y_4677_ = v___y_4685_;
v_a_4678_ = v_a_4705_;
goto v___jp_4671_;
}
}
else
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = lean_io_get_num_heartbeats();
v___x_4707_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; uint8_t v_isUnsafe_4709_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4708_);
lean_dec_ref_known(v___x_4707_, 1);
v_isUnsafe_4709_ = lean_ctor_get_uint8(v_a_4708_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4709_ == 0)
{
lean_object* v_ctors_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___f_4716_; lean_object* v___x_4717_; 
v_ctors_4710_ = lean_ctor_get(v_a_4708_, 4);
lean_inc(v_ctors_4710_);
lean_dec(v_a_4708_);
v___x_4711_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4712_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4713_ = lean_box(0);
v___x_4714_ = lean_box(v___y_4681_);
v___x_4715_ = lean_box(v_isUnsafe_4709_);
v___f_4716_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4716_, 0, v___x_4714_);
lean_closure_set(v___f_4716_, 1, v___x_4715_);
lean_closure_set(v___f_4716_, 2, v_ctors_4710_);
lean_closure_set(v___f_4716_, 3, v___x_4713_);
v___x_4717_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4711_, v___x_4712_, v___f_4716_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v_a_4718_; 
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4718_);
lean_dec_ref_known(v___x_4717_, 1);
v___y_4626_ = v___y_4682_;
v___y_4627_ = v___y_4683_;
v___y_4628_ = v___y_4684_;
v___y_4629_ = v_a_4687_;
v___y_4630_ = v___y_4685_;
v___y_4631_ = v___x_4706_;
v_a_4632_ = v_a_4718_;
goto v___jp_4625_;
}
else
{
lean_object* v_a_4719_; 
v_a_4719_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4719_);
lean_dec_ref_known(v___x_4717_, 1);
v___y_4635_ = v___y_4682_;
v___y_4636_ = v___y_4683_;
v___y_4637_ = v___y_4684_;
v___y_4638_ = v_a_4687_;
v___y_4639_ = v___y_4685_;
v___y_4640_ = v___x_4706_;
v_a_4641_ = v_a_4719_;
goto v___jp_4634_;
}
}
else
{
lean_object* v___x_4720_; 
lean_dec(v_a_4708_);
v___x_4720_ = lean_box(0);
v___y_4626_ = v___y_4682_;
v___y_4627_ = v___y_4683_;
v___y_4628_ = v___y_4684_;
v___y_4629_ = v_a_4687_;
v___y_4630_ = v___y_4685_;
v___y_4631_ = v___x_4706_;
v_a_4632_ = v___x_4720_;
goto v___jp_4625_;
}
}
else
{
lean_object* v_a_4721_; 
v_a_4721_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4707_, 1);
v___y_4635_ = v___y_4682_;
v___y_4636_ = v___y_4683_;
v___y_4637_ = v___y_4684_;
v___y_4638_ = v_a_4687_;
v___y_4639_ = v___y_4685_;
v___y_4640_ = v___x_4706_;
v_a_4641_ = v_a_4721_;
goto v___jp_4634_;
}
}
}
v___jp_4722_:
{
if (v___y_4723_ == 0)
{
lean_dec_ref(v___f_4606_);
lean_dec(v_a_4596_);
lean_dec(v_declName_4588_);
goto v___jp_4600_;
}
else
{
uint8_t v___x_4724_; 
v___x_4724_ = lean_unbox(v_a_4596_);
lean_dec(v_a_4596_);
if (v___x_4724_ == 0)
{
lean_object* v_options_4725_; uint8_t v_hasTrace_4726_; 
lean_del_object(v___x_4598_);
v_options_4725_ = lean_ctor_get(v_a_4591_, 2);
v_hasTrace_4726_ = lean_ctor_get_uint8(v_options_4725_, sizeof(void*)*1);
if (v_hasTrace_4726_ == 0)
{
lean_object* v___x_4727_; 
lean_dec_ref(v___f_4606_);
v___x_4727_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4745_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4727_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4730_ = v___x_4727_;
v_isShared_4731_ = v_isSharedCheck_4745_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4727_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4745_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
uint8_t v_isUnsafe_4732_; 
v_isUnsafe_4732_ = lean_ctor_get_uint8(v_a_4728_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4732_ == 0)
{
lean_object* v_ctors_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___f_4739_; lean_object* v___x_4740_; 
lean_del_object(v___x_4730_);
v_ctors_4733_ = lean_ctor_get(v_a_4728_, 4);
lean_inc(v_ctors_4733_);
lean_dec(v_a_4728_);
v___x_4734_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4735_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4736_ = lean_box(0);
v___x_4737_ = lean_box(v___y_4723_);
v___x_4738_ = lean_box(v_isUnsafe_4732_);
v___f_4739_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4739_, 0, v___x_4737_);
lean_closure_set(v___f_4739_, 1, v___x_4738_);
lean_closure_set(v___f_4739_, 2, v_ctors_4733_);
lean_closure_set(v___f_4739_, 3, v___x_4736_);
v___x_4740_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4734_, v___x_4735_, v___f_4739_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4740_;
}
else
{
lean_object* v___x_4741_; lean_object* v___x_4743_; 
lean_dec(v_a_4728_);
v___x_4741_ = lean_box(0);
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 0, v___x_4741_);
v___x_4743_ = v___x_4730_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4741_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
v_a_4746_ = lean_ctor_get(v___x_4727_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4727_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4727_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4727_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; 
v_inheritedTraceOptions_4754_ = lean_ctor_get(v_a_4591_, 13);
v___x_4755_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4756_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4757_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4758_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4754_, v_options_4725_, v___x_4757_);
if (v___x_4758_ == 0)
{
lean_object* v___x_4759_; uint8_t v___x_4760_; 
v___x_4759_ = l_Lean_trace_profiler;
v___x_4760_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4725_, v___x_4759_);
if (v___x_4760_ == 0)
{
lean_object* v___x_4761_; 
lean_dec_ref(v___f_4606_);
v___x_4761_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4779_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4764_ = v___x_4761_;
v_isShared_4765_ = v_isSharedCheck_4779_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4761_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4779_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
uint8_t v_isUnsafe_4766_; 
v_isUnsafe_4766_ = lean_ctor_get_uint8(v_a_4762_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4766_ == 0)
{
lean_object* v_ctors_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___f_4773_; lean_object* v___x_4774_; 
lean_del_object(v___x_4764_);
v_ctors_4767_ = lean_ctor_get(v_a_4762_, 4);
lean_inc(v_ctors_4767_);
lean_dec(v_a_4762_);
v___x_4768_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4769_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4770_ = lean_box(0);
v___x_4771_ = lean_box(v___y_4723_);
v___x_4772_ = lean_box(v_isUnsafe_4766_);
v___f_4773_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4773_, 0, v___x_4771_);
lean_closure_set(v___f_4773_, 1, v___x_4772_);
lean_closure_set(v___f_4773_, 2, v_ctors_4767_);
lean_closure_set(v___f_4773_, 3, v___x_4770_);
v___x_4774_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4768_, v___x_4769_, v___f_4773_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4774_;
}
else
{
lean_object* v___x_4775_; lean_object* v___x_4777_; 
lean_dec(v_a_4762_);
v___x_4775_ = lean_box(0);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 0, v___x_4775_);
v___x_4777_ = v___x_4764_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4775_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
}
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
v_a_4780_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___x_4761_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4761_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
else
{
v___y_4681_ = v___y_4723_;
v___y_4682_ = v___x_4758_;
v___y_4683_ = v_options_4725_;
v___y_4684_ = v___x_4756_;
v___y_4685_ = v___x_4755_;
goto v___jp_4680_;
}
}
else
{
v___y_4681_ = v___y_4723_;
v___y_4682_ = v___x_4758_;
v___y_4683_ = v_options_4725_;
v___y_4684_ = v___x_4756_;
v___y_4685_ = v___x_4755_;
goto v___jp_4680_;
}
}
}
else
{
lean_dec_ref(v___f_4606_);
lean_dec(v_declName_4588_);
goto v___jp_4600_;
}
}
}
}
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_dec(v___x_4594_);
lean_dec(v_declName_4588_);
v_a_4793_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4595_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4595_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
return v_res_4807_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4808_, uint8_t v___x_4809_, lean_object* v_as_4810_, lean_object* v_as_x27_4811_, lean_object* v_b_4812_, lean_object* v_a_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_){
_start:
{
lean_object* v___x_4819_; 
v___x_4819_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4808_, v___x_4809_, v_as_x27_4811_, v_b_4812_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4820_, lean_object* v___x_4821_, lean_object* v_as_4822_, lean_object* v_as_x27_4823_, lean_object* v_b_4824_, lean_object* v_a_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
uint8_t v___y_17419__boxed_4831_; uint8_t v___x_17420__boxed_4832_; lean_object* v_res_4833_; 
v___y_17419__boxed_4831_ = lean_unbox(v___y_4820_);
v___x_17420__boxed_4832_ = lean_unbox(v___x_4821_);
v_res_4833_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_17419__boxed_4831_, v___x_17420__boxed_4832_, v_as_4822_, v_as_x27_4823_, v_b_4824_, v_a_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v_as_x27_4823_);
lean_dec(v_as_4822_);
return v_res_4833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4874_ = lean_unsigned_to_nat(4172903888u);
v___x_4875_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4876_ = l_Lean_Name_num___override(v___x_4875_, v___x_4874_);
return v___x_4876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4878_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4879_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4880_ = l_Lean_Name_str___override(v___x_4879_, v___x_4878_);
return v___x_4880_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4882_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4883_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4884_ = l_Lean_Name_str___override(v___x_4883_, v___x_4882_);
return v___x_4884_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4885_ = lean_unsigned_to_nat(2u);
v___x_4886_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4887_ = l_Lean_Name_num___override(v___x_4886_, v___x_4885_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4889_; uint8_t v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4889_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4890_ = 0;
v___x_4891_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4892_ = l_Lean_registerTraceClass(v___x_4889_, v___x_4890_, v___x_4891_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4895_, lean_object* v_b_4896_){
_start:
{
lean_object* v_array_4897_; lean_object* v_start_4898_; lean_object* v_stop_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4912_; 
v_array_4897_ = lean_ctor_get(v_a_4895_, 0);
v_start_4898_ = lean_ctor_get(v_a_4895_, 1);
v_stop_4899_ = lean_ctor_get(v_a_4895_, 2);
v_isSharedCheck_4912_ = !lean_is_exclusive(v_a_4895_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4901_ = v_a_4895_;
v_isShared_4902_ = v_isSharedCheck_4912_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_stop_4899_);
lean_inc(v_start_4898_);
lean_inc(v_array_4897_);
lean_dec(v_a_4895_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4912_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
uint8_t v___x_4903_; 
v___x_4903_ = lean_nat_dec_lt(v_start_4898_, v_stop_4899_);
if (v___x_4903_ == 0)
{
lean_del_object(v___x_4901_);
lean_dec(v_stop_4899_);
lean_dec(v_start_4898_);
lean_dec_ref(v_array_4897_);
return v_b_4896_;
}
else
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4907_; 
v___x_4904_ = lean_unsigned_to_nat(1u);
v___x_4905_ = lean_nat_add(v_start_4898_, v___x_4904_);
lean_inc_ref(v_array_4897_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 1, v___x_4905_);
v___x_4907_ = v___x_4901_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_array_4897_);
lean_ctor_set(v_reuseFailAlloc_4911_, 1, v___x_4905_);
lean_ctor_set(v_reuseFailAlloc_4911_, 2, v_stop_4899_);
v___x_4907_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = lean_array_fget(v_array_4897_, v_start_4898_);
lean_dec(v_start_4898_);
lean_dec_ref(v_array_4897_);
v___x_4909_ = lean_array_push(v_b_4896_, v___x_4908_);
v_a_4895_ = v___x_4907_;
v_b_4896_ = v___x_4909_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4913_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
return v___x_4915_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4916_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4917_ = lean_unsigned_to_nat(0u);
v___x_4918_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
lean_ctor_set(v___x_4918_, 1, v___x_4917_);
lean_ctor_set(v___x_4918_, 2, v___x_4917_);
lean_ctor_set(v___x_4918_, 3, v___x_4917_);
lean_ctor_set(v___x_4918_, 4, v___x_4916_);
lean_ctor_set(v___x_4918_, 5, v___x_4916_);
lean_ctor_set(v___x_4918_, 6, v___x_4916_);
lean_ctor_set(v___x_4918_, 7, v___x_4916_);
lean_ctor_set(v___x_4918_, 8, v___x_4916_);
lean_ctor_set(v___x_4918_, 9, v___x_4916_);
lean_ctor_set(v___x_4918_, 10, v___x_4916_);
return v___x_4918_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4919_ = lean_box(1);
v___x_4920_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4922_, 0, v___x_4921_);
lean_ctor_set(v___x_4922_, 1, v___x_4920_);
lean_ctor_set(v___x_4922_, 2, v___x_4919_);
return v___x_4922_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4924_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4925_ = l_Lean_stringToMessageData(v___x_4924_);
return v___x_4925_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4928_ = l_Lean_stringToMessageData(v___x_4927_);
return v___x_4928_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
v___x_4930_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4931_ = l_Lean_stringToMessageData(v___x_4930_);
return v___x_4931_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; 
v___x_4933_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4934_ = l_Lean_stringToMessageData(v___x_4933_);
return v___x_4934_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4936_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4937_ = l_Lean_stringToMessageData(v___x_4936_);
return v___x_4937_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4940_ = l_Lean_stringToMessageData(v___x_4939_);
return v___x_4940_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4942_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4943_ = l_Lean_stringToMessageData(v___x_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4944_, lean_object* v_declHint_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v___x_4948_; lean_object* v_env_4949_; uint8_t v___x_4950_; 
v___x_4948_ = lean_st_ref_get(v___y_4946_);
v_env_4949_ = lean_ctor_get(v___x_4948_, 0);
lean_inc_ref(v_env_4949_);
lean_dec(v___x_4948_);
v___x_4950_ = l_Lean_Name_isAnonymous(v_declHint_4945_);
if (v___x_4950_ == 0)
{
uint8_t v_isExporting_4951_; 
v_isExporting_4951_ = lean_ctor_get_uint8(v_env_4949_, sizeof(void*)*8);
if (v_isExporting_4951_ == 0)
{
lean_object* v___x_4952_; 
lean_dec_ref(v_env_4949_);
lean_dec(v_declHint_4945_);
v___x_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4952_, 0, v_msg_4944_);
return v___x_4952_;
}
else
{
lean_object* v___x_4953_; uint8_t v___x_4954_; 
lean_inc_ref(v_env_4949_);
v___x_4953_ = l_Lean_Environment_setExporting(v_env_4949_, v___x_4950_);
lean_inc(v_declHint_4945_);
lean_inc_ref(v___x_4953_);
v___x_4954_ = l_Lean_Environment_contains(v___x_4953_, v_declHint_4945_, v_isExporting_4951_);
if (v___x_4954_ == 0)
{
lean_object* v___x_4955_; 
lean_dec_ref(v___x_4953_);
lean_dec_ref(v_env_4949_);
lean_dec(v_declHint_4945_);
v___x_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4955_, 0, v_msg_4944_);
return v___x_4955_;
}
else
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v_c_4961_; lean_object* v___x_4962_; 
v___x_4956_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4957_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4958_ = l_Lean_Options_empty;
v___x_4959_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4953_);
lean_ctor_set(v___x_4959_, 1, v___x_4956_);
lean_ctor_set(v___x_4959_, 2, v___x_4957_);
lean_ctor_set(v___x_4959_, 3, v___x_4958_);
lean_inc(v_declHint_4945_);
v___x_4960_ = l_Lean_MessageData_ofConstName(v_declHint_4945_, v___x_4950_);
v_c_4961_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4961_, 0, v___x_4959_);
lean_ctor_set(v_c_4961_, 1, v___x_4960_);
v___x_4962_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4949_, v_declHint_4945_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_dec_ref(v_env_4949_);
lean_dec(v_declHint_4945_);
v___x_4963_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4964_, 0, v___x_4963_);
lean_ctor_set(v___x_4964_, 1, v_c_4961_);
v___x_4965_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4964_);
lean_ctor_set(v___x_4966_, 1, v___x_4965_);
v___x_4967_ = l_Lean_MessageData_note(v___x_4966_);
v___x_4968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4968_, 0, v_msg_4944_);
lean_ctor_set(v___x_4968_, 1, v___x_4967_);
v___x_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
return v___x_4969_;
}
else
{
lean_object* v_val_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_5005_; 
v_val_4970_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_4972_ = v___x_4962_;
v_isShared_4973_ = v_isSharedCheck_5005_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_val_4970_);
lean_dec(v___x_4962_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_5005_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v_mod_4977_; uint8_t v___x_4978_; 
v___x_4974_ = lean_box(0);
v___x_4975_ = l_Lean_Environment_header(v_env_4949_);
lean_dec_ref(v_env_4949_);
v___x_4976_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4975_);
v_mod_4977_ = lean_array_get(v___x_4974_, v___x_4976_, v_val_4970_);
lean_dec(v_val_4970_);
lean_dec_ref(v___x_4976_);
v___x_4978_ = l_Lean_isPrivateName(v_declHint_4945_);
lean_dec(v_declHint_4945_);
if (v___x_4978_ == 0)
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4990_; 
v___x_4979_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_4980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4979_);
lean_ctor_set(v___x_4980_, 1, v_c_4961_);
v___x_4981_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_4982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4980_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
v___x_4983_ = l_Lean_MessageData_ofName(v_mod_4977_);
v___x_4984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4982_);
lean_ctor_set(v___x_4984_, 1, v___x_4983_);
v___x_4985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_4986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4984_);
lean_ctor_set(v___x_4986_, 1, v___x_4985_);
v___x_4987_ = l_Lean_MessageData_note(v___x_4986_);
v___x_4988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4988_, 0, v_msg_4944_);
lean_ctor_set(v___x_4988_, 1, v___x_4987_);
if (v_isShared_4973_ == 0)
{
lean_ctor_set_tag(v___x_4972_, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4988_);
v___x_4990_ = v___x_4972_;
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
else
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5003_; 
v___x_4992_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4992_);
lean_ctor_set(v___x_4993_, 1, v_c_4961_);
v___x_4994_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_4995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4993_);
lean_ctor_set(v___x_4995_, 1, v___x_4994_);
v___x_4996_ = l_Lean_MessageData_ofName(v_mod_4977_);
v___x_4997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4995_);
lean_ctor_set(v___x_4997_, 1, v___x_4996_);
v___x_4998_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_4999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4997_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
v___x_5000_ = l_Lean_MessageData_note(v___x_4999_);
v___x_5001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5001_, 0, v_msg_4944_);
lean_ctor_set(v___x_5001_, 1, v___x_5000_);
if (v_isShared_4973_ == 0)
{
lean_ctor_set_tag(v___x_4972_, 0);
lean_ctor_set(v___x_4972_, 0, v___x_5001_);
v___x_5003_ = v___x_4972_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5001_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5006_; 
lean_dec_ref(v_env_4949_);
lean_dec(v_declHint_4945_);
v___x_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5006_, 0, v_msg_4944_);
return v___x_5006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_5007_, lean_object* v_declHint_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5007_, v_declHint_5008_, v___y_5009_);
lean_dec(v___y_5009_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_5012_, lean_object* v_declHint_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_){
_start:
{
lean_object* v___x_5019_; lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5029_; 
v___x_5019_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5012_, v_declHint_5013_, v___y_5017_);
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5022_ = v___x_5019_;
v_isShared_5023_ = v_isSharedCheck_5029_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5019_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5029_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5027_; 
v___x_5024_ = l_Lean_unknownIdentifierMessageTag;
v___x_5025_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5024_);
lean_ctor_set(v___x_5025_, 1, v_a_5020_);
if (v_isShared_5023_ == 0)
{
lean_ctor_set(v___x_5022_, 0, v___x_5025_);
v___x_5027_ = v___x_5022_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v___x_5025_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5030_, lean_object* v_declHint_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5030_, v_declHint_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5038_, lean_object* v_msg_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v_fileName_5045_; lean_object* v_fileMap_5046_; lean_object* v_options_5047_; lean_object* v_currRecDepth_5048_; lean_object* v_maxRecDepth_5049_; lean_object* v_ref_5050_; lean_object* v_currNamespace_5051_; lean_object* v_openDecls_5052_; lean_object* v_initHeartbeats_5053_; lean_object* v_maxHeartbeats_5054_; lean_object* v_quotContext_5055_; lean_object* v_currMacroScope_5056_; uint8_t v_diag_5057_; lean_object* v_cancelTk_x3f_5058_; uint8_t v_suppressElabErrors_5059_; lean_object* v_inheritedTraceOptions_5060_; lean_object* v_ref_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v_fileName_5045_ = lean_ctor_get(v___y_5042_, 0);
v_fileMap_5046_ = lean_ctor_get(v___y_5042_, 1);
v_options_5047_ = lean_ctor_get(v___y_5042_, 2);
v_currRecDepth_5048_ = lean_ctor_get(v___y_5042_, 3);
v_maxRecDepth_5049_ = lean_ctor_get(v___y_5042_, 4);
v_ref_5050_ = lean_ctor_get(v___y_5042_, 5);
v_currNamespace_5051_ = lean_ctor_get(v___y_5042_, 6);
v_openDecls_5052_ = lean_ctor_get(v___y_5042_, 7);
v_initHeartbeats_5053_ = lean_ctor_get(v___y_5042_, 8);
v_maxHeartbeats_5054_ = lean_ctor_get(v___y_5042_, 9);
v_quotContext_5055_ = lean_ctor_get(v___y_5042_, 10);
v_currMacroScope_5056_ = lean_ctor_get(v___y_5042_, 11);
v_diag_5057_ = lean_ctor_get_uint8(v___y_5042_, sizeof(void*)*14);
v_cancelTk_x3f_5058_ = lean_ctor_get(v___y_5042_, 12);
v_suppressElabErrors_5059_ = lean_ctor_get_uint8(v___y_5042_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5060_ = lean_ctor_get(v___y_5042_, 13);
v_ref_5061_ = l_Lean_replaceRef(v_ref_5038_, v_ref_5050_);
lean_inc_ref(v_inheritedTraceOptions_5060_);
lean_inc(v_cancelTk_x3f_5058_);
lean_inc(v_currMacroScope_5056_);
lean_inc(v_quotContext_5055_);
lean_inc(v_maxHeartbeats_5054_);
lean_inc(v_initHeartbeats_5053_);
lean_inc(v_openDecls_5052_);
lean_inc(v_currNamespace_5051_);
lean_inc(v_maxRecDepth_5049_);
lean_inc(v_currRecDepth_5048_);
lean_inc_ref(v_options_5047_);
lean_inc_ref(v_fileMap_5046_);
lean_inc_ref(v_fileName_5045_);
v___x_5062_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5062_, 0, v_fileName_5045_);
lean_ctor_set(v___x_5062_, 1, v_fileMap_5046_);
lean_ctor_set(v___x_5062_, 2, v_options_5047_);
lean_ctor_set(v___x_5062_, 3, v_currRecDepth_5048_);
lean_ctor_set(v___x_5062_, 4, v_maxRecDepth_5049_);
lean_ctor_set(v___x_5062_, 5, v_ref_5061_);
lean_ctor_set(v___x_5062_, 6, v_currNamespace_5051_);
lean_ctor_set(v___x_5062_, 7, v_openDecls_5052_);
lean_ctor_set(v___x_5062_, 8, v_initHeartbeats_5053_);
lean_ctor_set(v___x_5062_, 9, v_maxHeartbeats_5054_);
lean_ctor_set(v___x_5062_, 10, v_quotContext_5055_);
lean_ctor_set(v___x_5062_, 11, v_currMacroScope_5056_);
lean_ctor_set(v___x_5062_, 12, v_cancelTk_x3f_5058_);
lean_ctor_set(v___x_5062_, 13, v_inheritedTraceOptions_5060_);
lean_ctor_set_uint8(v___x_5062_, sizeof(void*)*14, v_diag_5057_);
lean_ctor_set_uint8(v___x_5062_, sizeof(void*)*14 + 1, v_suppressElabErrors_5059_);
v___x_5063_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5039_, v___y_5040_, v___y_5041_, v___x_5062_, v___y_5043_);
lean_dec_ref_known(v___x_5062_, 14);
return v___x_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5064_, lean_object* v_msg_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_){
_start:
{
lean_object* v_res_5071_; 
v_res_5071_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5064_, v_msg_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v_ref_5064_);
return v_res_5071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5072_, lean_object* v_msg_5073_, lean_object* v_declHint_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_){
_start:
{
lean_object* v___x_5080_; lean_object* v_a_5081_; lean_object* v___x_5082_; 
v___x_5080_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5073_, v_declHint_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
v_a_5081_ = lean_ctor_get(v___x_5080_, 0);
lean_inc(v_a_5081_);
lean_dec_ref(v___x_5080_);
v___x_5082_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5072_, v_a_5081_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5083_, lean_object* v_msg_5084_, lean_object* v_declHint_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5083_, v_msg_5084_, v_declHint_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
lean_dec(v___y_5089_);
lean_dec_ref(v___y_5088_);
lean_dec(v___y_5087_);
lean_dec_ref(v___y_5086_);
lean_dec(v_ref_5083_);
return v_res_5091_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5094_ = l_Lean_stringToMessageData(v___x_5093_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5095_, lean_object* v_constName_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v___x_5102_; uint8_t v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5102_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5103_ = 0;
lean_inc(v_constName_5096_);
v___x_5104_ = l_Lean_MessageData_ofConstName(v_constName_5096_, v___x_5103_);
v___x_5105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5102_);
lean_ctor_set(v___x_5105_, 1, v___x_5104_);
v___x_5106_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5105_);
lean_ctor_set(v___x_5107_, 1, v___x_5106_);
v___x_5108_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5095_, v___x_5107_, v_constName_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5109_, lean_object* v_constName_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_){
_start:
{
lean_object* v_res_5116_; 
v_res_5116_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5109_, v_constName_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5111_);
lean_dec(v_ref_5109_);
return v_res_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v_ref_5123_; lean_object* v___x_5124_; 
v_ref_5123_ = lean_ctor_get(v___y_5120_, 5);
v___x_5124_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5123_, v_constName_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
lean_dec(v___y_5129_);
lean_dec_ref(v___y_5128_);
lean_dec(v___y_5127_);
lean_dec_ref(v___y_5126_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v___x_5138_; lean_object* v_env_5139_; uint8_t v___x_5140_; lean_object* v___x_5141_; 
v___x_5138_ = lean_st_ref_get(v___y_5136_);
v_env_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc_ref(v_env_5139_);
lean_dec(v___x_5138_);
v___x_5140_ = 0;
lean_inc(v_constName_5132_);
v___x_5141_ = l_Lean_Environment_find_x3f(v_env_5139_, v_constName_5132_, v___x_5140_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v___x_5142_; 
v___x_5142_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
return v___x_5142_;
}
else
{
lean_object* v_val_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec(v_constName_5132_);
v_val_5143_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5141_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_val_5143_);
lean_dec(v___x_5141_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
lean_ctor_set_tag(v___x_5145_, 0);
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_val_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5154_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5160_, lean_object* v_x_5161_, lean_object* v_x_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_){
_start:
{
if (lean_obj_tag(v_x_5160_) == 5)
{
lean_object* v_fn_5168_; lean_object* v_arg_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v_fn_5168_ = lean_ctor_get(v_x_5160_, 0);
lean_inc_ref(v_fn_5168_);
v_arg_5169_ = lean_ctor_get(v_x_5160_, 1);
lean_inc_ref(v_arg_5169_);
lean_dec_ref_known(v_x_5160_, 2);
v___x_5170_ = lean_array_set(v_x_5161_, v_x_5162_, v_arg_5169_);
v___x_5171_ = lean_unsigned_to_nat(1u);
v___x_5172_ = lean_nat_sub(v_x_5162_, v___x_5171_);
lean_dec(v_x_5162_);
v_x_5160_ = v_fn_5168_;
v_x_5161_ = v___x_5170_;
v_x_5162_ = v___x_5172_;
goto _start;
}
else
{
lean_dec(v_x_5162_);
if (lean_obj_tag(v_x_5160_) == 4)
{
lean_object* v_declName_5174_; lean_object* v___x_5175_; 
v_declName_5174_ = lean_ctor_get(v_x_5160_, 0);
lean_inc(v_declName_5174_);
lean_dec_ref_known(v_x_5160_, 2);
v___x_5175_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5174_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
if (lean_obj_tag(v___x_5175_) == 0)
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5207_; 
v_a_5176_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5178_ = v___x_5175_;
v_isShared_5179_ = v_isSharedCheck_5207_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v___x_5175_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5207_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v_lower_5181_; lean_object* v_upper_5182_; 
if (lean_obj_tag(v_a_5176_) == 5)
{
lean_object* v_val_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5204_; 
v_val_5190_ = lean_ctor_get(v_a_5176_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v_a_5176_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5192_ = v_a_5176_;
v_isShared_5193_ = v_isSharedCheck_5204_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_val_5190_);
lean_dec(v_a_5176_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5204_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v_numParams_5194_; lean_object* v_numIndices_5195_; lean_object* v___x_5196_; uint8_t v___x_5197_; 
v_numParams_5194_ = lean_ctor_get(v_val_5190_, 1);
lean_inc(v_numParams_5194_);
v_numIndices_5195_ = lean_ctor_get(v_val_5190_, 2);
lean_inc(v_numIndices_5195_);
lean_dec_ref(v_val_5190_);
v___x_5196_ = lean_unsigned_to_nat(0u);
v___x_5197_ = lean_nat_dec_eq(v_numIndices_5195_, v___x_5196_);
lean_dec(v_numIndices_5195_);
if (v___x_5197_ == 0)
{
lean_object* v___x_5198_; uint8_t v___x_5199_; 
lean_del_object(v___x_5192_);
v___x_5198_ = lean_array_get_size(v_x_5161_);
v___x_5199_ = lean_nat_dec_le(v_numParams_5194_, v___x_5196_);
if (v___x_5199_ == 0)
{
v_lower_5181_ = v_numParams_5194_;
v_upper_5182_ = v___x_5198_;
goto v___jp_5180_;
}
else
{
lean_dec(v_numParams_5194_);
v_lower_5181_ = v___x_5196_;
v_upper_5182_ = v___x_5198_;
goto v___jp_5180_;
}
}
else
{
lean_object* v___x_5200_; lean_object* v___x_5202_; 
lean_dec(v_numParams_5194_);
lean_del_object(v___x_5178_);
lean_dec_ref(v_x_5161_);
v___x_5200_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5193_ == 0)
{
lean_ctor_set_tag(v___x_5192_, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5200_);
v___x_5202_ = v___x_5192_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5200_);
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
lean_object* v___x_5205_; lean_object* v___x_5206_; 
lean_del_object(v___x_5178_);
lean_dec(v_a_5176_);
lean_dec_ref(v_x_5161_);
v___x_5205_ = lean_box(0);
v___x_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5206_, 0, v___x_5205_);
return v___x_5206_;
}
v___jp_5180_:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5188_; 
v___x_5183_ = l_Array_toSubarray___redArg(v_x_5161_, v_lower_5181_, v_upper_5182_);
v___x_5184_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5185_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5183_, v___x_5184_);
v___x_5186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5185_);
if (v_isShared_5179_ == 0)
{
lean_ctor_set(v___x_5178_, 0, v___x_5186_);
v___x_5188_ = v___x_5178_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v___x_5186_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
else
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5215_; 
lean_dec_ref(v_x_5161_);
v_a_5208_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_5175_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5175_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
return v___x_5213_;
}
}
}
}
else
{
lean_object* v___x_5216_; lean_object* v___x_5217_; 
lean_dec_ref(v_x_5161_);
lean_dec_ref(v_x_5160_);
v___x_5216_ = lean_box(0);
v___x_5217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5216_);
return v___x_5217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5218_, lean_object* v_x_5219_, lean_object* v_x_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5218_, v_x_5219_, v_x_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
lean_dec(v___y_5222_);
lean_dec_ref(v___y_5221_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_){
_start:
{
lean_object* v___x_5233_; 
lean_inc(v_a_5231_);
lean_inc_ref(v_a_5230_);
lean_inc(v_a_5229_);
lean_inc_ref(v_a_5228_);
v___x_5233_ = lean_infer_type(v_ctorApp_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_object* v_a_5234_; lean_object* v___x_5235_; 
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
lean_inc(v_a_5234_);
lean_dec_ref_known(v___x_5233_, 1);
v___x_5235_ = l_Lean_Meta_whnfD(v_a_5234_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_);
if (lean_obj_tag(v___x_5235_) == 0)
{
lean_object* v_a_5236_; lean_object* v_dummy_5237_; lean_object* v_nargs_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; 
v_a_5236_ = lean_ctor_get(v___x_5235_, 0);
lean_inc(v_a_5236_);
lean_dec_ref_known(v___x_5235_, 1);
v_dummy_5237_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5238_ = l_Lean_Expr_getAppNumArgs(v_a_5236_);
lean_inc(v_nargs_5238_);
v___x_5239_ = lean_mk_array(v_nargs_5238_, v_dummy_5237_);
v___x_5240_ = lean_unsigned_to_nat(1u);
v___x_5241_ = lean_nat_sub(v_nargs_5238_, v___x_5240_);
lean_dec(v_nargs_5238_);
v___x_5242_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5236_, v___x_5239_, v___x_5241_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_);
return v___x_5242_;
}
else
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5250_; 
v_a_5243_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5235_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5235_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5248_; 
if (v_isShared_5246_ == 0)
{
v___x_5248_ = v___x_5245_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_a_5243_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
}
else
{
lean_object* v_a_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5258_; 
v_a_5251_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5253_ = v___x_5233_;
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_a_5251_);
lean_dec(v___x_5233_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5256_; 
if (v_isShared_5254_ == 0)
{
v___x_5256_ = v___x_5253_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_a_5251_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5266_, lean_object* v_R_5267_, lean_object* v_a_5268_, lean_object* v_b_5269_){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5268_, v_b_5269_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5271_, lean_object* v_constName_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v___x_5278_; 
v___x_5278_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
return v___x_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5279_, lean_object* v_constName_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_){
_start:
{
lean_object* v_res_5286_; 
v_res_5286_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5279_, v_constName_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
return v_res_5286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5287_, lean_object* v_ref_5288_, lean_object* v_constName_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
lean_object* v___x_5295_; 
v___x_5295_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5288_, v_constName_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
return v___x_5295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5296_, lean_object* v_ref_5297_, lean_object* v_constName_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5296_, v_ref_5297_, v_constName_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
lean_dec(v___y_5300_);
lean_dec_ref(v___y_5299_);
lean_dec(v_ref_5297_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5305_, lean_object* v_ref_5306_, lean_object* v_msg_5307_, lean_object* v_declHint_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v___x_5314_; 
v___x_5314_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5306_, v_msg_5307_, v_declHint_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5315_, lean_object* v_ref_5316_, lean_object* v_msg_5317_, lean_object* v_declHint_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v_res_5324_; 
v_res_5324_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5315_, v_ref_5316_, v_msg_5317_, v_declHint_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec(v_ref_5316_);
return v_res_5324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5325_, lean_object* v_declHint_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v___x_5332_; 
v___x_5332_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5325_, v_declHint_5326_, v___y_5330_);
return v___x_5332_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5333_, lean_object* v_declHint_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5333_, v_declHint_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_);
lean_dec(v___y_5338_);
lean_dec_ref(v___y_5337_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5341_, lean_object* v_ref_5342_, lean_object* v_msg_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
lean_object* v___x_5349_; 
v___x_5349_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5342_, v_msg_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_);
return v___x_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5350_, lean_object* v_ref_5351_, lean_object* v_msg_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5350_, v_ref_5351_, v_msg_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_);
lean_dec(v___y_5356_);
lean_dec_ref(v___y_5355_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v_ref_5351_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5359_, lean_object* v_body_5360_, lean_object* v_args2_5361_, lean_object* v_ctorVal_5362_, lean_object* v_args1_5363_, lean_object* v_k_5364_, lean_object* v_arg2_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5359_, v_body_5360_, v_args2_5361_, v_ctorVal_5362_, v_args1_5363_, v_k_5364_, v_arg2_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_);
lean_dec(v___y_5369_);
lean_dec_ref(v___y_5368_);
lean_dec(v___y_5367_);
lean_dec_ref(v___y_5366_);
lean_dec_ref(v_body_5360_);
lean_dec(v_i_5359_);
return v_res_5371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5372_, lean_object* v_args1_5373_, lean_object* v_k_5374_, lean_object* v_i_5375_, lean_object* v_type_5376_, lean_object* v_args2_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_){
_start:
{
lean_object* v___x_5383_; uint8_t v___x_5384_; 
v___x_5383_ = lean_array_get_size(v_args1_5373_);
v___x_5384_ = lean_nat_dec_lt(v_i_5375_, v___x_5383_);
if (v___x_5384_ == 0)
{
lean_object* v___x_5385_; 
lean_dec_ref(v_type_5376_);
lean_dec(v_i_5375_);
lean_dec_ref(v_args1_5373_);
lean_dec_ref(v_ctorVal_5372_);
lean_inc(v_a_5381_);
lean_inc_ref(v_a_5380_);
lean_inc(v_a_5379_);
lean_inc_ref(v_a_5378_);
v___x_5385_ = lean_apply_6(v_k_5374_, v_args2_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_, lean_box(0));
return v___x_5385_;
}
else
{
lean_object* v___x_5386_; 
lean_inc(v_a_5381_);
lean_inc_ref(v_a_5380_);
lean_inc(v_a_5379_);
lean_inc_ref(v_a_5378_);
v___x_5386_ = lean_whnf(v_type_5376_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_object* v_a_5387_; 
v_a_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_a_5387_);
lean_dec_ref_known(v___x_5386_, 1);
if (lean_obj_tag(v_a_5387_) == 7)
{
lean_object* v_binderName_5388_; lean_object* v_binderType_5389_; lean_object* v_body_5390_; lean_object* v___f_5391_; uint8_t v___x_5392_; uint8_t v___x_5393_; lean_object* v___x_5394_; 
v_binderName_5388_ = lean_ctor_get(v_a_5387_, 0);
lean_inc(v_binderName_5388_);
v_binderType_5389_ = lean_ctor_get(v_a_5387_, 1);
lean_inc_ref(v_binderType_5389_);
v_body_5390_ = lean_ctor_get(v_a_5387_, 2);
lean_inc_ref(v_body_5390_);
lean_dec_ref_known(v_a_5387_, 3);
v___f_5391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5391_, 0, v_i_5375_);
lean_closure_set(v___f_5391_, 1, v_body_5390_);
lean_closure_set(v___f_5391_, 2, v_args2_5377_);
lean_closure_set(v___f_5391_, 3, v_ctorVal_5372_);
lean_closure_set(v___f_5391_, 4, v_args1_5373_);
lean_closure_set(v___f_5391_, 5, v_k_5374_);
v___x_5392_ = 1;
v___x_5393_ = 0;
v___x_5394_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5388_, v___x_5392_, v_binderType_5389_, v___f_5391_, v___x_5393_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_);
return v___x_5394_;
}
else
{
lean_object* v_toConstantVal_5395_; lean_object* v_name_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
lean_dec(v_a_5387_);
lean_dec_ref(v_args2_5377_);
lean_dec(v_i_5375_);
lean_dec_ref(v_k_5374_);
lean_dec_ref(v_args1_5373_);
v_toConstantVal_5395_ = lean_ctor_get(v_ctorVal_5372_, 0);
lean_inc_ref(v_toConstantVal_5395_);
lean_dec_ref(v_ctorVal_5372_);
v_name_5396_ = lean_ctor_get(v_toConstantVal_5395_, 0);
lean_inc(v_name_5396_);
lean_dec_ref(v_toConstantVal_5395_);
v___x_5397_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5398_ = l_Lean_MessageData_ofName(v_name_5396_);
v___x_5399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5399_, 0, v___x_5397_);
lean_ctor_set(v___x_5399_, 1, v___x_5398_);
v___x_5400_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5401_, 0, v___x_5399_);
lean_ctor_set(v___x_5401_, 1, v___x_5400_);
v___x_5402_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5401_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_);
return v___x_5402_;
}
}
else
{
lean_object* v_a_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5410_; 
lean_dec_ref(v_args2_5377_);
lean_dec(v_i_5375_);
lean_dec_ref(v_k_5374_);
lean_dec_ref(v_args1_5373_);
lean_dec_ref(v_ctorVal_5372_);
v_a_5403_ = lean_ctor_get(v___x_5386_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5386_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5386_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5408_; 
if (v_isShared_5406_ == 0)
{
v___x_5408_ = v___x_5405_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5411_, lean_object* v_body_5412_, lean_object* v_args2_5413_, lean_object* v_ctorVal_5414_, lean_object* v_args1_5415_, lean_object* v_k_5416_, lean_object* v_arg2_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; 
v___x_5423_ = lean_unsigned_to_nat(1u);
v___x_5424_ = lean_nat_add(v_i_5411_, v___x_5423_);
v___x_5425_ = lean_expr_instantiate1(v_body_5412_, v_arg2_5417_);
v___x_5426_ = lean_array_push(v_args2_5413_, v_arg2_5417_);
v___x_5427_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5414_, v_args1_5415_, v_k_5416_, v___x_5424_, v___x_5425_, v___x_5426_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_);
return v___x_5427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5428_, lean_object* v_args1_5429_, lean_object* v_k_5430_, lean_object* v_i_5431_, lean_object* v_type_5432_, lean_object* v_args2_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5428_, v_args1_5429_, v_k_5430_, v_i_5431_, v_type_5432_, v_args2_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_);
lean_dec(v_a_5437_);
lean_dec_ref(v_a_5436_);
lean_dec(v_a_5435_);
lean_dec_ref(v_a_5434_);
return v_res_5439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5440_, lean_object* v_us_5441_, lean_object* v_args1_5442_, lean_object* v___x_5443_, lean_object* v_numParams_5444_, lean_object* v___x_5445_, lean_object* v_args2_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
lean_inc(v_us_5441_);
v___x_5452_ = l_Lean_mkConst(v_name_5440_, v_us_5441_);
lean_inc_ref(v___x_5452_);
v___x_5453_ = l_Lean_mkAppN(v___x_5452_, v_args1_5442_);
v___x_5454_ = l_Lean_mkAppN(v___x_5452_, v_args2_5446_);
lean_inc_ref(v___x_5454_);
lean_inc_ref(v___x_5453_);
v___x_5455_ = l_Lean_Meta_mkEqHEq(v___x_5453_, v___x_5454_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_object* v_a_5456_; lean_object* v___x_5457_; uint8_t v___x_5458_; lean_object* v___x_5459_; 
v_a_5456_ = lean_ctor_get(v___x_5455_, 0);
lean_inc(v_a_5456_);
lean_dec_ref_known(v___x_5455_, 1);
lean_inc_ref_n(v_args2_5446_, 2);
v___x_5457_ = l_Array_toSubarray___redArg(v_args2_5446_, v___x_5443_, v_numParams_5444_);
v___x_5458_ = 1;
v___x_5459_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5442_, v_args2_5446_, v___x_5458_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5580_; 
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5462_ = v___x_5459_;
v_isShared_5463_ = v_isSharedCheck_5580_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5459_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5580_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v___x_5464_; 
v___x_5464_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5460_);
if (lean_obj_tag(v___x_5464_) == 1)
{
lean_object* v_val_5465_; lean_object* v___x_5466_; 
lean_del_object(v___x_5462_);
v_val_5465_ = lean_ctor_get(v___x_5464_, 0);
lean_inc(v_val_5465_);
lean_dec_ref_known(v___x_5464_, 1);
v___x_5466_ = l_Lean_mkArrow(v_a_5456_, v_val_5465_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v_a_5467_; lean_object* v___x_5468_; 
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
lean_inc(v_a_5467_);
lean_dec_ref_known(v___x_5466_, 1);
v___x_5468_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5453_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5468_) == 0)
{
lean_object* v_a_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5559_; 
v_a_5469_ = lean_ctor_get(v___x_5468_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5468_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5471_ = v___x_5468_;
v_isShared_5472_ = v_isSharedCheck_5559_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_a_5469_);
lean_dec(v___x_5468_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5559_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
if (lean_obj_tag(v_a_5469_) == 1)
{
lean_object* v_val_5473_; lean_object* v___x_5474_; 
lean_del_object(v___x_5471_);
v_val_5473_ = lean_ctor_get(v_a_5469_, 0);
lean_inc(v_val_5473_);
lean_dec_ref_known(v_a_5469_, 1);
v___x_5474_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5454_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5546_; 
v_a_5475_ = lean_ctor_get(v___x_5474_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5477_ = v___x_5474_;
v_isShared_5478_ = v_isSharedCheck_5546_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5474_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5546_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
if (lean_obj_tag(v_a_5475_) == 1)
{
lean_object* v_val_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5541_; 
lean_del_object(v___x_5477_);
v_val_5479_ = lean_ctor_get(v_a_5475_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v_a_5475_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5481_ = v_a_5475_;
v_isShared_5482_ = v_isSharedCheck_5541_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_val_5479_);
lean_dec(v_a_5475_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5541_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; uint8_t v___x_5487_; lean_object* v___x_5488_; 
v___x_5483_ = l_Subarray_copy___redArg(v___x_5445_);
v___x_5484_ = l_Array_append___redArg(v___x_5483_, v_val_5473_);
v___x_5485_ = l_Subarray_copy___redArg(v___x_5457_);
v___x_5486_ = l_Array_append___redArg(v___x_5485_, v_val_5479_);
lean_dec(v_val_5479_);
v___x_5487_ = 0;
v___x_5488_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5484_, v___x_5486_, v___x_5487_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
lean_dec_ref(v___x_5484_);
if (lean_obj_tag(v___x_5488_) == 0)
{
lean_object* v_a_5489_; lean_object* v___x_5490_; 
v_a_5489_ = lean_ctor_get(v___x_5488_, 0);
lean_inc(v_a_5489_);
lean_dec_ref_known(v___x_5488_, 1);
v___x_5490_ = l_Lean_mkArrowN(v_a_5489_, v_a_5467_, v___y_5449_, v___y_5450_);
lean_dec(v_a_5489_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; uint8_t v___x_5492_; lean_object* v___x_5493_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref_known(v___x_5490_, 1);
v___x_5492_ = 1;
v___x_5493_ = l_Lean_Meta_mkForallFVars(v_args2_5446_, v_a_5491_, v___x_5487_, v___x_5458_, v___x_5458_, v___x_5492_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
lean_dec_ref(v_args2_5446_);
if (lean_obj_tag(v___x_5493_) == 0)
{
lean_object* v_a_5494_; lean_object* v___x_5495_; 
v_a_5494_ = lean_ctor_get(v___x_5493_, 0);
lean_inc(v_a_5494_);
lean_dec_ref_known(v___x_5493_, 1);
v___x_5495_ = l_Lean_Meta_mkForallFVars(v_args1_5442_, v_a_5494_, v___x_5487_, v___x_5458_, v___x_5458_, v___x_5492_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5508_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5508_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5508_ == 0)
{
v___x_5498_ = v___x_5495_;
v_isShared_5499_ = v_isSharedCheck_5508_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_a_5496_);
lean_dec(v___x_5495_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5508_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5503_; 
v___x_5500_ = lean_array_get_size(v_val_5473_);
lean_dec(v_val_5473_);
v___x_5501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5501_, 0, v_a_5496_);
lean_ctor_set(v___x_5501_, 1, v_us_5441_);
lean_ctor_set(v___x_5501_, 2, v___x_5500_);
if (v_isShared_5482_ == 0)
{
lean_ctor_set(v___x_5481_, 0, v___x_5501_);
v___x_5503_ = v___x_5481_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5507_; 
v_reuseFailAlloc_5507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5507_, 0, v___x_5501_);
v___x_5503_ = v_reuseFailAlloc_5507_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
lean_object* v___x_5505_; 
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 0, v___x_5503_);
v___x_5505_ = v___x_5498_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5503_);
v___x_5505_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
return v___x_5505_;
}
}
}
}
else
{
lean_object* v_a_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5516_; 
lean_del_object(v___x_5481_);
lean_dec(v_val_5473_);
lean_dec(v_us_5441_);
v_a_5509_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5511_ = v___x_5495_;
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_a_5509_);
lean_dec(v___x_5495_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v___x_5514_; 
if (v_isShared_5512_ == 0)
{
v___x_5514_ = v___x_5511_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_a_5509_);
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
lean_del_object(v___x_5481_);
lean_dec(v_val_5473_);
lean_dec(v_us_5441_);
v_a_5517_ = lean_ctor_get(v___x_5493_, 0);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5524_ == 0)
{
v___x_5519_ = v___x_5493_;
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_a_5517_);
lean_dec(v___x_5493_);
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
lean_object* v_a_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5532_; 
lean_del_object(v___x_5481_);
lean_dec(v_val_5473_);
lean_dec_ref(v_args2_5446_);
lean_dec(v_us_5441_);
v_a_5525_ = lean_ctor_get(v___x_5490_, 0);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5527_ = v___x_5490_;
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_a_5525_);
lean_dec(v___x_5490_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5530_; 
if (v_isShared_5528_ == 0)
{
v___x_5530_ = v___x_5527_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_a_5525_);
v___x_5530_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
return v___x_5530_;
}
}
}
}
else
{
lean_object* v_a_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5540_; 
lean_del_object(v___x_5481_);
lean_dec(v_val_5473_);
lean_dec(v_a_5467_);
lean_dec_ref(v_args2_5446_);
lean_dec(v_us_5441_);
v_a_5533_ = lean_ctor_get(v___x_5488_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v___x_5488_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5535_ = v___x_5488_;
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_a_5533_);
lean_dec(v___x_5488_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5538_; 
if (v_isShared_5536_ == 0)
{
v___x_5538_ = v___x_5535_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_a_5533_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
return v___x_5538_;
}
}
}
}
}
else
{
lean_object* v___x_5542_; lean_object* v___x_5544_; 
lean_dec(v_a_5475_);
lean_dec(v_val_5473_);
lean_dec(v_a_5467_);
lean_dec_ref(v___x_5457_);
lean_dec_ref(v_args2_5446_);
lean_dec_ref(v___x_5445_);
lean_dec(v_us_5441_);
v___x_5542_ = lean_box(0);
if (v_isShared_5478_ == 0)
{
lean_ctor_set(v___x_5477_, 0, v___x_5542_);
v___x_5544_ = v___x_5477_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v___x_5542_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
else
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5554_; 
lean_dec(v_val_5473_);
lean_dec(v_a_5467_);
lean_dec_ref(v___x_5457_);
lean_dec_ref(v_args2_5446_);
lean_dec_ref(v___x_5445_);
lean_dec(v_us_5441_);
v_a_5547_ = lean_ctor_get(v___x_5474_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5549_ = v___x_5474_;
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5474_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5552_; 
if (v_isShared_5550_ == 0)
{
v___x_5552_ = v___x_5549_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
else
{
lean_object* v___x_5555_; lean_object* v___x_5557_; 
lean_dec(v_a_5469_);
lean_dec(v_a_5467_);
lean_dec_ref(v___x_5457_);
lean_dec_ref(v___x_5454_);
lean_dec_ref(v_args2_5446_);
lean_dec_ref(v___x_5445_);
lean_dec(v_us_5441_);
v___x_5555_ = lean_box(0);
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 0, v___x_5555_);
v___x_5557_ = v___x_5471_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v___x_5555_);
v___x_5557_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
return v___x_5557_;
}
}
}
}
else
{
lean_object* v_a_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5567_; 
lean_dec(v_a_5467_);
lean_dec_ref(v___x_5457_);
lean_dec_ref(v___x_5454_);
lean_dec_ref(v_args2_5446_);
lean_dec_ref(v___x_5445_);
lean_dec(v_us_5441_);
v_a_5560_ = lean_ctor_get(v___x_5468_, 0);
v_isSharedCheck_5567_ = !lean_is_exclusive(v___x_5468_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5562_ = v___x_5468_;
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_a_5560_);
lean_dec(v___x_5468_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5565_; 
if (v_isShared_5563_ == 0)
{
v___x_5565_ = v___x_5562_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_a_5560_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
return v___x_5565_;
}
}
}
}
else
{
lean_object* v_a_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5575_; 
lean_dec_ref(v___x_5457_);
lean_dec_ref(v___x_5454_);
lean_dec_ref(v___x_5453_);
lean_dec_ref(v_args2_5446_);
lean_dec_ref(v___x_5445_);
lean_dec(v_us_5441_);
v_a_5568_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5575_ == 0)
{
v___x_5570_ = v___x_5466_;
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_a_5568_);
lean_dec(v___x_5466_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5573_; 
if (v_isShared_5571_ == 0)
{
v___x_5573_ = v___x_5570_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
v___x_5573_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
return v___x_5573_;
}
}
}
}
else
{
lean_object* v___x_5576_; lean_object* v___x_5578_; 
lean_dec(v___x_5464_);
lean_dec_ref(v___x_5457_);
lean_dec(v_a_5456_);
lean_dec_ref(v___x_5454_);
lean_dec_ref(v___x_5453_);
lean_dec_ref(v_args2_5446_);
lean_dec_ref(v___x_5445_);
lean_dec(v_us_5441_);
v___x_5576_ = lean_box(0);
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 0, v___x_5576_);
v___x_5578_ = v___x_5462_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5576_);
v___x_5578_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
return v___x_5578_;
}
}
}
}
else
{
lean_object* v_a_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5588_; 
lean_dec_ref(v___x_5457_);
lean_dec(v_a_5456_);
lean_dec_ref(v___x_5454_);
lean_dec_ref(v___x_5453_);
lean_dec_ref(v_args2_5446_);
lean_dec_ref(v___x_5445_);
lean_dec(v_us_5441_);
v_a_5581_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5583_ = v___x_5459_;
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5459_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5586_; 
if (v_isShared_5584_ == 0)
{
v___x_5586_ = v___x_5583_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
return v___x_5586_;
}
}
}
}
else
{
lean_object* v_a_5589_; lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5596_; 
lean_dec_ref(v___x_5454_);
lean_dec_ref(v___x_5453_);
lean_dec_ref(v_args2_5446_);
lean_dec_ref(v___x_5445_);
lean_dec(v_numParams_5444_);
lean_dec(v___x_5443_);
lean_dec(v_us_5441_);
v_a_5589_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5596_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5596_ == 0)
{
v___x_5591_ = v___x_5455_;
v_isShared_5592_ = v_isSharedCheck_5596_;
goto v_resetjp_5590_;
}
else
{
lean_inc(v_a_5589_);
lean_dec(v___x_5455_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5596_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v___x_5594_; 
if (v_isShared_5592_ == 0)
{
v___x_5594_ = v___x_5591_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_a_5589_);
v___x_5594_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
return v___x_5594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5597_, lean_object* v_us_5598_, lean_object* v_args1_5599_, lean_object* v___x_5600_, lean_object* v_numParams_5601_, lean_object* v___x_5602_, lean_object* v_args2_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_){
_start:
{
lean_object* v_res_5609_; 
v_res_5609_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5597_, v_us_5598_, v_args1_5599_, v___x_5600_, v_numParams_5601_, v___x_5602_, v_args2_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_);
lean_dec(v___y_5607_);
lean_dec_ref(v___y_5606_);
lean_dec(v___y_5605_);
lean_dec_ref(v___y_5604_);
lean_dec_ref(v_args1_5599_);
return v_res_5609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5610_, lean_object* v_name_5611_, lean_object* v_us_5612_, lean_object* v_ctorVal_5613_, lean_object* v_a_5614_, lean_object* v_args1_5615_, lean_object* v_x_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_){
_start:
{
lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___f_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
v___x_5622_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5610_);
lean_inc_ref_n(v_args1_5615_, 3);
v___x_5623_ = l_Array_toSubarray___redArg(v_args1_5615_, v___x_5622_, v_numParams_5610_);
v___f_5624_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5624_, 0, v_name_5611_);
lean_closure_set(v___f_5624_, 1, v_us_5612_);
lean_closure_set(v___f_5624_, 2, v_args1_5615_);
lean_closure_set(v___f_5624_, 3, v___x_5622_);
lean_closure_set(v___f_5624_, 4, v_numParams_5610_);
lean_closure_set(v___f_5624_, 5, v___x_5623_);
v___x_5625_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5626_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5626_, 0, v_ctorVal_5613_);
lean_closure_set(v___x_5626_, 1, v_args1_5615_);
lean_closure_set(v___x_5626_, 2, v___f_5624_);
lean_closure_set(v___x_5626_, 3, v___x_5622_);
lean_closure_set(v___x_5626_, 4, v_a_5614_);
lean_closure_set(v___x_5626_, 5, v___x_5625_);
v___x_5627_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5615_, v___x_5626_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_);
return v___x_5627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5628_, lean_object* v_name_5629_, lean_object* v_us_5630_, lean_object* v_ctorVal_5631_, lean_object* v_a_5632_, lean_object* v_args1_5633_, lean_object* v_x_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_){
_start:
{
lean_object* v_res_5640_; 
v_res_5640_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5628_, v_name_5629_, v_us_5630_, v_ctorVal_5631_, v_a_5632_, v_args1_5633_, v_x_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
lean_dec(v___y_5636_);
lean_dec_ref(v___y_5635_);
lean_dec_ref(v_x_5634_);
return v_res_5640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_){
_start:
{
lean_object* v_toConstantVal_5647_; lean_object* v_numParams_5648_; lean_object* v_name_5649_; lean_object* v_levelParams_5650_; lean_object* v_type_5651_; lean_object* v___x_5652_; 
v_toConstantVal_5647_ = lean_ctor_get(v_ctorVal_5641_, 0);
v_numParams_5648_ = lean_ctor_get(v_ctorVal_5641_, 3);
lean_inc(v_numParams_5648_);
v_name_5649_ = lean_ctor_get(v_toConstantVal_5647_, 0);
lean_inc(v_name_5649_);
v_levelParams_5650_ = lean_ctor_get(v_toConstantVal_5647_, 1);
v_type_5651_ = lean_ctor_get(v_toConstantVal_5647_, 2);
lean_inc_ref(v_type_5651_);
v___x_5652_ = l_Lean_Meta_elimOptParam(v_type_5651_, v_a_5644_, v_a_5645_);
if (lean_obj_tag(v___x_5652_) == 0)
{
lean_object* v_a_5653_; lean_object* v___x_5654_; lean_object* v_us_5655_; lean_object* v___f_5656_; uint8_t v___x_5657_; lean_object* v___x_5658_; 
v_a_5653_ = lean_ctor_get(v___x_5652_, 0);
lean_inc_n(v_a_5653_, 2);
lean_dec_ref_known(v___x_5652_, 1);
v___x_5654_ = lean_box(0);
lean_inc(v_levelParams_5650_);
v_us_5655_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5650_, v___x_5654_);
v___f_5656_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5656_, 0, v_numParams_5648_);
lean_closure_set(v___f_5656_, 1, v_name_5649_);
lean_closure_set(v___f_5656_, 2, v_us_5655_);
lean_closure_set(v___f_5656_, 3, v_ctorVal_5641_);
lean_closure_set(v___f_5656_, 4, v_a_5653_);
v___x_5657_ = 0;
v___x_5658_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5653_, v___f_5656_, v___x_5657_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_);
return v___x_5658_;
}
else
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5666_; 
lean_dec(v_name_5649_);
lean_dec(v_numParams_5648_);
lean_dec_ref(v_ctorVal_5641_);
v_a_5659_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5661_ = v___x_5652_;
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5652_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5662_ == 0)
{
v___x_5664_ = v___x_5661_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
v___x_5664_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
return v___x_5664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_){
_start:
{
lean_object* v_res_5673_; 
v_res_5673_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5667_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_);
lean_dec(v_a_5671_);
lean_dec_ref(v_a_5670_);
lean_dec(v_a_5669_);
lean_dec_ref(v_a_5668_);
return v_res_5673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5675_; lean_object* v___x_5676_; 
v___x_5675_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5676_ = l_Lean_stringToMessageData(v___x_5675_);
return v___x_5676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_){
_start:
{
lean_object* v_toConstantVal_5683_; lean_object* v_name_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; 
v_toConstantVal_5683_ = lean_ctor_get(v_ctorVal_5677_, 0);
lean_inc_ref(v_toConstantVal_5683_);
lean_dec_ref(v_ctorVal_5677_);
v_name_5684_ = lean_ctor_get(v_toConstantVal_5683_, 0);
lean_inc(v_name_5684_);
lean_dec_ref(v_toConstantVal_5683_);
v___x_5685_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5686_ = l_Lean_MessageData_ofName(v_name_5684_);
v___x_5687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5685_);
lean_ctor_set(v___x_5687_, 1, v___x_5686_);
v___x_5688_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5687_);
lean_ctor_set(v___x_5689_, 1, v___x_5688_);
v___x_5690_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5689_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_);
return v___x_5690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_){
_start:
{
lean_object* v_res_5697_; 
v_res_5697_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_);
lean_dec(v_a_5695_);
lean_dec_ref(v_a_5694_);
lean_dec(v_a_5693_);
lean_dec_ref(v_a_5692_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5698_, lean_object* v_ctorVal_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_){
_start:
{
lean_object* v___x_5705_; 
v___x_5705_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_);
return v___x_5705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5706_, lean_object* v_ctorVal_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_){
_start:
{
lean_object* v_res_5713_; 
v_res_5713_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5706_, v_ctorVal_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_);
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5719_, size_t v_sz_5720_, size_t v_i_5721_, lean_object* v_bs_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
uint8_t v___x_5728_; 
v___x_5728_ = lean_usize_dec_lt(v_i_5721_, v_sz_5720_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5729_; 
lean_dec_ref(v_ctorVal_5719_);
v___x_5729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5729_, 0, v_bs_5722_);
return v___x_5729_;
}
else
{
lean_object* v_v_5730_; lean_object* v___x_5731_; 
v_v_5730_ = lean_array_uget_borrowed(v_bs_5722_, v_i_5721_);
lean_inc(v___y_5726_);
lean_inc_ref(v___y_5725_);
lean_inc(v___y_5724_);
lean_inc_ref(v___y_5723_);
lean_inc(v_v_5730_);
v___x_5731_ = lean_infer_type(v_v_5730_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
if (lean_obj_tag(v___x_5731_) == 0)
{
lean_object* v_a_5732_; lean_object* v___x_5733_; 
v_a_5732_ = lean_ctor_get(v___x_5731_, 0);
lean_inc(v_a_5732_);
lean_dec_ref_known(v___x_5731_, 1);
v___x_5733_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5732_, v___y_5724_);
if (lean_obj_tag(v___x_5733_) == 0)
{
lean_object* v_a_5734_; lean_object* v___x_5735_; lean_object* v_bs_x27_5736_; lean_object* v_a_5738_; lean_object* v___y_5744_; lean_object* v_lhs_5755_; lean_object* v_rhs_5756_; lean_object* v___x_5758_; uint8_t v___x_5759_; 
v_a_5734_ = lean_ctor_get(v___x_5733_, 0);
lean_inc(v_a_5734_);
lean_dec_ref_known(v___x_5733_, 1);
v___x_5735_ = lean_unsigned_to_nat(0u);
v_bs_x27_5736_ = lean_array_uset(v_bs_5722_, v_i_5721_, v___x_5735_);
v___x_5758_ = l_Lean_Expr_cleanupAnnotations(v_a_5734_);
v___x_5759_ = l_Lean_Expr_isApp(v___x_5758_);
if (v___x_5759_ == 0)
{
lean_object* v___x_5760_; 
lean_dec_ref(v___x_5758_);
lean_inc_ref(v_ctorVal_5719_);
v___x_5760_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5719_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
v___y_5744_ = v___x_5760_;
goto v___jp_5743_;
}
else
{
lean_object* v_arg_5761_; lean_object* v___x_5762_; uint8_t v___x_5763_; 
v_arg_5761_ = lean_ctor_get(v___x_5758_, 1);
lean_inc_ref(v_arg_5761_);
v___x_5762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5758_);
v___x_5763_ = l_Lean_Expr_isApp(v___x_5762_);
if (v___x_5763_ == 0)
{
lean_object* v___x_5764_; 
lean_dec_ref(v___x_5762_);
lean_dec_ref(v_arg_5761_);
lean_inc_ref(v_ctorVal_5719_);
v___x_5764_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5719_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
v___y_5744_ = v___x_5764_;
goto v___jp_5743_;
}
else
{
lean_object* v_arg_5765_; lean_object* v___x_5766_; uint8_t v___x_5767_; 
v_arg_5765_ = lean_ctor_get(v___x_5762_, 1);
lean_inc_ref(v_arg_5765_);
v___x_5766_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5762_);
v___x_5767_ = l_Lean_Expr_isApp(v___x_5766_);
if (v___x_5767_ == 0)
{
lean_object* v___x_5768_; 
lean_dec_ref(v___x_5766_);
lean_dec_ref(v_arg_5765_);
lean_dec_ref(v_arg_5761_);
lean_inc_ref(v_ctorVal_5719_);
v___x_5768_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5719_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
v___y_5744_ = v___x_5768_;
goto v___jp_5743_;
}
else
{
lean_object* v_arg_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; uint8_t v___x_5772_; 
v_arg_5769_ = lean_ctor_get(v___x_5766_, 1);
lean_inc_ref(v_arg_5769_);
v___x_5770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5766_);
v___x_5771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5772_ = l_Lean_Expr_isConstOf(v___x_5770_, v___x_5771_);
if (v___x_5772_ == 0)
{
uint8_t v___x_5773_; 
lean_dec_ref(v_arg_5765_);
v___x_5773_ = l_Lean_Expr_isApp(v___x_5770_);
if (v___x_5773_ == 0)
{
lean_object* v___x_5774_; 
lean_dec_ref(v___x_5770_);
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5761_);
lean_inc_ref(v_ctorVal_5719_);
v___x_5774_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5719_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
v___y_5744_ = v___x_5774_;
goto v___jp_5743_;
}
else
{
lean_object* v___x_5775_; lean_object* v___x_5776_; uint8_t v___x_5777_; 
v___x_5775_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5770_);
v___x_5776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5777_ = l_Lean_Expr_isConstOf(v___x_5775_, v___x_5776_);
lean_dec_ref(v___x_5775_);
if (v___x_5777_ == 0)
{
lean_object* v___x_5778_; 
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5761_);
lean_inc_ref(v_ctorVal_5719_);
v___x_5778_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5719_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
v___y_5744_ = v___x_5778_;
goto v___jp_5743_;
}
else
{
v_lhs_5755_ = v_arg_5769_;
v_rhs_5756_ = v_arg_5761_;
goto v___jp_5754_;
}
}
}
else
{
lean_dec_ref(v___x_5770_);
lean_dec_ref(v_arg_5769_);
v_lhs_5755_ = v_arg_5765_;
v_rhs_5756_ = v_arg_5761_;
goto v___jp_5754_;
}
}
}
}
v___jp_5737_:
{
size_t v___x_5739_; size_t v___x_5740_; lean_object* v___x_5741_; 
v___x_5739_ = ((size_t)1ULL);
v___x_5740_ = lean_usize_add(v_i_5721_, v___x_5739_);
v___x_5741_ = lean_array_uset(v_bs_x27_5736_, v_i_5721_, v_a_5738_);
v_i_5721_ = v___x_5740_;
v_bs_5722_ = v___x_5741_;
goto _start;
}
v___jp_5743_:
{
if (lean_obj_tag(v___y_5744_) == 0)
{
lean_object* v_a_5745_; 
v_a_5745_ = lean_ctor_get(v___y_5744_, 0);
lean_inc(v_a_5745_);
lean_dec_ref_known(v___y_5744_, 1);
v_a_5738_ = v_a_5745_;
goto v___jp_5737_;
}
else
{
lean_object* v_a_5746_; lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5753_; 
lean_dec_ref(v_bs_x27_5736_);
lean_dec_ref(v_ctorVal_5719_);
v_a_5746_ = lean_ctor_get(v___y_5744_, 0);
v_isSharedCheck_5753_ = !lean_is_exclusive(v___y_5744_);
if (v_isSharedCheck_5753_ == 0)
{
v___x_5748_ = v___y_5744_;
v_isShared_5749_ = v_isSharedCheck_5753_;
goto v_resetjp_5747_;
}
else
{
lean_inc(v_a_5746_);
lean_dec(v___y_5744_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5753_;
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
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_a_5746_);
v___x_5751_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
return v___x_5751_;
}
}
}
}
v___jp_5754_:
{
lean_object* v___x_5757_; 
v___x_5757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5757_, 0, v_lhs_5755_);
lean_ctor_set(v___x_5757_, 1, v_rhs_5756_);
v_a_5738_ = v___x_5757_;
goto v___jp_5737_;
}
}
else
{
lean_object* v_a_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5786_; 
lean_dec_ref(v_bs_5722_);
lean_dec_ref(v_ctorVal_5719_);
v_a_5779_ = lean_ctor_get(v___x_5733_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v___x_5733_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5781_ = v___x_5733_;
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_a_5779_);
lean_dec(v___x_5733_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5786_;
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
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v_a_5779_);
v___x_5784_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
return v___x_5784_;
}
}
}
}
else
{
lean_object* v_a_5787_; lean_object* v___x_5789_; uint8_t v_isShared_5790_; uint8_t v_isSharedCheck_5794_; 
lean_dec_ref(v_bs_5722_);
lean_dec_ref(v_ctorVal_5719_);
v_a_5787_ = lean_ctor_get(v___x_5731_, 0);
v_isSharedCheck_5794_ = !lean_is_exclusive(v___x_5731_);
if (v_isSharedCheck_5794_ == 0)
{
v___x_5789_ = v___x_5731_;
v_isShared_5790_ = v_isSharedCheck_5794_;
goto v_resetjp_5788_;
}
else
{
lean_inc(v_a_5787_);
lean_dec(v___x_5731_);
v___x_5789_ = lean_box(0);
v_isShared_5790_ = v_isSharedCheck_5794_;
goto v_resetjp_5788_;
}
v_resetjp_5788_:
{
lean_object* v___x_5792_; 
if (v_isShared_5790_ == 0)
{
v___x_5792_ = v___x_5789_;
goto v_reusejp_5791_;
}
else
{
lean_object* v_reuseFailAlloc_5793_; 
v_reuseFailAlloc_5793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5793_, 0, v_a_5787_);
v___x_5792_ = v_reuseFailAlloc_5793_;
goto v_reusejp_5791_;
}
v_reusejp_5791_:
{
return v___x_5792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5795_, lean_object* v_sz_5796_, lean_object* v_i_5797_, lean_object* v_bs_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_){
_start:
{
size_t v_sz_boxed_5804_; size_t v_i_boxed_5805_; lean_object* v_res_5806_; 
v_sz_boxed_5804_ = lean_unbox_usize(v_sz_5796_);
lean_dec(v_sz_5796_);
v_i_boxed_5805_ = lean_unbox_usize(v_i_5797_);
lean_dec(v_i_5797_);
v_res_5806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5795_, v_sz_boxed_5804_, v_i_boxed_5805_, v_bs_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
lean_dec(v___y_5802_);
lean_dec_ref(v___y_5801_);
lean_dec(v___y_5800_);
lean_dec_ref(v___y_5799_);
return v_res_5806_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___x_5808_ = lean_unsigned_to_nat(0u);
v___x_5809_ = l_Lean_Level_ofNat(v___x_5808_);
return v___x_5809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5810_, lean_object* v_us_5811_, lean_object* v_numIndices_5812_, lean_object* v_xs_5813_, lean_object* v_type_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_){
_start:
{
lean_object* v_toConstantVal_5820_; lean_object* v_induct_5821_; lean_object* v_numParams_5822_; lean_object* v___x_5823_; lean_object* v_noConfusionName_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v_noConfusion_5828_; lean_object* v_noConfusion_5829_; lean_object* v_lower_5831_; lean_object* v_upper_5832_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v_n_5943_; uint8_t v___x_5944_; 
v_toConstantVal_5820_ = lean_ctor_get(v_ctorVal_5810_, 0);
v_induct_5821_ = lean_ctor_get(v_ctorVal_5810_, 1);
v_numParams_5822_ = lean_ctor_get(v_ctorVal_5810_, 3);
v___x_5823_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5821_);
v_noConfusionName_5824_ = l_Lean_Name_str___override(v_induct_5821_, v___x_5823_);
v___x_5825_ = lean_unsigned_to_nat(0u);
v___x_5826_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5827_, 0, v___x_5826_);
lean_ctor_set(v___x_5827_, 1, v_us_5811_);
v_noConfusion_5828_ = l_Lean_mkConst(v_noConfusionName_5824_, v___x_5827_);
v_noConfusion_5829_ = l_Lean_Expr_app___override(v_noConfusion_5828_, v_type_5814_);
v___x_5939_ = lean_array_get_size(v_xs_5813_);
v___x_5940_ = lean_nat_sub(v___x_5939_, v_numParams_5822_);
v___x_5941_ = lean_nat_sub(v___x_5940_, v_numIndices_5812_);
lean_dec(v___x_5940_);
v___x_5942_ = lean_unsigned_to_nat(1u);
v_n_5943_ = lean_nat_sub(v___x_5941_, v___x_5942_);
lean_dec(v___x_5941_);
v___x_5944_ = lean_nat_dec_le(v_n_5943_, v___x_5825_);
if (v___x_5944_ == 0)
{
v_lower_5831_ = v_n_5943_;
v_upper_5832_ = v___x_5939_;
goto v___jp_5830_;
}
else
{
lean_dec(v_n_5943_);
v_lower_5831_ = v___x_5825_;
v_upper_5832_ = v___x_5939_;
goto v___jp_5830_;
}
v___jp_5830_:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v_eqs_5835_; size_t v_sz_5836_; size_t v___x_5837_; lean_object* v___x_5838_; 
lean_inc_ref(v_xs_5813_);
v___x_5833_ = l_Array_toSubarray___redArg(v_xs_5813_, v_lower_5831_, v_upper_5832_);
v___x_5834_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5835_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5833_, v___x_5834_);
v_sz_5836_ = lean_array_size(v_eqs_5835_);
v___x_5837_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5835_);
lean_inc_ref(v_ctorVal_5810_);
v___x_5838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5810_, v_sz_5836_, v___x_5837_, v_eqs_5835_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
if (lean_obj_tag(v___x_5838_) == 0)
{
lean_object* v_a_5839_; lean_object* v___x_5840_; lean_object* v_fst_5841_; lean_object* v_snd_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; 
v_a_5839_ = lean_ctor_get(v___x_5838_, 0);
lean_inc(v_a_5839_);
lean_dec_ref_known(v___x_5838_, 1);
v___x_5840_ = l_Array_unzip___redArg(v_a_5839_);
lean_dec(v_a_5839_);
v_fst_5841_ = lean_ctor_get(v___x_5840_, 0);
lean_inc(v_fst_5841_);
v_snd_5842_ = lean_ctor_get(v___x_5840_, 1);
lean_inc(v_snd_5842_);
lean_dec_ref(v___x_5840_);
v___x_5843_ = l_Lean_mkAppN(v_noConfusion_5829_, v_fst_5841_);
lean_dec(v_fst_5841_);
v___x_5844_ = l_Lean_mkAppN(v___x_5843_, v_snd_5842_);
lean_dec(v_snd_5842_);
v___x_5845_ = l_Lean_mkAppN(v___x_5844_, v_eqs_5835_);
lean_dec_ref(v_eqs_5835_);
lean_inc(v___y_5818_);
lean_inc_ref(v___y_5817_);
lean_inc(v___y_5816_);
lean_inc_ref(v___y_5815_);
lean_inc_ref(v___x_5845_);
v___x_5846_ = lean_infer_type(v___x_5845_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
if (lean_obj_tag(v___x_5846_) == 0)
{
lean_object* v_a_5847_; lean_object* v___x_5848_; 
v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
lean_inc(v_a_5847_);
lean_dec_ref_known(v___x_5846_, 1);
lean_inc(v___y_5818_);
lean_inc_ref(v___y_5817_);
lean_inc(v___y_5816_);
lean_inc_ref(v___y_5815_);
v___x_5848_ = lean_whnf(v_a_5847_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
if (lean_obj_tag(v___x_5848_) == 0)
{
lean_object* v_a_5849_; 
v_a_5849_ = lean_ctor_get(v___x_5848_, 0);
lean_inc(v_a_5849_);
lean_dec_ref_known(v___x_5848_, 1);
if (lean_obj_tag(v_a_5849_) == 7)
{
lean_object* v_binderType_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; 
lean_inc_ref(v_toConstantVal_5820_);
lean_dec_ref(v_ctorVal_5810_);
v_binderType_5850_ = lean_ctor_get(v_a_5849_, 1);
lean_inc_ref(v_binderType_5850_);
lean_dec_ref_known(v_a_5849_, 3);
v___x_5851_ = lean_box(0);
v___x_5852_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5850_, v___x_5851_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
if (lean_obj_tag(v___x_5852_) == 0)
{
lean_object* v_a_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; 
v_a_5853_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_a_5853_);
lean_dec_ref_known(v___x_5852_, 1);
v___x_5854_ = l_Lean_Expr_mvarId_x21(v_a_5853_);
v___x_5855_ = l_Lean_MVarId_intros(v___x_5854_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
if (lean_obj_tag(v___x_5855_) == 0)
{
lean_object* v_a_5856_; lean_object* v_snd_5857_; lean_object* v_name_5858_; lean_object* v___x_5859_; 
v_a_5856_ = lean_ctor_get(v___x_5855_, 0);
lean_inc(v_a_5856_);
lean_dec_ref_known(v___x_5855_, 1);
v_snd_5857_ = lean_ctor_get(v_a_5856_, 1);
lean_inc(v_snd_5857_);
lean_dec(v_a_5856_);
v_name_5858_ = lean_ctor_get(v_toConstantVal_5820_, 0);
lean_inc(v_name_5858_);
lean_dec_ref(v_toConstantVal_5820_);
v___x_5859_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5857_, v_name_5858_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
if (lean_obj_tag(v___x_5859_) == 0)
{
lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5889_; 
lean_dec_ref_known(v___x_5859_, 1);
v___x_5860_ = l_Lean_Expr_app___override(v___x_5845_, v_a_5853_);
v___x_5861_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5860_, v___y_5816_);
v_a_5862_ = lean_ctor_get(v___x_5861_, 0);
v_isSharedCheck_5889_ = !lean_is_exclusive(v___x_5861_);
if (v_isSharedCheck_5889_ == 0)
{
v___x_5864_ = v___x_5861_;
v_isShared_5865_ = v_isSharedCheck_5889_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5861_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5889_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
uint8_t v___x_5866_; uint8_t v___x_5867_; uint8_t v___x_5868_; lean_object* v___x_5869_; 
v___x_5866_ = 0;
v___x_5867_ = 1;
v___x_5868_ = 1;
v___x_5869_ = l_Lean_Meta_mkLambdaFVars(v_xs_5813_, v_a_5862_, v___x_5866_, v___x_5867_, v___x_5866_, v___x_5867_, v___x_5868_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
lean_dec_ref(v_xs_5813_);
if (lean_obj_tag(v___x_5869_) == 0)
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5880_; 
v_a_5870_ = lean_ctor_get(v___x_5869_, 0);
v_isSharedCheck_5880_ = !lean_is_exclusive(v___x_5869_);
if (v_isSharedCheck_5880_ == 0)
{
v___x_5872_ = v___x_5869_;
v_isShared_5873_ = v_isSharedCheck_5880_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v___x_5869_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5880_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5865_ == 0)
{
lean_ctor_set_tag(v___x_5864_, 1);
lean_ctor_set(v___x_5864_, 0, v_a_5870_);
v___x_5875_ = v___x_5864_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5879_; 
v_reuseFailAlloc_5879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5879_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5879_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
lean_object* v___x_5877_; 
if (v_isShared_5873_ == 0)
{
lean_ctor_set(v___x_5872_, 0, v___x_5875_);
v___x_5877_ = v___x_5872_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5878_; 
v_reuseFailAlloc_5878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5878_, 0, v___x_5875_);
v___x_5877_ = v_reuseFailAlloc_5878_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
return v___x_5877_;
}
}
}
}
else
{
lean_object* v_a_5881_; lean_object* v___x_5883_; uint8_t v_isShared_5884_; uint8_t v_isSharedCheck_5888_; 
lean_del_object(v___x_5864_);
v_a_5881_ = lean_ctor_get(v___x_5869_, 0);
v_isSharedCheck_5888_ = !lean_is_exclusive(v___x_5869_);
if (v_isSharedCheck_5888_ == 0)
{
v___x_5883_ = v___x_5869_;
v_isShared_5884_ = v_isSharedCheck_5888_;
goto v_resetjp_5882_;
}
else
{
lean_inc(v_a_5881_);
lean_dec(v___x_5869_);
v___x_5883_ = lean_box(0);
v_isShared_5884_ = v_isSharedCheck_5888_;
goto v_resetjp_5882_;
}
v_resetjp_5882_:
{
lean_object* v___x_5886_; 
if (v_isShared_5884_ == 0)
{
v___x_5886_ = v___x_5883_;
goto v_reusejp_5885_;
}
else
{
lean_object* v_reuseFailAlloc_5887_; 
v_reuseFailAlloc_5887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_a_5881_);
v___x_5886_ = v_reuseFailAlloc_5887_;
goto v_reusejp_5885_;
}
v_reusejp_5885_:
{
return v___x_5886_;
}
}
}
}
}
else
{
lean_object* v_a_5890_; lean_object* v___x_5892_; uint8_t v_isShared_5893_; uint8_t v_isSharedCheck_5897_; 
lean_dec(v_a_5853_);
lean_dec_ref(v___x_5845_);
lean_dec_ref(v_xs_5813_);
v_a_5890_ = lean_ctor_get(v___x_5859_, 0);
v_isSharedCheck_5897_ = !lean_is_exclusive(v___x_5859_);
if (v_isSharedCheck_5897_ == 0)
{
v___x_5892_ = v___x_5859_;
v_isShared_5893_ = v_isSharedCheck_5897_;
goto v_resetjp_5891_;
}
else
{
lean_inc(v_a_5890_);
lean_dec(v___x_5859_);
v___x_5892_ = lean_box(0);
v_isShared_5893_ = v_isSharedCheck_5897_;
goto v_resetjp_5891_;
}
v_resetjp_5891_:
{
lean_object* v___x_5895_; 
if (v_isShared_5893_ == 0)
{
v___x_5895_ = v___x_5892_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v_a_5890_);
v___x_5895_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
return v___x_5895_;
}
}
}
}
else
{
lean_object* v_a_5898_; lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5905_; 
lean_dec(v_a_5853_);
lean_dec_ref(v___x_5845_);
lean_dec_ref(v_toConstantVal_5820_);
lean_dec_ref(v_xs_5813_);
v_a_5898_ = lean_ctor_get(v___x_5855_, 0);
v_isSharedCheck_5905_ = !lean_is_exclusive(v___x_5855_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5900_ = v___x_5855_;
v_isShared_5901_ = v_isSharedCheck_5905_;
goto v_resetjp_5899_;
}
else
{
lean_inc(v_a_5898_);
lean_dec(v___x_5855_);
v___x_5900_ = lean_box(0);
v_isShared_5901_ = v_isSharedCheck_5905_;
goto v_resetjp_5899_;
}
v_resetjp_5899_:
{
lean_object* v___x_5903_; 
if (v_isShared_5901_ == 0)
{
v___x_5903_ = v___x_5900_;
goto v_reusejp_5902_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_a_5898_);
v___x_5903_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5902_;
}
v_reusejp_5902_:
{
return v___x_5903_;
}
}
}
}
else
{
lean_object* v_a_5906_; lean_object* v___x_5908_; uint8_t v_isShared_5909_; uint8_t v_isSharedCheck_5913_; 
lean_dec_ref(v___x_5845_);
lean_dec_ref(v_toConstantVal_5820_);
lean_dec_ref(v_xs_5813_);
v_a_5906_ = lean_ctor_get(v___x_5852_, 0);
v_isSharedCheck_5913_ = !lean_is_exclusive(v___x_5852_);
if (v_isSharedCheck_5913_ == 0)
{
v___x_5908_ = v___x_5852_;
v_isShared_5909_ = v_isSharedCheck_5913_;
goto v_resetjp_5907_;
}
else
{
lean_inc(v_a_5906_);
lean_dec(v___x_5852_);
v___x_5908_ = lean_box(0);
v_isShared_5909_ = v_isSharedCheck_5913_;
goto v_resetjp_5907_;
}
v_resetjp_5907_:
{
lean_object* v___x_5911_; 
if (v_isShared_5909_ == 0)
{
v___x_5911_ = v___x_5908_;
goto v_reusejp_5910_;
}
else
{
lean_object* v_reuseFailAlloc_5912_; 
v_reuseFailAlloc_5912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5912_, 0, v_a_5906_);
v___x_5911_ = v_reuseFailAlloc_5912_;
goto v_reusejp_5910_;
}
v_reusejp_5910_:
{
return v___x_5911_;
}
}
}
}
else
{
lean_object* v___x_5914_; 
lean_dec(v_a_5849_);
lean_dec_ref(v___x_5845_);
lean_dec_ref(v_xs_5813_);
v___x_5914_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5810_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
return v___x_5914_;
}
}
else
{
lean_object* v_a_5915_; lean_object* v___x_5917_; uint8_t v_isShared_5918_; uint8_t v_isSharedCheck_5922_; 
lean_dec_ref(v___x_5845_);
lean_dec_ref(v_xs_5813_);
lean_dec_ref(v_ctorVal_5810_);
v_a_5915_ = lean_ctor_get(v___x_5848_, 0);
v_isSharedCheck_5922_ = !lean_is_exclusive(v___x_5848_);
if (v_isSharedCheck_5922_ == 0)
{
v___x_5917_ = v___x_5848_;
v_isShared_5918_ = v_isSharedCheck_5922_;
goto v_resetjp_5916_;
}
else
{
lean_inc(v_a_5915_);
lean_dec(v___x_5848_);
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
else
{
lean_object* v_a_5923_; lean_object* v___x_5925_; uint8_t v_isShared_5926_; uint8_t v_isSharedCheck_5930_; 
lean_dec_ref(v___x_5845_);
lean_dec_ref(v_xs_5813_);
lean_dec_ref(v_ctorVal_5810_);
v_a_5923_ = lean_ctor_get(v___x_5846_, 0);
v_isSharedCheck_5930_ = !lean_is_exclusive(v___x_5846_);
if (v_isSharedCheck_5930_ == 0)
{
v___x_5925_ = v___x_5846_;
v_isShared_5926_ = v_isSharedCheck_5930_;
goto v_resetjp_5924_;
}
else
{
lean_inc(v_a_5923_);
lean_dec(v___x_5846_);
v___x_5925_ = lean_box(0);
v_isShared_5926_ = v_isSharedCheck_5930_;
goto v_resetjp_5924_;
}
v_resetjp_5924_:
{
lean_object* v___x_5928_; 
if (v_isShared_5926_ == 0)
{
v___x_5928_ = v___x_5925_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5929_; 
v_reuseFailAlloc_5929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5929_, 0, v_a_5923_);
v___x_5928_ = v_reuseFailAlloc_5929_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
return v___x_5928_;
}
}
}
}
else
{
lean_object* v_a_5931_; lean_object* v___x_5933_; uint8_t v_isShared_5934_; uint8_t v_isSharedCheck_5938_; 
lean_dec_ref(v_eqs_5835_);
lean_dec_ref(v_noConfusion_5829_);
lean_dec_ref(v_xs_5813_);
lean_dec_ref(v_ctorVal_5810_);
v_a_5931_ = lean_ctor_get(v___x_5838_, 0);
v_isSharedCheck_5938_ = !lean_is_exclusive(v___x_5838_);
if (v_isSharedCheck_5938_ == 0)
{
v___x_5933_ = v___x_5838_;
v_isShared_5934_ = v_isSharedCheck_5938_;
goto v_resetjp_5932_;
}
else
{
lean_inc(v_a_5931_);
lean_dec(v___x_5838_);
v___x_5933_ = lean_box(0);
v_isShared_5934_ = v_isSharedCheck_5938_;
goto v_resetjp_5932_;
}
v_resetjp_5932_:
{
lean_object* v___x_5936_; 
if (v_isShared_5934_ == 0)
{
v___x_5936_ = v___x_5933_;
goto v_reusejp_5935_;
}
else
{
lean_object* v_reuseFailAlloc_5937_; 
v_reuseFailAlloc_5937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5937_, 0, v_a_5931_);
v___x_5936_ = v_reuseFailAlloc_5937_;
goto v_reusejp_5935_;
}
v_reusejp_5935_:
{
return v___x_5936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5945_, lean_object* v_us_5946_, lean_object* v_numIndices_5947_, lean_object* v_xs_5948_, lean_object* v_type_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_){
_start:
{
lean_object* v_res_5955_; 
v_res_5955_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5945_, v_us_5946_, v_numIndices_5947_, v_xs_5948_, v_type_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_);
lean_dec(v___y_5953_);
lean_dec_ref(v___y_5952_);
lean_dec(v___y_5951_);
lean_dec_ref(v___y_5950_);
lean_dec(v_numIndices_5947_);
return v_res_5955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5956_, lean_object* v_typeInfo_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_, lean_object* v_a_5961_){
_start:
{
lean_object* v_thmType_5963_; lean_object* v_us_5964_; lean_object* v_numIndices_5965_; lean_object* v___f_5966_; uint8_t v___x_5967_; lean_object* v___x_5968_; 
v_thmType_5963_ = lean_ctor_get(v_typeInfo_5957_, 0);
lean_inc_ref(v_thmType_5963_);
v_us_5964_ = lean_ctor_get(v_typeInfo_5957_, 1);
lean_inc(v_us_5964_);
v_numIndices_5965_ = lean_ctor_get(v_typeInfo_5957_, 2);
lean_inc(v_numIndices_5965_);
lean_dec_ref(v_typeInfo_5957_);
v___f_5966_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5966_, 0, v_ctorVal_5956_);
lean_closure_set(v___f_5966_, 1, v_us_5964_);
lean_closure_set(v___f_5966_, 2, v_numIndices_5965_);
v___x_5967_ = 0;
v___x_5968_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5963_, v___f_5966_, v___x_5967_, v___x_5967_, v_a_5958_, v_a_5959_, v_a_5960_, v_a_5961_);
return v___x_5968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5969_, lean_object* v_typeInfo_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_){
_start:
{
lean_object* v_res_5976_; 
v_res_5976_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5969_, v_typeInfo_5970_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_);
lean_dec(v_a_5974_);
lean_dec_ref(v_a_5973_);
lean_dec(v_a_5972_);
lean_dec_ref(v_a_5971_);
return v_res_5976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5979_){
_start:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5980_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5981_ = l_Lean_Name_str___override(v_ctorName_5979_, v___x_5980_);
return v___x_5981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5982_, lean_object* v_ctorVal_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_){
_start:
{
lean_object* v___x_5989_; 
lean_inc_ref(v_ctorVal_5983_);
v___x_5989_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5983_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_);
if (lean_obj_tag(v___x_5989_) == 0)
{
lean_object* v_a_5990_; lean_object* v___x_5992_; uint8_t v_isShared_5993_; uint8_t v_isSharedCheck_6051_; 
v_a_5990_ = lean_ctor_get(v___x_5989_, 0);
v_isSharedCheck_6051_ = !lean_is_exclusive(v___x_5989_);
if (v_isSharedCheck_6051_ == 0)
{
v___x_5992_ = v___x_5989_;
v_isShared_5993_ = v_isSharedCheck_6051_;
goto v_resetjp_5991_;
}
else
{
lean_inc(v_a_5990_);
lean_dec(v___x_5989_);
v___x_5992_ = lean_box(0);
v_isShared_5993_ = v_isSharedCheck_6051_;
goto v_resetjp_5991_;
}
v_resetjp_5991_:
{
if (lean_obj_tag(v_a_5990_) == 1)
{
lean_object* v_val_5994_; lean_object* v___x_5995_; 
lean_del_object(v___x_5992_);
v_val_5994_ = lean_ctor_get(v_a_5990_, 0);
lean_inc_n(v_val_5994_, 2);
lean_dec_ref_known(v_a_5990_, 1);
lean_inc_ref(v_ctorVal_5983_);
v___x_5995_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5983_, v_val_5994_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_);
if (lean_obj_tag(v___x_5995_) == 0)
{
lean_object* v_a_5996_; lean_object* v___x_5998_; uint8_t v_isShared_5999_; uint8_t v_isSharedCheck_6038_; 
v_a_5996_ = lean_ctor_get(v___x_5995_, 0);
v_isSharedCheck_6038_ = !lean_is_exclusive(v___x_5995_);
if (v_isSharedCheck_6038_ == 0)
{
v___x_5998_ = v___x_5995_;
v_isShared_5999_ = v_isSharedCheck_6038_;
goto v_resetjp_5997_;
}
else
{
lean_inc(v_a_5996_);
lean_dec(v___x_5995_);
v___x_5998_ = lean_box(0);
v_isShared_5999_ = v_isSharedCheck_6038_;
goto v_resetjp_5997_;
}
v_resetjp_5997_:
{
if (lean_obj_tag(v_a_5996_) == 1)
{
lean_object* v_toConstantVal_6000_; lean_object* v_val_6001_; lean_object* v___x_6003_; uint8_t v_isShared_6004_; uint8_t v_isSharedCheck_6033_; 
v_toConstantVal_6000_ = lean_ctor_get(v_ctorVal_5983_, 0);
lean_inc_ref(v_toConstantVal_6000_);
lean_dec_ref(v_ctorVal_5983_);
v_val_6001_ = lean_ctor_get(v_a_5996_, 0);
v_isSharedCheck_6033_ = !lean_is_exclusive(v_a_5996_);
if (v_isSharedCheck_6033_ == 0)
{
v___x_6003_ = v_a_5996_;
v_isShared_6004_ = v_isSharedCheck_6033_;
goto v_resetjp_6002_;
}
else
{
lean_inc(v_val_6001_);
lean_dec(v_a_5996_);
v___x_6003_ = lean_box(0);
v_isShared_6004_ = v_isSharedCheck_6033_;
goto v_resetjp_6002_;
}
v_resetjp_6002_:
{
lean_object* v_levelParams_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6030_; 
v_levelParams_6005_ = lean_ctor_get(v_toConstantVal_6000_, 1);
v_isSharedCheck_6030_ = !lean_is_exclusive(v_toConstantVal_6000_);
if (v_isSharedCheck_6030_ == 0)
{
lean_object* v_unused_6031_; lean_object* v_unused_6032_; 
v_unused_6031_ = lean_ctor_get(v_toConstantVal_6000_, 2);
lean_dec(v_unused_6031_);
v_unused_6032_ = lean_ctor_get(v_toConstantVal_6000_, 0);
lean_dec(v_unused_6032_);
v___x_6007_ = v_toConstantVal_6000_;
v_isShared_6008_ = v_isSharedCheck_6030_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_levelParams_6005_);
lean_dec(v_toConstantVal_6000_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6030_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v_thmType_6009_; lean_object* v___x_6011_; uint8_t v_isShared_6012_; uint8_t v_isSharedCheck_6027_; 
v_thmType_6009_ = lean_ctor_get(v_val_5994_, 0);
v_isSharedCheck_6027_ = !lean_is_exclusive(v_val_5994_);
if (v_isSharedCheck_6027_ == 0)
{
lean_object* v_unused_6028_; lean_object* v_unused_6029_; 
v_unused_6028_ = lean_ctor_get(v_val_5994_, 2);
lean_dec(v_unused_6028_);
v_unused_6029_ = lean_ctor_get(v_val_5994_, 1);
lean_dec(v_unused_6029_);
v___x_6011_ = v_val_5994_;
v_isShared_6012_ = v_isSharedCheck_6027_;
goto v_resetjp_6010_;
}
else
{
lean_inc(v_thmType_6009_);
lean_dec(v_val_5994_);
v___x_6011_ = lean_box(0);
v_isShared_6012_ = v_isSharedCheck_6027_;
goto v_resetjp_6010_;
}
v_resetjp_6010_:
{
lean_object* v___x_6014_; 
lean_inc(v_thmName_5982_);
if (v_isShared_6008_ == 0)
{
lean_ctor_set(v___x_6007_, 2, v_thmType_6009_);
lean_ctor_set(v___x_6007_, 0, v_thmName_5982_);
v___x_6014_ = v___x_6007_;
goto v_reusejp_6013_;
}
else
{
lean_object* v_reuseFailAlloc_6026_; 
v_reuseFailAlloc_6026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_thmName_5982_);
lean_ctor_set(v_reuseFailAlloc_6026_, 1, v_levelParams_6005_);
lean_ctor_set(v_reuseFailAlloc_6026_, 2, v_thmType_6009_);
v___x_6014_ = v_reuseFailAlloc_6026_;
goto v_reusejp_6013_;
}
v_reusejp_6013_:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6018_; 
v___x_6015_ = lean_box(0);
v___x_6016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6016_, 0, v_thmName_5982_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
if (v_isShared_6012_ == 0)
{
lean_ctor_set(v___x_6011_, 2, v___x_6016_);
lean_ctor_set(v___x_6011_, 1, v_val_6001_);
lean_ctor_set(v___x_6011_, 0, v___x_6014_);
v___x_6018_ = v___x_6011_;
goto v_reusejp_6017_;
}
else
{
lean_object* v_reuseFailAlloc_6025_; 
v_reuseFailAlloc_6025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6025_, 0, v___x_6014_);
lean_ctor_set(v_reuseFailAlloc_6025_, 1, v_val_6001_);
lean_ctor_set(v_reuseFailAlloc_6025_, 2, v___x_6016_);
v___x_6018_ = v_reuseFailAlloc_6025_;
goto v_reusejp_6017_;
}
v_reusejp_6017_:
{
lean_object* v___x_6020_; 
if (v_isShared_6004_ == 0)
{
lean_ctor_set(v___x_6003_, 0, v___x_6018_);
v___x_6020_ = v___x_6003_;
goto v_reusejp_6019_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v___x_6018_);
v___x_6020_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6019_;
}
v_reusejp_6019_:
{
lean_object* v___x_6022_; 
if (v_isShared_5999_ == 0)
{
lean_ctor_set(v___x_5998_, 0, v___x_6020_);
v___x_6022_ = v___x_5998_;
goto v_reusejp_6021_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v___x_6020_);
v___x_6022_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6021_;
}
v_reusejp_6021_:
{
return v___x_6022_;
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
lean_object* v___x_6034_; lean_object* v___x_6036_; 
lean_dec(v_a_5996_);
lean_dec(v_val_5994_);
lean_dec_ref(v_ctorVal_5983_);
lean_dec(v_thmName_5982_);
v___x_6034_ = lean_box(0);
if (v_isShared_5999_ == 0)
{
lean_ctor_set(v___x_5998_, 0, v___x_6034_);
v___x_6036_ = v___x_5998_;
goto v_reusejp_6035_;
}
else
{
lean_object* v_reuseFailAlloc_6037_; 
v_reuseFailAlloc_6037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6034_);
v___x_6036_ = v_reuseFailAlloc_6037_;
goto v_reusejp_6035_;
}
v_reusejp_6035_:
{
return v___x_6036_;
}
}
}
}
else
{
lean_object* v_a_6039_; lean_object* v___x_6041_; uint8_t v_isShared_6042_; uint8_t v_isSharedCheck_6046_; 
lean_dec(v_val_5994_);
lean_dec_ref(v_ctorVal_5983_);
lean_dec(v_thmName_5982_);
v_a_6039_ = lean_ctor_get(v___x_5995_, 0);
v_isSharedCheck_6046_ = !lean_is_exclusive(v___x_5995_);
if (v_isSharedCheck_6046_ == 0)
{
v___x_6041_ = v___x_5995_;
v_isShared_6042_ = v_isSharedCheck_6046_;
goto v_resetjp_6040_;
}
else
{
lean_inc(v_a_6039_);
lean_dec(v___x_5995_);
v___x_6041_ = lean_box(0);
v_isShared_6042_ = v_isSharedCheck_6046_;
goto v_resetjp_6040_;
}
v_resetjp_6040_:
{
lean_object* v___x_6044_; 
if (v_isShared_6042_ == 0)
{
v___x_6044_ = v___x_6041_;
goto v_reusejp_6043_;
}
else
{
lean_object* v_reuseFailAlloc_6045_; 
v_reuseFailAlloc_6045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6045_, 0, v_a_6039_);
v___x_6044_ = v_reuseFailAlloc_6045_;
goto v_reusejp_6043_;
}
v_reusejp_6043_:
{
return v___x_6044_;
}
}
}
}
else
{
lean_object* v___x_6047_; lean_object* v___x_6049_; 
lean_dec(v_a_5990_);
lean_dec_ref(v_ctorVal_5983_);
lean_dec(v_thmName_5982_);
v___x_6047_ = lean_box(0);
if (v_isShared_5993_ == 0)
{
lean_ctor_set(v___x_5992_, 0, v___x_6047_);
v___x_6049_ = v___x_5992_;
goto v_reusejp_6048_;
}
else
{
lean_object* v_reuseFailAlloc_6050_; 
v_reuseFailAlloc_6050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6050_, 0, v___x_6047_);
v___x_6049_ = v_reuseFailAlloc_6050_;
goto v_reusejp_6048_;
}
v_reusejp_6048_:
{
return v___x_6049_;
}
}
}
}
else
{
lean_object* v_a_6052_; lean_object* v___x_6054_; uint8_t v_isShared_6055_; uint8_t v_isSharedCheck_6059_; 
lean_dec_ref(v_ctorVal_5983_);
lean_dec(v_thmName_5982_);
v_a_6052_ = lean_ctor_get(v___x_5989_, 0);
v_isSharedCheck_6059_ = !lean_is_exclusive(v___x_5989_);
if (v_isSharedCheck_6059_ == 0)
{
v___x_6054_ = v___x_5989_;
v_isShared_6055_ = v_isSharedCheck_6059_;
goto v_resetjp_6053_;
}
else
{
lean_inc(v_a_6052_);
lean_dec(v___x_5989_);
v___x_6054_ = lean_box(0);
v_isShared_6055_ = v_isSharedCheck_6059_;
goto v_resetjp_6053_;
}
v_resetjp_6053_:
{
lean_object* v___x_6057_; 
if (v_isShared_6055_ == 0)
{
v___x_6057_ = v___x_6054_;
goto v_reusejp_6056_;
}
else
{
lean_object* v_reuseFailAlloc_6058_; 
v_reuseFailAlloc_6058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6058_, 0, v_a_6052_);
v___x_6057_ = v_reuseFailAlloc_6058_;
goto v_reusejp_6056_;
}
v_reusejp_6056_:
{
return v___x_6057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6060_, lean_object* v_ctorVal_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_){
_start:
{
lean_object* v_res_6067_; 
v_res_6067_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6060_, v_ctorVal_6061_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_);
lean_dec(v_a_6065_);
lean_dec_ref(v_a_6064_);
lean_dec(v_a_6063_);
lean_dec_ref(v_a_6062_);
return v_res_6067_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6068_, lean_object* v_n_6069_){
_start:
{
if (lean_obj_tag(v_n_6069_) == 1)
{
lean_object* v_pre_6070_; lean_object* v_str_6071_; lean_object* v___x_6072_; uint8_t v___x_6073_; 
v_pre_6070_ = lean_ctor_get(v_n_6069_, 0);
lean_inc(v_pre_6070_);
v_str_6071_ = lean_ctor_get(v_n_6069_, 1);
lean_inc_ref(v_str_6071_);
lean_dec_ref_known(v_n_6069_, 2);
v___x_6072_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6073_ = lean_string_dec_eq(v_str_6071_, v___x_6072_);
lean_dec_ref(v_str_6071_);
if (v___x_6073_ == 0)
{
lean_dec(v_pre_6070_);
lean_dec_ref(v_env_6068_);
return v___x_6073_;
}
else
{
uint8_t v___x_6074_; lean_object* v___x_6075_; 
v___x_6074_ = 0;
v___x_6075_ = l_Lean_Environment_find_x3f(v_env_6068_, v_pre_6070_, v___x_6074_);
if (lean_obj_tag(v___x_6075_) == 1)
{
lean_object* v_val_6076_; 
v_val_6076_ = lean_ctor_get(v___x_6075_, 0);
lean_inc(v_val_6076_);
lean_dec_ref_known(v___x_6075_, 1);
if (lean_obj_tag(v_val_6076_) == 6)
{
lean_dec_ref_known(v_val_6076_, 1);
return v___x_6073_;
}
else
{
lean_dec(v_val_6076_);
return v___x_6074_;
}
}
else
{
lean_dec(v___x_6075_);
return v___x_6074_;
}
}
}
else
{
uint8_t v___x_6077_; 
lean_dec(v_n_6069_);
lean_dec_ref(v_env_6068_);
v___x_6077_ = 0;
return v___x_6077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6078_, lean_object* v_n_6079_){
_start:
{
uint8_t v_res_6080_; lean_object* v_r_6081_; 
v_res_6080_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6078_, v_n_6079_);
v_r_6081_ = lean_box(v_res_6080_);
return v_r_6081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6084_; lean_object* v___x_6085_; 
v___f_6084_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6085_ = l_Lean_registerReservedNamePredicate(v___f_6084_);
return v___x_6085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6086_){
_start:
{
lean_object* v_res_6087_; 
v_res_6087_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6087_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6088_, lean_object* v___y_6089_){
_start:
{
lean_object* v___x_6091_; lean_object* v_env_6092_; lean_object* v_toConstantVal_6093_; lean_object* v_value_6094_; lean_object* v_all_6095_; uint8_t v___y_6097_; lean_object* v_type_6105_; uint8_t v___x_6106_; 
v___x_6091_ = lean_st_ref_get(v___y_6089_);
v_env_6092_ = lean_ctor_get(v___x_6091_, 0);
lean_inc_ref_n(v_env_6092_, 2);
lean_dec(v___x_6091_);
v_toConstantVal_6093_ = lean_ctor_get(v_thm_6088_, 0);
v_value_6094_ = lean_ctor_get(v_thm_6088_, 1);
v_all_6095_ = lean_ctor_get(v_thm_6088_, 2);
v_type_6105_ = lean_ctor_get(v_toConstantVal_6093_, 2);
v___x_6106_ = l_Lean_Environment_hasUnsafe(v_env_6092_, v_type_6105_);
if (v___x_6106_ == 0)
{
uint8_t v___x_6107_; 
v___x_6107_ = l_Lean_Environment_hasUnsafe(v_env_6092_, v_value_6094_);
v___y_6097_ = v___x_6107_;
goto v___jp_6096_;
}
else
{
lean_dec_ref(v_env_6092_);
v___y_6097_ = v___x_6106_;
goto v___jp_6096_;
}
v___jp_6096_:
{
if (v___y_6097_ == 0)
{
lean_object* v___x_6098_; lean_object* v___x_6099_; 
v___x_6098_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6098_, 0, v_thm_6088_);
v___x_6099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6098_);
return v___x_6099_;
}
else
{
lean_object* v___x_6100_; uint8_t v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; 
lean_inc(v_all_6095_);
lean_inc_ref(v_value_6094_);
lean_inc_ref(v_toConstantVal_6093_);
lean_dec_ref(v_thm_6088_);
v___x_6100_ = lean_box(0);
v___x_6101_ = 0;
v___x_6102_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6102_, 0, v_toConstantVal_6093_);
lean_ctor_set(v___x_6102_, 1, v_value_6094_);
lean_ctor_set(v___x_6102_, 2, v___x_6100_);
lean_ctor_set(v___x_6102_, 3, v_all_6095_);
lean_ctor_set_uint8(v___x_6102_, sizeof(void*)*4, v___x_6101_);
v___x_6103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6102_);
v___x_6104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
return v___x_6104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_){
_start:
{
lean_object* v_res_6111_; 
v_res_6111_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6108_, v___y_6109_);
lean_dec(v___y_6109_);
return v_res_6111_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_){
_start:
{
lean_object* v___x_6118_; 
v___x_6118_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6112_, v___y_6116_);
return v___x_6118_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_){
_start:
{
lean_object* v_res_6125_; 
v_res_6125_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
lean_dec(v___y_6121_);
lean_dec_ref(v___y_6120_);
return v_res_6125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6126_, uint8_t v___x_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_){
_start:
{
lean_object* v___x_6133_; lean_object* v_a_6134_; lean_object* v___x_6135_; 
v___x_6133_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6126_, v___y_6131_);
v_a_6134_ = lean_ctor_get(v___x_6133_, 0);
lean_inc(v_a_6134_);
lean_dec_ref(v___x_6133_);
v___x_6135_ = l_Lean_addDecl(v_a_6134_, v___x_6127_, v___y_6130_, v___y_6131_);
return v___x_6135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6136_, lean_object* v___x_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_){
_start:
{
uint8_t v___x_2127__boxed_6143_; lean_object* v_res_6144_; 
v___x_2127__boxed_6143_ = lean_unbox(v___x_6137_);
v_res_6144_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6136_, v___x_2127__boxed_6143_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_);
lean_dec(v___y_6141_);
lean_dec_ref(v___y_6140_);
lean_dec(v___y_6139_);
lean_dec_ref(v___y_6138_);
return v_res_6144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; 
v___x_6147_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6148_ = lean_unsigned_to_nat(0u);
v___x_6149_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6148_);
lean_ctor_set(v___x_6149_, 1, v___x_6148_);
lean_ctor_set(v___x_6149_, 2, v___x_6148_);
lean_ctor_set(v___x_6149_, 3, v___x_6148_);
lean_ctor_set(v___x_6149_, 4, v___x_6147_);
lean_ctor_set(v___x_6149_, 5, v___x_6147_);
lean_ctor_set(v___x_6149_, 6, v___x_6147_);
lean_ctor_set(v___x_6149_, 7, v___x_6147_);
lean_ctor_set(v___x_6149_, 8, v___x_6147_);
lean_ctor_set(v___x_6149_, 9, v___x_6147_);
lean_ctor_set(v___x_6149_, 10, v___x_6147_);
return v___x_6149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6150_; lean_object* v___x_6151_; 
v___x_6150_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6151_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6150_);
lean_ctor_set(v___x_6151_, 1, v___x_6150_);
lean_ctor_set(v___x_6151_, 2, v___x_6150_);
lean_ctor_set(v___x_6151_, 3, v___x_6150_);
lean_ctor_set(v___x_6151_, 4, v___x_6150_);
lean_ctor_set(v___x_6151_, 5, v___x_6150_);
return v___x_6151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6152_; lean_object* v___x_6153_; 
v___x_6152_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6153_, 0, v___x_6152_);
lean_ctor_set(v___x_6153_, 1, v___x_6152_);
lean_ctor_set(v___x_6153_, 2, v___x_6152_);
lean_ctor_set(v___x_6153_, 3, v___x_6152_);
lean_ctor_set(v___x_6153_, 4, v___x_6152_);
return v___x_6153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6154_, lean_object* v_name_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
if (lean_obj_tag(v_name_6155_) == 1)
{
lean_object* v_pre_6167_; lean_object* v_str_6168_; lean_object* v___x_6169_; uint8_t v___x_6170_; 
v_pre_6167_ = lean_ctor_get(v_name_6155_, 0);
lean_inc(v_pre_6167_);
v_str_6168_ = lean_ctor_get(v_name_6155_, 1);
v___x_6169_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6170_ = lean_string_dec_eq(v_str_6168_, v___x_6169_);
if (v___x_6170_ == 0)
{
lean_dec_ref_known(v_name_6155_, 2);
lean_dec(v_pre_6167_);
lean_dec(v___x_6154_);
goto v___jp_6163_;
}
else
{
lean_object* v___x_6171_; lean_object* v_env_6172_; uint8_t v___x_6173_; lean_object* v___x_6174_; 
v___x_6171_ = lean_st_ref_get(v___y_6157_);
v_env_6172_ = lean_ctor_get(v___x_6171_, 0);
lean_inc_ref(v_env_6172_);
lean_dec(v___x_6171_);
v___x_6173_ = 0;
lean_inc(v_pre_6167_);
v___x_6174_ = l_Lean_Environment_find_x3f(v_env_6172_, v_pre_6167_, v___x_6173_);
if (lean_obj_tag(v___x_6174_) == 1)
{
lean_object* v_val_6175_; 
v_val_6175_ = lean_ctor_get(v___x_6174_, 0);
lean_inc(v_val_6175_);
lean_dec_ref_known(v___x_6174_, 1);
if (lean_obj_tag(v_val_6175_) == 6)
{
lean_object* v_val_6176_; lean_object* v___x_6178_; uint8_t v_isShared_6179_; uint8_t v_isSharedCheck_6226_; 
v_val_6176_ = lean_ctor_get(v_val_6175_, 0);
v_isSharedCheck_6226_ = !lean_is_exclusive(v_val_6175_);
if (v_isSharedCheck_6226_ == 0)
{
v___x_6178_ = v_val_6175_;
v_isShared_6179_ = v_isSharedCheck_6226_;
goto v_resetjp_6177_;
}
else
{
lean_inc(v_val_6176_);
lean_dec(v_val_6175_);
v___x_6178_ = lean_box(0);
v_isShared_6179_ = v_isSharedCheck_6226_;
goto v_resetjp_6177_;
}
v_resetjp_6177_:
{
uint8_t v___x_6180_; uint8_t v___x_6181_; uint8_t v___x_6182_; lean_object* v___x_6183_; uint64_t v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; uint8_t v_a_6198_; lean_object* v___x_6204_; 
v___x_6180_ = 1;
v___x_6181_ = 0;
v___x_6182_ = 2;
v___x_6183_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_6183_, 0, v___x_6173_);
lean_ctor_set_uint8(v___x_6183_, 1, v___x_6173_);
lean_ctor_set_uint8(v___x_6183_, 2, v___x_6173_);
lean_ctor_set_uint8(v___x_6183_, 3, v___x_6173_);
lean_ctor_set_uint8(v___x_6183_, 4, v___x_6173_);
lean_ctor_set_uint8(v___x_6183_, 5, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 6, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 7, v___x_6173_);
lean_ctor_set_uint8(v___x_6183_, 8, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 9, v___x_6180_);
lean_ctor_set_uint8(v___x_6183_, 10, v___x_6181_);
lean_ctor_set_uint8(v___x_6183_, 11, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 12, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 13, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 14, v___x_6182_);
lean_ctor_set_uint8(v___x_6183_, 15, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 16, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 17, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 18, v___x_6170_);
lean_ctor_set_uint8(v___x_6183_, 19, v___x_6173_);
v___x_6184_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6183_);
v___x_6185_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6185_, 0, v___x_6183_);
lean_ctor_set_uint64(v___x_6185_, sizeof(void*)*1, v___x_6184_);
v___x_6186_ = lean_unsigned_to_nat(0u);
v___x_6187_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6188_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6189_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6190_ = lean_box(0);
lean_inc(v___x_6154_);
v___x_6191_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6191_, 0, v___x_6185_);
lean_ctor_set(v___x_6191_, 1, v___x_6154_);
lean_ctor_set(v___x_6191_, 2, v___x_6188_);
lean_ctor_set(v___x_6191_, 3, v___x_6189_);
lean_ctor_set(v___x_6191_, 4, v___x_6190_);
lean_ctor_set(v___x_6191_, 5, v___x_6186_);
lean_ctor_set(v___x_6191_, 6, v___x_6190_);
lean_ctor_set_uint8(v___x_6191_, sizeof(void*)*7, v___x_6173_);
lean_ctor_set_uint8(v___x_6191_, sizeof(void*)*7 + 1, v___x_6173_);
lean_ctor_set_uint8(v___x_6191_, sizeof(void*)*7 + 2, v___x_6173_);
lean_ctor_set_uint8(v___x_6191_, sizeof(void*)*7 + 3, v___x_6170_);
v___x_6192_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6193_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6194_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6195_, 0, v___x_6192_);
lean_ctor_set(v___x_6195_, 1, v___x_6193_);
lean_ctor_set(v___x_6195_, 2, v___x_6154_);
lean_ctor_set(v___x_6195_, 3, v___x_6187_);
lean_ctor_set(v___x_6195_, 4, v___x_6194_);
v___x_6196_ = lean_st_mk_ref(v___x_6195_);
lean_inc_ref(v_name_6155_);
v___x_6204_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6155_, v_val_6176_, v___x_6191_, v___x_6196_, v___y_6156_, v___y_6157_);
if (lean_obj_tag(v___x_6204_) == 0)
{
lean_object* v_a_6205_; 
v_a_6205_ = lean_ctor_get(v___x_6204_, 0);
lean_inc(v_a_6205_);
lean_dec_ref_known(v___x_6204_, 1);
if (lean_obj_tag(v_a_6205_) == 1)
{
lean_object* v_val_6206_; lean_object* v___x_6207_; lean_object* v___f_6208_; lean_object* v___x_6209_; 
v_val_6206_ = lean_ctor_get(v_a_6205_, 0);
lean_inc(v_val_6206_);
lean_dec_ref_known(v_a_6205_, 1);
v___x_6207_ = lean_box(v___x_6173_);
v___f_6208_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6208_, 0, v_val_6206_);
lean_closure_set(v___f_6208_, 1, v___x_6207_);
v___x_6209_ = l_Lean_Meta_realizeConst(v_pre_6167_, v_name_6155_, v___f_6208_, v___x_6191_, v___x_6196_, v___y_6156_, v___y_6157_);
lean_dec_ref_known(v___x_6191_, 7);
if (lean_obj_tag(v___x_6209_) == 0)
{
lean_dec_ref_known(v___x_6209_, 1);
v_a_6198_ = v___x_6170_;
goto v___jp_6197_;
}
else
{
lean_object* v_a_6210_; lean_object* v___x_6212_; uint8_t v_isShared_6213_; uint8_t v_isSharedCheck_6217_; 
lean_dec(v___x_6196_);
lean_del_object(v___x_6178_);
v_a_6210_ = lean_ctor_get(v___x_6209_, 0);
v_isSharedCheck_6217_ = !lean_is_exclusive(v___x_6209_);
if (v_isSharedCheck_6217_ == 0)
{
v___x_6212_ = v___x_6209_;
v_isShared_6213_ = v_isSharedCheck_6217_;
goto v_resetjp_6211_;
}
else
{
lean_inc(v_a_6210_);
lean_dec(v___x_6209_);
v___x_6212_ = lean_box(0);
v_isShared_6213_ = v_isSharedCheck_6217_;
goto v_resetjp_6211_;
}
v_resetjp_6211_:
{
lean_object* v___x_6215_; 
if (v_isShared_6213_ == 0)
{
v___x_6215_ = v___x_6212_;
goto v_reusejp_6214_;
}
else
{
lean_object* v_reuseFailAlloc_6216_; 
v_reuseFailAlloc_6216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6216_, 0, v_a_6210_);
v___x_6215_ = v_reuseFailAlloc_6216_;
goto v_reusejp_6214_;
}
v_reusejp_6214_:
{
return v___x_6215_;
}
}
}
}
else
{
lean_dec(v_a_6205_);
lean_dec_ref_known(v___x_6191_, 7);
lean_dec(v_pre_6167_);
lean_dec_ref_known(v_name_6155_, 2);
v_a_6198_ = v___x_6173_;
goto v___jp_6197_;
}
}
else
{
lean_object* v_a_6218_; lean_object* v___x_6220_; uint8_t v_isShared_6221_; uint8_t v_isSharedCheck_6225_; 
lean_dec(v___x_6196_);
lean_dec_ref_known(v___x_6191_, 7);
lean_del_object(v___x_6178_);
lean_dec(v_pre_6167_);
lean_dec_ref_known(v_name_6155_, 2);
v_a_6218_ = lean_ctor_get(v___x_6204_, 0);
v_isSharedCheck_6225_ = !lean_is_exclusive(v___x_6204_);
if (v_isSharedCheck_6225_ == 0)
{
v___x_6220_ = v___x_6204_;
v_isShared_6221_ = v_isSharedCheck_6225_;
goto v_resetjp_6219_;
}
else
{
lean_inc(v_a_6218_);
lean_dec(v___x_6204_);
v___x_6220_ = lean_box(0);
v_isShared_6221_ = v_isSharedCheck_6225_;
goto v_resetjp_6219_;
}
v_resetjp_6219_:
{
lean_object* v___x_6223_; 
if (v_isShared_6221_ == 0)
{
v___x_6223_ = v___x_6220_;
goto v_reusejp_6222_;
}
else
{
lean_object* v_reuseFailAlloc_6224_; 
v_reuseFailAlloc_6224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6224_, 0, v_a_6218_);
v___x_6223_ = v_reuseFailAlloc_6224_;
goto v_reusejp_6222_;
}
v_reusejp_6222_:
{
return v___x_6223_;
}
}
}
v___jp_6197_:
{
lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6202_; 
v___x_6199_ = lean_st_ref_get(v___x_6196_);
lean_dec(v___x_6196_);
lean_dec(v___x_6199_);
v___x_6200_ = lean_box(v_a_6198_);
if (v_isShared_6179_ == 0)
{
lean_ctor_set_tag(v___x_6178_, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6200_);
v___x_6202_ = v___x_6178_;
goto v_reusejp_6201_;
}
else
{
lean_object* v_reuseFailAlloc_6203_; 
v_reuseFailAlloc_6203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6203_, 0, v___x_6200_);
v___x_6202_ = v_reuseFailAlloc_6203_;
goto v_reusejp_6201_;
}
v_reusejp_6201_:
{
return v___x_6202_;
}
}
}
}
else
{
lean_dec(v_val_6175_);
lean_dec_ref_known(v_name_6155_, 2);
lean_dec(v_pre_6167_);
lean_dec(v___x_6154_);
goto v___jp_6159_;
}
}
else
{
lean_dec(v___x_6174_);
lean_dec_ref_known(v_name_6155_, 2);
lean_dec(v_pre_6167_);
lean_dec(v___x_6154_);
goto v___jp_6159_;
}
}
}
else
{
lean_dec(v_name_6155_);
lean_dec(v___x_6154_);
goto v___jp_6163_;
}
v___jp_6159_:
{
uint8_t v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; 
v___x_6160_ = 0;
v___x_6161_ = lean_box(v___x_6160_);
v___x_6162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6161_);
return v___x_6162_;
}
v___jp_6163_:
{
uint8_t v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; 
v___x_6164_ = 0;
v___x_6165_ = lean_box(v___x_6164_);
v___x_6166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6165_);
return v___x_6166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6227_, lean_object* v_name_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_){
_start:
{
lean_object* v_res_6232_; 
v_res_6232_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6227_, v_name_6228_, v___y_6229_, v___y_6230_);
lean_dec(v___y_6230_);
lean_dec_ref(v___y_6229_);
return v_res_6232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6236_; lean_object* v___x_6237_; 
v___f_6236_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6237_ = l_Lean_registerReservedNameAction(v___f_6236_);
return v___x_6237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6238_){
_start:
{
lean_object* v_res_6239_; 
v_res_6239_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6239_;
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
