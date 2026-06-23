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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object*);
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
lean_object* v___y_254_; lean_object* v___y_264_; uint8_t v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; uint8_t v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v_fileName_284_; lean_object* v_fileMap_285_; lean_object* v_options_286_; lean_object* v_currRecDepth_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ref_289_; lean_object* v_currNamespace_290_; lean_object* v_openDecls_291_; lean_object* v_initHeartbeats_292_; lean_object* v_maxHeartbeats_293_; lean_object* v_quotContext_294_; lean_object* v_currMacroScope_295_; uint8_t v_diag_296_; lean_object* v_cancelTk_x3f_297_; uint8_t v_suppressElabErrors_298_; lean_object* v_inheritedTraceOptions_299_; 
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
v___x_281_ = lean_nat_add(v___y_279_, v___x_280_);
lean_inc_ref(v___y_278_);
lean_inc(v___y_272_);
lean_inc(v___y_267_);
lean_inc(v___y_269_);
lean_inc(v___y_271_);
lean_inc(v___y_264_);
lean_inc(v___y_275_);
lean_inc(v___y_274_);
lean_inc(v___y_276_);
lean_inc_ref(v___y_273_);
lean_inc_ref(v___y_268_);
lean_inc_ref(v___y_266_);
v___x_282_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_282_, 0, v___y_266_);
lean_ctor_set(v___x_282_, 1, v___y_268_);
lean_ctor_set(v___x_282_, 2, v___y_273_);
lean_ctor_set(v___x_282_, 3, v___x_281_);
lean_ctor_set(v___x_282_, 4, v___y_276_);
lean_ctor_set(v___x_282_, 5, v___y_270_);
lean_ctor_set(v___x_282_, 6, v___y_274_);
lean_ctor_set(v___x_282_, 7, v___y_275_);
lean_ctor_set(v___x_282_, 8, v___y_264_);
lean_ctor_set(v___x_282_, 9, v___y_271_);
lean_ctor_set(v___x_282_, 10, v___y_269_);
lean_ctor_set(v___x_282_, 11, v___y_267_);
lean_ctor_set(v___x_282_, 12, v___y_272_);
lean_ctor_set(v___x_282_, 13, v___y_278_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14, v___y_277_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14 + 1, v___y_265_);
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
v___y_265_ = v_suppressElabErrors_298_;
v___y_266_ = v_fileName_284_;
v___y_267_ = v_currMacroScope_295_;
v___y_268_ = v_fileMap_285_;
v___y_269_ = v_quotContext_294_;
v___y_270_ = v_ref_289_;
v___y_271_ = v_maxHeartbeats_293_;
v___y_272_ = v_cancelTk_x3f_297_;
v___y_273_ = v_options_286_;
v___y_274_ = v_currNamespace_290_;
v___y_275_ = v_openDecls_291_;
v___y_276_ = v_maxRecDepth_288_;
v___y_277_ = v_diag_296_;
v___y_278_ = v_inheritedTraceOptions_299_;
v___y_279_ = v_currRecDepth_287_;
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
v___y_265_ = v_suppressElabErrors_298_;
v___y_266_ = v_fileName_284_;
v___y_267_ = v_currMacroScope_295_;
v___y_268_ = v_fileMap_285_;
v___y_269_ = v_quotContext_294_;
v___y_270_ = v_ref_289_;
v___y_271_ = v_maxHeartbeats_293_;
v___y_272_ = v_cancelTk_x3f_297_;
v___y_273_ = v_options_286_;
v___y_274_ = v_currNamespace_290_;
v___y_275_ = v_openDecls_291_;
v___y_276_ = v_maxRecDepth_288_;
v___y_277_ = v_diag_296_;
v___y_278_ = v_inheritedTraceOptions_299_;
v___y_279_ = v_currRecDepth_287_;
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
lean_object* v___y_439_; lean_object* v___y_440_; uint8_t v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; uint8_t v___y_446_; lean_object* v___y_456_; uint8_t v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; uint8_t v___y_461_; lean_object* v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; uint8_t v___y_474_; lean_object* v___x_481_; 
v___x_481_ = l_Lean_Core_checkSystem(v___x_430_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
lean_dec_ref_known(v___x_481_, 1);
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
lean_dec_ref_known(v_a_483_, 1);
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
lean_dec_ref_known(v_a_483_, 1);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_567_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_e_566_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
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
lean_dec_ref_known(v_a_483_, 1);
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
lean_dec_ref_known(v_e_x3f_570_, 1);
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
lean_dec_ref_known(v___x_493_, 1);
lean_inc_ref(v_body_491_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_491_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; size_t v___x_497_; size_t v___x_498_; uint8_t v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
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
lean_dec_ref_known(v___y_488_, 3);
lean_dec(v_binderName_489_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_495_;
}
}
else
{
lean_dec_ref_known(v___y_488_, 3);
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
lean_dec_ref_known(v___x_507_, 1);
lean_inc_ref(v_body_505_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_505_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; size_t v___x_511_; size_t v___x_512_; uint8_t v___x_513_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
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
lean_dec_ref_known(v___y_488_, 3);
lean_dec(v_binderName_503_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_509_;
}
}
else
{
lean_dec(v_binderName_503_);
lean_dec_ref_known(v___y_488_, 3);
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
lean_dec_ref_known(v___x_522_, 1);
lean_inc_ref(v_value_519_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_value_519_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
lean_inc_ref(v_body_520_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_520_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; size_t v___x_528_; size_t v___x_529_; uint8_t v___x_530_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
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
lean_dec_ref_known(v___y_488_, 4);
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
lean_dec_ref_known(v___y_488_, 4);
lean_dec(v_declName_517_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_524_;
}
}
else
{
lean_dec_ref(v_body_520_);
lean_dec(v_declName_517_);
lean_dec_ref_known(v___y_488_, 4);
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
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = lean_ptr_addr(v_expr_541_);
v___x_545_ = lean_ptr_addr(v_a_543_);
v___x_546_ = lean_usize_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_inc(v_data_540_);
lean_dec_ref_known(v___y_488_, 2);
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
lean_dec_ref_known(v___y_488_, 2);
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
lean_dec_ref_known(v___x_553_, 1);
v___x_555_ = lean_ptr_addr(v_struct_552_);
v___x_556_ = lean_ptr_addr(v_a_554_);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_inc(v_idx_551_);
lean_inc(v_typeName_550_);
lean_dec_ref_known(v___y_488_, 3);
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
lean_dec_ref_known(v___y_488_, 3);
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
lean_dec_ref_known(v___x_614_, 1);
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
lean_dec_ref_known(v___x_611_, 1);
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
lean_dec_ref_known(v_a_655_, 1);
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
lean_dec_ref_known(v_a_655_, 1);
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
lean_dec_ref_known(v_a_655_, 1);
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
lean_dec_ref_known(v_e_x3f_665_, 1);
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
lean_dec_ref_known(v___x_750_, 1);
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
lean_dec_ref_known(v___x_900_, 1);
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
lean_dec_ref_known(v___x_907_, 1);
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
lean_dec_ref_known(v___x_921_, 1);
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
lean_dec_ref_known(v___x_929_, 1);
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
lean_dec_ref_known(v___x_1191_, 1);
if (lean_obj_tag(v_a_1192_) == 7)
{
lean_object* v_binderName_1193_; lean_object* v_binderType_1194_; lean_object* v_body_1195_; lean_object* v_lctx_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_binderName_1193_ = lean_ctor_get(v_a_1192_, 0);
lean_inc(v_binderName_1193_);
v_binderType_1194_ = lean_ctor_get(v_a_1192_, 1);
lean_inc_ref(v_binderType_1194_);
v_body_1195_ = lean_ctor_get(v_a_1192_, 2);
lean_inc_ref(v_body_1195_);
lean_dec_ref_known(v_a_1192_, 3);
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
lean_dec_ref_known(v_____x_1281_, 3);
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
lean_dec_ref_known(v_____x_1292_, 3);
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
lean_dec_ref_known(v___x_1462_, 1);
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
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = l_Lean_mkArrow(v_a_1463_, v_val_1517_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
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
lean_dec_ref_known(v___x_1516_, 1);
v___x_1529_ = l_Lean_Meta_mkEq(v_a_1463_, v_val_1528_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
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
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = l_Lean_Meta_mkForallFVars(v_args1_1449_, v_a_1474_, v___x_1471_, v___x_1464_, v___x_1464_, v___x_1472_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
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
lean_dec_ref_known(v___x_1739_, 1);
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
lean_dec_ref_known(v_as_1867_, 2);
v___x_1877_ = l_Lean_MVarId_assumptionCore(v_head_1875_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; uint8_t v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
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
lean_dec_ref_known(v___x_1905_, 1);
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
lean_dec_ref_known(v___x_2083_, 1);
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
lean_dec_ref_known(v___x_2051_, 1);
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
lean_dec_ref_known(v_a_2052_, 3);
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
lean_dec_ref_known(v___x_2166_, 1);
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
lean_dec_ref_known(v___x_2174_, 1);
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
lean_dec_ref_known(v___x_2328_, 1);
if (lean_obj_tag(v_val_2330_) == 1)
{
uint8_t v_v_2331_; 
v_v_2331_ = lean_ctor_get_uint8(v_val_2330_, 0);
lean_dec_ref_known(v_val_2330_, 0);
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
lean_dec_ref_known(v___x_2372_, 1);
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
uint8_t v___x_12904__boxed_2409_; lean_object* v_res_2410_; 
v___x_12904__boxed_2409_ = lean_unbox(v___x_2402_);
v_res_2410_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2398_, v_val_2399_, v_name_2400_, v_levelParams_2401_, v___x_12904__boxed_2409_, v_____r_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
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
lean_dec_ref_known(v___x_2421_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t v_sz_2459_, size_t v_i_2460_, lean_object* v_bs_2461_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_usize_dec_lt(v_i_2460_, v_sz_2459_);
if (v___x_2462_ == 0)
{
return v_bs_2461_;
}
else
{
lean_object* v_v_2463_; lean_object* v_msg_2464_; lean_object* v___x_2465_; lean_object* v_bs_x27_2466_; size_t v___x_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v_v_2463_ = lean_array_uget_borrowed(v_bs_2461_, v_i_2460_);
v_msg_2464_ = lean_ctor_get(v_v_2463_, 1);
lean_inc_ref(v_msg_2464_);
v___x_2465_ = lean_unsigned_to_nat(0u);
v_bs_x27_2466_ = lean_array_uset(v_bs_2461_, v_i_2460_, v___x_2465_);
v___x_2467_ = ((size_t)1ULL);
v___x_2468_ = lean_usize_add(v_i_2460_, v___x_2467_);
v___x_2469_ = lean_array_uset(v_bs_x27_2466_, v_i_2460_, v_msg_2464_);
v_i_2460_ = v___x_2468_;
v_bs_2461_ = v___x_2469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2471_, lean_object* v_i_2472_, lean_object* v_bs_2473_){
_start:
{
size_t v_sz_boxed_2474_; size_t v_i_boxed_2475_; lean_object* v_res_2476_; 
v_sz_boxed_2474_ = lean_unbox_usize(v_sz_2471_);
lean_dec(v_sz_2471_);
v_i_boxed_2475_ = lean_unbox_usize(v_i_2472_);
lean_dec(v_i_2472_);
v_res_2476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_boxed_2474_, v_i_boxed_2475_, v_bs_2473_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_oldTraces_2477_, lean_object* v_data_2478_, lean_object* v_ref_2479_, lean_object* v_msg_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_fileName_2486_; lean_object* v_fileMap_2487_; lean_object* v_options_2488_; lean_object* v_currRecDepth_2489_; lean_object* v_maxRecDepth_2490_; lean_object* v_ref_2491_; lean_object* v_currNamespace_2492_; lean_object* v_openDecls_2493_; lean_object* v_initHeartbeats_2494_; lean_object* v_maxHeartbeats_2495_; lean_object* v_quotContext_2496_; lean_object* v_currMacroScope_2497_; uint8_t v_diag_2498_; lean_object* v_cancelTk_x3f_2499_; uint8_t v_suppressElabErrors_2500_; lean_object* v_inheritedTraceOptions_2501_; lean_object* v___x_2502_; lean_object* v_traceState_2503_; lean_object* v_traces_2504_; lean_object* v_ref_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; size_t v_sz_2508_; size_t v___x_2509_; lean_object* v___x_2510_; lean_object* v_msg_2511_; lean_object* v___x_2512_; lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2550_; 
v_fileName_2486_ = lean_ctor_get(v___y_2483_, 0);
v_fileMap_2487_ = lean_ctor_get(v___y_2483_, 1);
v_options_2488_ = lean_ctor_get(v___y_2483_, 2);
v_currRecDepth_2489_ = lean_ctor_get(v___y_2483_, 3);
v_maxRecDepth_2490_ = lean_ctor_get(v___y_2483_, 4);
v_ref_2491_ = lean_ctor_get(v___y_2483_, 5);
v_currNamespace_2492_ = lean_ctor_get(v___y_2483_, 6);
v_openDecls_2493_ = lean_ctor_get(v___y_2483_, 7);
v_initHeartbeats_2494_ = lean_ctor_get(v___y_2483_, 8);
v_maxHeartbeats_2495_ = lean_ctor_get(v___y_2483_, 9);
v_quotContext_2496_ = lean_ctor_get(v___y_2483_, 10);
v_currMacroScope_2497_ = lean_ctor_get(v___y_2483_, 11);
v_diag_2498_ = lean_ctor_get_uint8(v___y_2483_, sizeof(void*)*14);
v_cancelTk_x3f_2499_ = lean_ctor_get(v___y_2483_, 12);
v_suppressElabErrors_2500_ = lean_ctor_get_uint8(v___y_2483_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2501_ = lean_ctor_get(v___y_2483_, 13);
v___x_2502_ = lean_st_ref_get(v___y_2484_);
v_traceState_2503_ = lean_ctor_get(v___x_2502_, 4);
lean_inc_ref(v_traceState_2503_);
lean_dec(v___x_2502_);
v_traces_2504_ = lean_ctor_get(v_traceState_2503_, 0);
lean_inc_ref(v_traces_2504_);
lean_dec_ref(v_traceState_2503_);
v_ref_2505_ = l_Lean_replaceRef(v_ref_2479_, v_ref_2491_);
lean_inc_ref(v_inheritedTraceOptions_2501_);
lean_inc(v_cancelTk_x3f_2499_);
lean_inc(v_currMacroScope_2497_);
lean_inc(v_quotContext_2496_);
lean_inc(v_maxHeartbeats_2495_);
lean_inc(v_initHeartbeats_2494_);
lean_inc(v_openDecls_2493_);
lean_inc(v_currNamespace_2492_);
lean_inc(v_maxRecDepth_2490_);
lean_inc(v_currRecDepth_2489_);
lean_inc_ref(v_options_2488_);
lean_inc_ref(v_fileMap_2487_);
lean_inc_ref(v_fileName_2486_);
v___x_2506_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2506_, 0, v_fileName_2486_);
lean_ctor_set(v___x_2506_, 1, v_fileMap_2487_);
lean_ctor_set(v___x_2506_, 2, v_options_2488_);
lean_ctor_set(v___x_2506_, 3, v_currRecDepth_2489_);
lean_ctor_set(v___x_2506_, 4, v_maxRecDepth_2490_);
lean_ctor_set(v___x_2506_, 5, v_ref_2505_);
lean_ctor_set(v___x_2506_, 6, v_currNamespace_2492_);
lean_ctor_set(v___x_2506_, 7, v_openDecls_2493_);
lean_ctor_set(v___x_2506_, 8, v_initHeartbeats_2494_);
lean_ctor_set(v___x_2506_, 9, v_maxHeartbeats_2495_);
lean_ctor_set(v___x_2506_, 10, v_quotContext_2496_);
lean_ctor_set(v___x_2506_, 11, v_currMacroScope_2497_);
lean_ctor_set(v___x_2506_, 12, v_cancelTk_x3f_2499_);
lean_ctor_set(v___x_2506_, 13, v_inheritedTraceOptions_2501_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*14, v_diag_2498_);
lean_ctor_set_uint8(v___x_2506_, sizeof(void*)*14 + 1, v_suppressElabErrors_2500_);
v___x_2507_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2504_);
lean_dec_ref(v_traces_2504_);
v_sz_2508_ = lean_array_size(v___x_2507_);
v___x_2509_ = ((size_t)0ULL);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_2508_, v___x_2509_, v___x_2507_);
v_msg_2511_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2511_, 0, v_data_2478_);
lean_ctor_set(v_msg_2511_, 1, v_msg_2480_);
lean_ctor_set(v_msg_2511_, 2, v___x_2510_);
v___x_2512_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2511_, v___y_2481_, v___y_2482_, v___x_2506_, v___y_2484_);
lean_dec_ref_known(v___x_2506_, 14);
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2550_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2550_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v_traceState_2518_; lean_object* v_env_2519_; lean_object* v_nextMacroScope_2520_; lean_object* v_ngen_2521_; lean_object* v_auxDeclNGen_2522_; lean_object* v_cache_2523_; lean_object* v_messages_2524_; lean_object* v_infoState_2525_; lean_object* v_snapshotTasks_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2549_; 
v___x_2517_ = lean_st_ref_take(v___y_2484_);
v_traceState_2518_ = lean_ctor_get(v___x_2517_, 4);
v_env_2519_ = lean_ctor_get(v___x_2517_, 0);
v_nextMacroScope_2520_ = lean_ctor_get(v___x_2517_, 1);
v_ngen_2521_ = lean_ctor_get(v___x_2517_, 2);
v_auxDeclNGen_2522_ = lean_ctor_get(v___x_2517_, 3);
v_cache_2523_ = lean_ctor_get(v___x_2517_, 5);
v_messages_2524_ = lean_ctor_get(v___x_2517_, 6);
v_infoState_2525_ = lean_ctor_get(v___x_2517_, 7);
v_snapshotTasks_2526_ = lean_ctor_get(v___x_2517_, 8);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2528_ = v___x_2517_;
v_isShared_2529_ = v_isSharedCheck_2549_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_snapshotTasks_2526_);
lean_inc(v_infoState_2525_);
lean_inc(v_messages_2524_);
lean_inc(v_cache_2523_);
lean_inc(v_traceState_2518_);
lean_inc(v_auxDeclNGen_2522_);
lean_inc(v_ngen_2521_);
lean_inc(v_nextMacroScope_2520_);
lean_inc(v_env_2519_);
lean_dec(v___x_2517_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2549_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
uint64_t v_tid_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2547_; 
v_tid_2530_ = lean_ctor_get_uint64(v_traceState_2518_, sizeof(void*)*1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_traceState_2518_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; 
v_unused_2548_ = lean_ctor_get(v_traceState_2518_, 0);
lean_dec(v_unused_2548_);
v___x_2532_ = v_traceState_2518_;
v_isShared_2533_ = v_isSharedCheck_2547_;
goto v_resetjp_2531_;
}
else
{
lean_dec(v_traceState_2518_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2547_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v_ref_2479_);
lean_ctor_set(v___x_2534_, 1, v_a_2513_);
v___x_2535_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2477_, v___x_2534_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2535_);
v___x_2537_ = v___x_2532_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2535_);
lean_ctor_set_uint64(v_reuseFailAlloc_2546_, sizeof(void*)*1, v_tid_2530_);
v___x_2537_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 4, v___x_2537_);
v___x_2539_ = v___x_2528_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_env_2519_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_nextMacroScope_2520_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_ngen_2521_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_auxDeclNGen_2522_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2545_, 5, v_cache_2523_);
lean_ctor_set(v_reuseFailAlloc_2545_, 6, v_messages_2524_);
lean_ctor_set(v_reuseFailAlloc_2545_, 7, v_infoState_2525_);
lean_ctor_set(v_reuseFailAlloc_2545_, 8, v_snapshotTasks_2526_);
v___x_2539_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2540_ = lean_st_ref_set(v___y_2484_, v___x_2539_);
v___x_2541_ = lean_box(0);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2541_);
v___x_2543_ = v___x_2515_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_oldTraces_2551_, lean_object* v_data_2552_, lean_object* v_ref_2553_, lean_object* v_msg_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2551_, v_data_2552_, v_ref_2553_, v_msg_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2561_, lean_object* v_opt_2562_){
_start:
{
lean_object* v_name_2563_; lean_object* v_defValue_2564_; lean_object* v_map_2565_; lean_object* v___x_2566_; 
v_name_2563_ = lean_ctor_get(v_opt_2562_, 0);
v_defValue_2564_ = lean_ctor_get(v_opt_2562_, 1);
v_map_2565_ = lean_ctor_get(v_opts_2561_, 0);
v___x_2566_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2565_, v_name_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_inc(v_defValue_2564_);
return v_defValue_2564_;
}
else
{
lean_object* v_val_2567_; 
v_val_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_val_2567_);
lean_dec_ref_known(v___x_2566_, 1);
if (lean_obj_tag(v_val_2567_) == 3)
{
lean_object* v_v_2568_; 
v_v_2568_ = lean_ctor_get(v_val_2567_, 0);
lean_inc(v_v_2568_);
lean_dec_ref_known(v_val_2567_, 1);
return v_v_2568_;
}
else
{
lean_dec(v_val_2567_);
lean_inc(v_defValue_2564_);
return v_defValue_2564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2569_, lean_object* v_opt_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2569_, v_opt_2570_);
lean_dec_ref(v_opt_2570_);
lean_dec_ref(v_opts_2569_);
return v_res_2571_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_e_2572_){
_start:
{
if (lean_obj_tag(v_e_2572_) == 0)
{
uint8_t v___x_2573_; 
v___x_2573_ = 2;
return v___x_2573_;
}
else
{
uint8_t v___x_2574_; 
v___x_2574_ = 0;
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_e_2575_){
_start:
{
uint8_t v_res_2576_; lean_object* v_r_2577_; 
v_res_2576_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_e_2575_);
lean_dec_ref(v_e_2575_);
v_r_2577_ = lean_box(v_res_2576_);
return v_r_2577_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object* v_x_2578_){
_start:
{
if (lean_obj_tag(v_x_2578_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
v_a_2580_ = lean_ctor_get(v_x_2578_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_x_2578_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v_x_2578_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v_x_2578_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set_tag(v___x_2582_, 1);
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
v_a_2588_ = lean_ctor_get(v_x_2578_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_x_2578_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v_x_2578_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v_x_2578_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 0);
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object* v_x_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2596_);
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
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2602_; double v___x_2603_; 
v___x_2602_ = lean_unsigned_to_nat(1000u);
v___x_2603_ = lean_float_of_nat(v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2604_, uint8_t v_collapsed_2605_, lean_object* v_tag_2606_, lean_object* v_opts_2607_, uint8_t v_clsEnabled_2608_, lean_object* v_oldTraces_2609_, lean_object* v_msg_2610_, lean_object* v_resStartStop_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_fst_2617_; lean_object* v_snd_2618_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v_data_2622_; lean_object* v_fst_2625_; lean_object* v_snd_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___y_2630_; lean_object* v_a_2631_; uint8_t v___y_2646_; double v___y_2677_; 
v_fst_2617_ = lean_ctor_get(v_resStartStop_2611_, 0);
lean_inc(v_fst_2617_);
v_snd_2618_ = lean_ctor_get(v_resStartStop_2611_, 1);
lean_inc(v_snd_2618_);
lean_dec_ref(v_resStartStop_2611_);
v_fst_2625_ = lean_ctor_get(v_snd_2618_, 0);
lean_inc(v_fst_2625_);
v_snd_2626_ = lean_ctor_get(v_snd_2618_, 1);
lean_inc(v_snd_2626_);
lean_dec(v_snd_2618_);
v___x_2627_ = l_Lean_trace_profiler;
v___x_2628_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2607_, v___x_2627_);
if (v___x_2628_ == 0)
{
v___y_2646_ = v___x_2628_;
goto v___jp_2645_;
}
else
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2683_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2607_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; double v___x_2686_; double v___x_2687_; double v___x_2688_; 
v___x_2684_ = l_Lean_trace_profiler_threshold;
v___x_2685_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2607_, v___x_2684_);
v___x_2686_ = lean_float_of_nat(v___x_2685_);
v___x_2687_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2);
v___x_2688_ = lean_float_div(v___x_2686_, v___x_2687_);
v___y_2677_ = v___x_2688_;
goto v___jp_2676_;
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; double v___x_2691_; 
v___x_2689_ = l_Lean_trace_profiler_threshold;
v___x_2690_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2607_, v___x_2689_);
v___x_2691_ = lean_float_of_nat(v___x_2690_);
v___y_2677_ = v___x_2691_;
goto v___jp_2676_;
}
}
v___jp_2619_:
{
lean_object* v___x_2623_; 
lean_inc(v___y_2620_);
v___x_2623_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2609_, v_data_2622_, v___y_2620_, v___y_2621_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v___x_2624_; 
lean_dec_ref_known(v___x_2623_, 1);
v___x_2624_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2617_);
return v___x_2624_;
}
else
{
lean_dec(v_fst_2617_);
return v___x_2623_;
}
}
v___jp_2629_:
{
uint8_t v_result_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; double v___x_2635_; lean_object* v_data_2636_; 
v_result_2632_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_fst_2617_);
v___x_2633_ = lean_box(v_result_2632_);
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
v___x_2635_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2606_);
lean_inc_ref(v___x_2634_);
lean_inc(v_cls_2604_);
v_data_2636_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2636_, 0, v_cls_2604_);
lean_ctor_set(v_data_2636_, 1, v___x_2634_);
lean_ctor_set(v_data_2636_, 2, v_tag_2606_);
lean_ctor_set_float(v_data_2636_, sizeof(void*)*3, v___x_2635_);
lean_ctor_set_float(v_data_2636_, sizeof(void*)*3 + 8, v___x_2635_);
lean_ctor_set_uint8(v_data_2636_, sizeof(void*)*3 + 16, v_collapsed_2605_);
if (v___x_2628_ == 0)
{
lean_dec_ref_known(v___x_2634_, 1);
lean_dec(v_snd_2626_);
lean_dec(v_fst_2625_);
lean_dec_ref(v_tag_2606_);
lean_dec(v_cls_2604_);
v___y_2620_ = v___y_2630_;
v___y_2621_ = v_a_2631_;
v_data_2622_ = v_data_2636_;
goto v___jp_2619_;
}
else
{
lean_object* v_data_2637_; double v___x_2638_; double v___x_2639_; 
lean_dec_ref_known(v_data_2636_, 3);
v_data_2637_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2637_, 0, v_cls_2604_);
lean_ctor_set(v_data_2637_, 1, v___x_2634_);
lean_ctor_set(v_data_2637_, 2, v_tag_2606_);
v___x_2638_ = lean_unbox_float(v_fst_2625_);
lean_dec(v_fst_2625_);
lean_ctor_set_float(v_data_2637_, sizeof(void*)*3, v___x_2638_);
v___x_2639_ = lean_unbox_float(v_snd_2626_);
lean_dec(v_snd_2626_);
lean_ctor_set_float(v_data_2637_, sizeof(void*)*3 + 8, v___x_2639_);
lean_ctor_set_uint8(v_data_2637_, sizeof(void*)*3 + 16, v_collapsed_2605_);
v___y_2620_ = v___y_2630_;
v___y_2621_ = v_a_2631_;
v_data_2622_ = v_data_2637_;
goto v___jp_2619_;
}
}
v___jp_2640_:
{
lean_object* v_ref_2641_; lean_object* v___x_2642_; 
v_ref_2641_ = lean_ctor_get(v___y_2614_, 5);
lean_inc(v___y_2615_);
lean_inc_ref(v___y_2614_);
lean_inc(v___y_2613_);
lean_inc_ref(v___y_2612_);
lean_inc(v_fst_2617_);
v___x_2642_ = lean_apply_6(v_msg_2610_, v_fst_2617_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, lean_box(0));
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___y_2630_ = v_ref_2641_;
v_a_2631_ = v_a_2643_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2644_; 
lean_dec_ref_known(v___x_2642_, 1);
v___x_2644_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
v___y_2630_ = v_ref_2641_;
v_a_2631_ = v___x_2644_;
goto v___jp_2629_;
}
}
v___jp_2645_:
{
if (v_clsEnabled_2608_ == 0)
{
if (v___y_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v_traceState_2648_; lean_object* v_env_2649_; lean_object* v_nextMacroScope_2650_; lean_object* v_ngen_2651_; lean_object* v_auxDeclNGen_2652_; lean_object* v_cache_2653_; lean_object* v_messages_2654_; lean_object* v_infoState_2655_; lean_object* v_snapshotTasks_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_snd_2626_);
lean_dec(v_fst_2625_);
lean_dec_ref(v_msg_2610_);
lean_dec_ref(v_tag_2606_);
lean_dec(v_cls_2604_);
v___x_2647_ = lean_st_ref_take(v___y_2615_);
v_traceState_2648_ = lean_ctor_get(v___x_2647_, 4);
v_env_2649_ = lean_ctor_get(v___x_2647_, 0);
v_nextMacroScope_2650_ = lean_ctor_get(v___x_2647_, 1);
v_ngen_2651_ = lean_ctor_get(v___x_2647_, 2);
v_auxDeclNGen_2652_ = lean_ctor_get(v___x_2647_, 3);
v_cache_2653_ = lean_ctor_get(v___x_2647_, 5);
v_messages_2654_ = lean_ctor_get(v___x_2647_, 6);
v_infoState_2655_ = lean_ctor_get(v___x_2647_, 7);
v_snapshotTasks_2656_ = lean_ctor_get(v___x_2647_, 8);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2658_ = v___x_2647_;
v_isShared_2659_ = v_isSharedCheck_2675_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snapshotTasks_2656_);
lean_inc(v_infoState_2655_);
lean_inc(v_messages_2654_);
lean_inc(v_cache_2653_);
lean_inc(v_traceState_2648_);
lean_inc(v_auxDeclNGen_2652_);
lean_inc(v_ngen_2651_);
lean_inc(v_nextMacroScope_2650_);
lean_inc(v_env_2649_);
lean_dec(v___x_2647_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2675_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
uint64_t v_tid_2660_; lean_object* v_traces_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2674_; 
v_tid_2660_ = lean_ctor_get_uint64(v_traceState_2648_, sizeof(void*)*1);
v_traces_2661_ = lean_ctor_get(v_traceState_2648_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_traceState_2648_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2663_ = v_traceState_2648_;
v_isShared_2664_ = v_isSharedCheck_2674_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_traces_2661_);
lean_dec(v_traceState_2648_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2674_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2665_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2609_, v_traces_2661_);
lean_dec_ref(v_traces_2661_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2665_);
v___x_2667_ = v___x_2663_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2665_);
lean_ctor_set_uint64(v_reuseFailAlloc_2673_, sizeof(void*)*1, v_tid_2660_);
v___x_2667_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2669_; 
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 4, v___x_2667_);
v___x_2669_ = v___x_2658_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_env_2649_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_nextMacroScope_2650_);
lean_ctor_set(v_reuseFailAlloc_2672_, 2, v_ngen_2651_);
lean_ctor_set(v_reuseFailAlloc_2672_, 3, v_auxDeclNGen_2652_);
lean_ctor_set(v_reuseFailAlloc_2672_, 4, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2672_, 5, v_cache_2653_);
lean_ctor_set(v_reuseFailAlloc_2672_, 6, v_messages_2654_);
lean_ctor_set(v_reuseFailAlloc_2672_, 7, v_infoState_2655_);
lean_ctor_set(v_reuseFailAlloc_2672_, 8, v_snapshotTasks_2656_);
v___x_2669_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_st_ref_set(v___y_2615_, v___x_2669_);
v___x_2671_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2617_);
return v___x_2671_;
}
}
}
}
}
else
{
goto v___jp_2640_;
}
}
else
{
goto v___jp_2640_;
}
}
v___jp_2676_:
{
double v___x_2678_; double v___x_2679_; double v___x_2680_; uint8_t v___x_2681_; 
v___x_2678_ = lean_unbox_float(v_snd_2626_);
v___x_2679_ = lean_unbox_float(v_fst_2625_);
v___x_2680_ = lean_float_sub(v___x_2678_, v___x_2679_);
v___x_2681_ = lean_float_decLt(v___y_2677_, v___x_2680_);
v___y_2646_ = v___x_2681_;
goto v___jp_2645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2692_, lean_object* v_collapsed_2693_, lean_object* v_tag_2694_, lean_object* v_opts_2695_, lean_object* v_clsEnabled_2696_, lean_object* v_oldTraces_2697_, lean_object* v_msg_2698_, lean_object* v_resStartStop_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
uint8_t v_collapsed_boxed_2705_; uint8_t v_clsEnabled_boxed_2706_; lean_object* v_res_2707_; 
v_collapsed_boxed_2705_ = lean_unbox(v_collapsed_2693_);
v_clsEnabled_boxed_2706_ = lean_unbox(v_clsEnabled_2696_);
v_res_2707_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2692_, v_collapsed_boxed_2705_, v_tag_2694_, v_opts_2695_, v_clsEnabled_boxed_2706_, v_oldTraces_2697_, v_msg_2698_, v_resStartStop_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec_ref(v_opts_2695_);
return v_res_2707_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2708_; double v___x_2709_; 
v___x_2708_ = lean_unsigned_to_nat(1000000000u);
v___x_2709_ = lean_float_of_nat(v___x_2708_);
return v___x_2709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2712_ = l_Lean_stringToMessageData(v___x_2711_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_toConstantVal_2719_; lean_object* v_options_2720_; lean_object* v_name_2721_; lean_object* v_levelParams_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2933_; 
v_toConstantVal_2719_ = lean_ctor_get(v_ctorVal_2713_, 0);
lean_inc_ref(v_toConstantVal_2719_);
v_options_2720_ = lean_ctor_get(v_a_2716_, 2);
v_name_2721_ = lean_ctor_get(v_toConstantVal_2719_, 0);
v_levelParams_2722_ = lean_ctor_get(v_toConstantVal_2719_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_toConstantVal_2719_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; 
v_unused_2934_ = lean_ctor_get(v_toConstantVal_2719_, 2);
lean_dec(v_unused_2934_);
v___x_2724_ = v_toConstantVal_2719_;
v_isShared_2725_ = v_isSharedCheck_2933_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_levelParams_2722_);
lean_inc(v_name_2721_);
lean_dec(v_toConstantVal_2719_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2933_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_inheritedTraceOptions_2726_; uint8_t v_hasTrace_2727_; lean_object* v_name_2728_; 
v_inheritedTraceOptions_2726_ = lean_ctor_get(v_a_2716_, 13);
v_hasTrace_2727_ = lean_ctor_get_uint8(v_options_2720_, sizeof(void*)*1);
lean_inc(v_name_2721_);
v_name_2728_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2721_);
if (v_hasTrace_2727_ == 0)
{
lean_object* v___x_2729_; 
v___x_2729_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2767_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2767_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2767_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
if (lean_obj_tag(v_a_2730_) == 1)
{
lean_object* v_val_2734_; lean_object* v___x_2735_; 
lean_del_object(v___x_2732_);
v_val_2734_ = lean_ctor_get(v_a_2730_, 0);
lean_inc_n(v_val_2734_, 2);
lean_dec_ref_known(v_a_2730_, 1);
v___x_2735_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2721_, v_val_2734_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2737_; lean_object* v_a_2738_; lean_object* v___x_2739_; lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2754_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2734_, v_a_2715_);
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref(v___x_2737_);
v___x_2739_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2736_, v_a_2715_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
lean_inc(v_name_2728_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 2, v_a_2738_);
lean_ctor_set(v___x_2724_, 0, v_name_2728_);
v___x_2745_ = v___x_2724_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_name_2728_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_levelParams_2722_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v_a_2738_);
v___x_2745_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2747_, 0, v_name_2728_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2745_);
lean_ctor_set(v___x_2748_, 1, v_a_2740_);
lean_ctor_set(v___x_2748_, 2, v___x_2747_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set_tag(v___x_2742_, 2);
lean_ctor_set(v___x_2742_, 0, v___x_2748_);
v___x_2750_ = v___x_2742_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_addDecl(v___x_2750_, v_hasTrace_2727_, v_a_2716_, v_a_2717_);
return v___x_2751_;
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_val_2734_);
lean_dec(v_name_2728_);
lean_del_object(v___x_2724_);
lean_dec(v_levelParams_2722_);
v_a_2755_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2735_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2735_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
lean_dec(v_a_2730_);
lean_dec(v_name_2728_);
lean_del_object(v___x_2724_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v___x_2763_ = lean_box(0);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2763_);
v___x_2765_ = v___x_2732_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_name_2728_);
lean_del_object(v___x_2724_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v_a_2768_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2729_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2729_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v___f_2776_; lean_object* v_cls_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v_a_2784_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v_a_2796_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v_a_2801_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v_a_2812_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v_a_2827_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v_a_2832_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; 
lean_inc(v_name_2728_);
v___f_2776_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2776_, 0, v_name_2728_);
v_cls_2777_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2778_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2779_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2726_, v_options_2720_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = l_Lean_trace_profiler;
v___x_2876_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2720_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
lean_dec_ref(v___f_2776_);
v___x_2877_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2924_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_2924_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2924_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
if (lean_obj_tag(v_a_2878_) == 1)
{
lean_object* v_val_2882_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; 
lean_del_object(v___x_2880_);
v_val_2882_ = lean_ctor_get(v_a_2878_, 0);
lean_inc(v_val_2882_);
lean_dec_ref_known(v_a_2878_, 1);
if (v___x_2780_ == 0)
{
v___y_2884_ = v_a_2714_;
v___y_2885_ = v_a_2715_;
v___y_2886_ = v_a_2716_;
v___y_2887_ = v_a_2717_;
goto v___jp_2883_;
}
else
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2916_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2882_);
v___x_2917_ = l_Lean_MessageData_ofExpr(v_val_2882_);
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2777_, v___x_2918_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_dec_ref_known(v___x_2919_, 1);
v___y_2884_ = v_a_2714_;
v___y_2885_ = v_a_2715_;
v___y_2886_ = v_a_2716_;
v___y_2887_ = v_a_2717_;
goto v___jp_2883_;
}
else
{
lean_dec(v_val_2882_);
lean_dec(v_name_2728_);
lean_del_object(v___x_2724_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
return v___x_2919_;
}
}
v___jp_2883_:
{
lean_object* v___x_2888_; 
lean_inc(v_val_2882_);
v___x_2888_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2721_, v_val_2882_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2907_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
v___x_2890_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2882_, v___y_2885_);
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref(v___x_2890_);
v___x_2892_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2889_, v___y_2885_);
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2907_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2907_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
lean_inc(v_name_2728_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 2, v_a_2891_);
lean_ctor_set(v___x_2724_, 0, v_name_2728_);
v___x_2898_ = v___x_2724_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_name_2728_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_levelParams_2722_);
lean_ctor_set(v_reuseFailAlloc_2906_, 2, v_a_2891_);
v___x_2898_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2899_ = lean_box(0);
v___x_2900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2900_, 0, v_name_2728_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2898_);
lean_ctor_set(v___x_2901_, 1, v_a_2893_);
lean_ctor_set(v___x_2901_, 2, v___x_2900_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set_tag(v___x_2895_, 2);
lean_ctor_set(v___x_2895_, 0, v___x_2901_);
v___x_2903_ = v___x_2895_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Lean_addDecl(v___x_2903_, v___x_2876_, v___y_2886_, v___y_2887_);
return v___x_2904_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_val_2882_);
lean_dec(v_name_2728_);
lean_del_object(v___x_2724_);
lean_dec(v_levelParams_2722_);
v_a_2908_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2888_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2888_);
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
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2922_; 
lean_dec(v_a_2878_);
lean_dec(v_name_2728_);
lean_del_object(v___x_2724_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v___x_2920_ = lean_box(0);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2920_);
v___x_2922_ = v___x_2880_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_name_2728_);
lean_del_object(v___x_2724_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v_a_2925_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2877_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2877_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_del_object(v___x_2724_);
goto v___jp_2840_;
}
}
else
{
lean_del_object(v___x_2724_);
goto v___jp_2840_;
}
v___jp_2781_:
{
lean_object* v___x_2785_; double v___x_2786_; double v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2785_ = lean_io_get_num_heartbeats();
v___x_2786_ = lean_float_of_nat(v___y_2783_);
v___x_2787_ = lean_float_of_nat(v___x_2785_);
v___x_2788_ = lean_box_float(v___x_2786_);
v___x_2789_ = lean_box_float(v___x_2787_);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v_a_2784_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2777_, v_hasTrace_2727_, v___x_2778_, v_options_2720_, v___x_2780_, v___y_2782_, v___f_2776_, v___x_2791_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
return v___x_2792_;
}
v___jp_2793_:
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v_a_2796_);
v___y_2782_ = v___y_2794_;
v___y_2783_ = v___y_2795_;
v_a_2784_ = v___x_2797_;
goto v___jp_2781_;
}
v___jp_2798_:
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_a_2801_);
v___y_2782_ = v___y_2799_;
v___y_2783_ = v___y_2800_;
v_a_2784_ = v___x_2802_;
goto v___jp_2781_;
}
v___jp_2803_:
{
if (lean_obj_tag(v___y_2806_) == 0)
{
lean_object* v_a_2807_; 
v_a_2807_ = lean_ctor_get(v___y_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___y_2806_, 1);
v___y_2799_ = v___y_2804_;
v___y_2800_ = v___y_2805_;
v_a_2801_ = v_a_2807_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2808_; 
v_a_2808_ = lean_ctor_get(v___y_2806_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___y_2806_, 1);
v___y_2794_ = v___y_2804_;
v___y_2795_ = v___y_2805_;
v_a_2796_ = v_a_2808_;
goto v___jp_2793_;
}
}
v___jp_2809_:
{
lean_object* v___x_2813_; double v___x_2814_; double v___x_2815_; double v___x_2816_; double v___x_2817_; double v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2813_ = lean_io_mono_nanos_now();
v___x_2814_ = lean_float_of_nat(v___y_2810_);
v___x_2815_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2816_ = lean_float_div(v___x_2814_, v___x_2815_);
v___x_2817_ = lean_float_of_nat(v___x_2813_);
v___x_2818_ = lean_float_div(v___x_2817_, v___x_2815_);
v___x_2819_ = lean_box_float(v___x_2816_);
v___x_2820_ = lean_box_float(v___x_2818_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2812_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2777_, v_hasTrace_2727_, v___x_2778_, v_options_2720_, v___x_2780_, v___y_2811_, v___f_2776_, v___x_2822_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
return v___x_2823_;
}
v___jp_2824_:
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2828_, 0, v_a_2827_);
v___y_2810_ = v___y_2825_;
v___y_2811_ = v___y_2826_;
v_a_2812_ = v___x_2828_;
goto v___jp_2809_;
}
v___jp_2829_:
{
lean_object* v___x_2833_; 
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2832_);
v___y_2810_ = v___y_2830_;
v___y_2811_ = v___y_2831_;
v_a_2812_ = v___x_2833_;
goto v___jp_2809_;
}
v___jp_2834_:
{
if (lean_obj_tag(v___y_2837_) == 0)
{
lean_object* v_a_2838_; 
v_a_2838_ = lean_ctor_get(v___y_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___y_2837_, 1);
v___y_2825_ = v___y_2835_;
v___y_2826_ = v___y_2836_;
v_a_2827_ = v_a_2838_;
goto v___jp_2824_;
}
else
{
lean_object* v_a_2839_; 
v_a_2839_ = lean_ctor_get(v___y_2837_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___y_2837_, 1);
v___y_2830_ = v___y_2835_;
v___y_2831_ = v___y_2836_;
v_a_2832_ = v_a_2839_;
goto v___jp_2829_;
}
}
v___jp_2840_:
{
lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2841_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2717_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2844_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2720_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_io_mono_nanos_now();
v___x_2846_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
if (lean_obj_tag(v_a_2847_) == 1)
{
if (v___x_2780_ == 0)
{
lean_object* v_val_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_val_2848_ = lean_ctor_get(v_a_2847_, 0);
lean_inc(v_val_2848_);
lean_dec_ref_known(v_a_2847_, 1);
v___x_2849_ = lean_box(0);
v___x_2850_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2721_, v_val_2848_, v_name_2728_, v_levelParams_2722_, v___x_2844_, v___x_2849_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
v___y_2835_ = v___x_2845_;
v___y_2836_ = v_a_2842_;
v___y_2837_ = v___x_2850_;
goto v___jp_2834_;
}
else
{
lean_object* v_val_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_val_2851_ = lean_ctor_get(v_a_2847_, 0);
lean_inc_n(v_val_2851_, 2);
lean_dec_ref_known(v_a_2847_, 1);
v___x_2852_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2853_ = l_Lean_MessageData_ofExpr(v_val_2851_);
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2777_, v___x_2854_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2721_, v_val_2851_, v_name_2728_, v_levelParams_2722_, v___x_2844_, v_a_2856_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
v___y_2835_ = v___x_2845_;
v___y_2836_ = v_a_2842_;
v___y_2837_ = v___x_2857_;
goto v___jp_2834_;
}
else
{
lean_dec(v_val_2851_);
lean_dec(v_name_2728_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v___y_2835_ = v___x_2845_;
v___y_2836_ = v_a_2842_;
v___y_2837_ = v___x_2855_;
goto v___jp_2834_;
}
}
}
else
{
lean_object* v___x_2858_; 
lean_dec(v_a_2847_);
lean_dec(v_name_2728_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v___x_2858_ = lean_box(0);
v___y_2825_ = v___x_2845_;
v___y_2826_ = v_a_2842_;
v_a_2827_ = v___x_2858_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_a_2859_; 
lean_dec(v_name_2728_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v_a_2859_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2846_, 1);
v___y_2830_ = v___x_2845_;
v___y_2831_ = v_a_2842_;
v_a_2832_ = v_a_2859_;
goto v___jp_2829_;
}
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_io_get_num_heartbeats();
v___x_2861_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
if (lean_obj_tag(v_a_2862_) == 1)
{
if (v___x_2780_ == 0)
{
lean_object* v_val_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_val_2863_ = lean_ctor_get(v_a_2862_, 0);
lean_inc(v_val_2863_);
lean_dec_ref_known(v_a_2862_, 1);
v___x_2864_ = lean_box(0);
v___x_2865_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2721_, v_val_2863_, v_name_2728_, v_levelParams_2722_, v___x_2864_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
v___y_2804_ = v_a_2842_;
v___y_2805_ = v___x_2860_;
v___y_2806_ = v___x_2865_;
goto v___jp_2803_;
}
else
{
lean_object* v_val_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_val_2866_ = lean_ctor_get(v_a_2862_, 0);
lean_inc_n(v_val_2866_, 2);
lean_dec_ref_known(v_a_2862_, 1);
v___x_2867_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2868_ = l_Lean_MessageData_ofExpr(v_val_2866_);
v___x_2869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2777_, v___x_2869_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2872_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
v___x_2872_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2721_, v_val_2866_, v_name_2728_, v_levelParams_2722_, v_a_2871_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_);
v___y_2804_ = v_a_2842_;
v___y_2805_ = v___x_2860_;
v___y_2806_ = v___x_2872_;
goto v___jp_2803_;
}
else
{
lean_dec(v_val_2866_);
lean_dec(v_name_2728_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v___y_2804_ = v_a_2842_;
v___y_2805_ = v___x_2860_;
v___y_2806_ = v___x_2870_;
goto v___jp_2803_;
}
}
}
else
{
lean_object* v___x_2873_; 
lean_dec(v_a_2862_);
lean_dec(v_name_2728_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v___x_2873_ = lean_box(0);
v___y_2799_ = v_a_2842_;
v___y_2800_ = v___x_2860_;
v_a_2801_ = v___x_2873_;
goto v___jp_2798_;
}
}
else
{
lean_object* v_a_2874_; 
lean_dec(v_name_2728_);
lean_dec(v_levelParams_2722_);
lean_dec(v_name_2721_);
v_a_2874_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2861_, 1);
v___y_2794_ = v_a_2842_;
v___y_2795_ = v___x_2860_;
v_a_2796_ = v_a_2874_;
goto v___jp_2793_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_00_u03b1_2942_, lean_object* v_x_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2943_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2950_, lean_object* v_x_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_00_u03b1_2950_, v_x_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2961_){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2963_ = l_Lean_Name_append(v_ctorName_2961_, v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
uint8_t v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = 1;
v___x_2971_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2964_, v___x_2970_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2979_, lean_object* v_t_2980_, lean_object* v_acc_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2980_, v_a_2982_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3008_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2987_ = v___x_2984_;
v_isShared_2988_ = v_isSharedCheck_3008_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3008_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
v___x_2994_ = l_Lean_Expr_cleanupAnnotations(v_a_2985_);
v___x_2995_ = l_Lean_Expr_isApp(v___x_2994_);
if (v___x_2995_ == 0)
{
lean_dec_ref(v___x_2994_);
goto v___jp_2989_;
}
else
{
lean_object* v_arg_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; 
v_arg_2996_ = lean_ctor_get(v___x_2994_, 1);
lean_inc_ref(v_arg_2996_);
v___x_2997_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2994_);
v___x_2998_ = l_Lean_Expr_isApp(v___x_2997_);
if (v___x_2998_ == 0)
{
lean_dec_ref(v___x_2997_);
lean_dec_ref(v_arg_2996_);
goto v___jp_2989_;
}
else
{
lean_object* v_arg_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
v_arg_2999_ = lean_ctor_get(v___x_2997_, 1);
lean_inc_ref(v_arg_2999_);
v___x_3000_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2997_);
v___x_3001_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3002_ = l_Lean_Expr_isConstOf(v___x_3000_, v___x_3001_);
lean_dec_ref(v___x_3000_);
if (v___x_3002_ == 0)
{
lean_dec_ref(v_arg_2999_);
lean_dec_ref(v_arg_2996_);
goto v___jp_2989_;
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
lean_del_object(v___x_2987_);
v___x_3003_ = lean_unsigned_to_nat(0u);
v___x_3004_ = l_Lean_mkProj(v___x_3001_, v___x_3003_, v_e_2979_);
lean_inc_ref(v___x_3004_);
v___x_3005_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_3004_, v_arg_2999_, v_acc_2981_, v_a_2982_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v_e_2979_ = v___x_3004_;
v_t_2980_ = v_arg_2996_;
v_acc_2981_ = v_a_3006_;
goto _start;
}
else
{
lean_dec_ref(v___x_3004_);
lean_dec_ref(v_arg_2996_);
return v___x_3005_;
}
}
}
}
v___jp_2989_:
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2990_ = lean_array_push(v_acc_2981_, v_e_2979_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_2990_);
v___x_2992_ = v___x_2987_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v_acc_2981_);
lean_dec_ref(v_e_2979_);
v_a_3009_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2984_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2984_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_3017_, lean_object* v_t_3018_, lean_object* v_acc_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3017_, v_t_3018_, v_acc_3019_, v_a_3020_);
lean_dec(v_a_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_3023_, lean_object* v_t_3024_, lean_object* v_acc_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3023_, v_t_3024_, v_acc_3025_, v_a_3027_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3032_, lean_object* v_t_3033_, lean_object* v_acc_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3032_, v_t_3033_, v_acc_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3047_; 
lean_inc(v_a_3045_);
lean_inc_ref(v_a_3044_);
lean_inc(v_a_3043_);
lean_inc_ref(v_a_3042_);
lean_inc_ref(v_e_3041_);
v___x_3047_ = lean_infer_type(v_e_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___x_3049_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3050_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3041_, v_a_3048_, v___x_3049_, v_a_3043_);
return v___x_3050_;
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v_e_3041_);
v_a_3051_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3047_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3047_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3066_, lean_object* v_x_3067_, lean_object* v_x_3068_, lean_object* v_x_3069_){
_start:
{
lean_object* v_ks_3070_; lean_object* v_vs_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3095_; 
v_ks_3070_ = lean_ctor_get(v_x_3066_, 0);
v_vs_3071_ = lean_ctor_get(v_x_3066_, 1);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_x_3066_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3073_ = v_x_3066_;
v_isShared_3074_ = v_isSharedCheck_3095_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_vs_3071_);
lean_inc(v_ks_3070_);
lean_dec(v_x_3066_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3095_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; uint8_t v___x_3076_; 
v___x_3075_ = lean_array_get_size(v_ks_3070_);
v___x_3076_ = lean_nat_dec_lt(v_x_3067_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
lean_dec(v_x_3067_);
v___x_3077_ = lean_array_push(v_ks_3070_, v_x_3068_);
v___x_3078_ = lean_array_push(v_vs_3071_, v_x_3069_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 1, v___x_3078_);
lean_ctor_set(v___x_3073_, 0, v___x_3077_);
v___x_3080_ = v___x_3073_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
else
{
lean_object* v_k_x27_3082_; uint8_t v___x_3083_; 
v_k_x27_3082_ = lean_array_fget_borrowed(v_ks_3070_, v_x_3067_);
v___x_3083_ = l_Lean_instBEqMVarId_beq(v_x_3068_, v_k_x27_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3085_; 
if (v_isShared_3074_ == 0)
{
v___x_3085_ = v___x_3073_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_ks_3070_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_vs_3071_);
v___x_3085_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_unsigned_to_nat(1u);
v___x_3087_ = lean_nat_add(v_x_3067_, v___x_3086_);
lean_dec(v_x_3067_);
v_x_3066_ = v___x_3085_;
v_x_3067_ = v___x_3087_;
goto _start;
}
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3090_ = lean_array_fset(v_ks_3070_, v_x_3067_, v_x_3068_);
v___x_3091_ = lean_array_fset(v_vs_3071_, v_x_3067_, v_x_3069_);
lean_dec(v_x_3067_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 1, v___x_3091_);
lean_ctor_set(v___x_3073_, 0, v___x_3090_);
v___x_3093_ = v___x_3073_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3096_, lean_object* v_k_3097_, lean_object* v_v_3098_){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3096_, v___x_3099_, v_k_3097_, v_v_3098_);
return v___x_3100_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3102_, size_t v_x_3103_, size_t v_x_3104_, lean_object* v_x_3105_, lean_object* v_x_3106_){
_start:
{
if (lean_obj_tag(v_x_3102_) == 0)
{
lean_object* v_es_3107_; size_t v___x_3108_; size_t v___x_3109_; lean_object* v_j_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v_es_3107_ = lean_ctor_get(v_x_3102_, 0);
v___x_3108_ = ((size_t)31ULL);
v___x_3109_ = lean_usize_land(v_x_3103_, v___x_3108_);
v_j_3110_ = lean_usize_to_nat(v___x_3109_);
v___x_3111_ = lean_array_get_size(v_es_3107_);
v___x_3112_ = lean_nat_dec_lt(v_j_3110_, v___x_3111_);
if (v___x_3112_ == 0)
{
lean_dec(v_j_3110_);
lean_dec(v_x_3106_);
lean_dec(v_x_3105_);
return v_x_3102_;
}
else
{
lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3151_; 
lean_inc_ref(v_es_3107_);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_x_3102_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_x_3102_, 0);
lean_dec(v_unused_3152_);
v___x_3114_ = v_x_3102_;
v_isShared_3115_ = v_isSharedCheck_3151_;
goto v_resetjp_3113_;
}
else
{
lean_dec(v_x_3102_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3151_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v_v_3116_; lean_object* v___x_3117_; lean_object* v_xs_x27_3118_; lean_object* v___y_3120_; 
v_v_3116_ = lean_array_fget(v_es_3107_, v_j_3110_);
v___x_3117_ = lean_box(0);
v_xs_x27_3118_ = lean_array_fset(v_es_3107_, v_j_3110_, v___x_3117_);
switch(lean_obj_tag(v_v_3116_))
{
case 0:
{
lean_object* v_key_3125_; lean_object* v_val_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3136_; 
v_key_3125_ = lean_ctor_get(v_v_3116_, 0);
v_val_3126_ = lean_ctor_get(v_v_3116_, 1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_v_3116_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3128_ = v_v_3116_;
v_isShared_3129_ = v_isSharedCheck_3136_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_val_3126_);
lean_inc(v_key_3125_);
lean_dec(v_v_3116_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3136_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
uint8_t v___x_3130_; 
v___x_3130_ = l_Lean_instBEqMVarId_beq(v_x_3105_, v_key_3125_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_del_object(v___x_3128_);
v___x_3131_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3125_, v_val_3126_, v_x_3105_, v_x_3106_);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
v___y_3120_ = v___x_3132_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3134_; 
lean_dec(v_val_3126_);
lean_dec(v_key_3125_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 1, v_x_3106_);
lean_ctor_set(v___x_3128_, 0, v_x_3105_);
v___x_3134_ = v___x_3128_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_x_3105_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_x_3106_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
v___y_3120_ = v___x_3134_;
goto v___jp_3119_;
}
}
}
}
case 1:
{
lean_object* v_node_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3149_; 
v_node_3137_ = lean_ctor_get(v_v_3116_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_v_3116_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3139_ = v_v_3116_;
v_isShared_3140_ = v_isSharedCheck_3149_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_node_3137_);
lean_dec(v_v_3116_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3149_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
size_t v___x_3141_; size_t v___x_3142_; size_t v___x_3143_; size_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3141_ = ((size_t)5ULL);
v___x_3142_ = lean_usize_shift_right(v_x_3103_, v___x_3141_);
v___x_3143_ = ((size_t)1ULL);
v___x_3144_ = lean_usize_add(v_x_3104_, v___x_3143_);
v___x_3145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3137_, v___x_3142_, v___x_3144_, v_x_3105_, v_x_3106_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3145_);
v___x_3147_ = v___x_3139_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
v___y_3120_ = v___x_3147_;
goto v___jp_3119_;
}
}
}
default: 
{
lean_object* v___x_3150_; 
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_x_3105_);
lean_ctor_set(v___x_3150_, 1, v_x_3106_);
v___y_3120_ = v___x_3150_;
goto v___jp_3119_;
}
}
v___jp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3121_ = lean_array_fset(v_xs_x27_3118_, v_j_3110_, v___y_3120_);
lean_dec(v_j_3110_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3121_);
v___x_3123_ = v___x_3114_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
else
{
lean_object* v_ks_3153_; lean_object* v_vs_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3174_; 
v_ks_3153_ = lean_ctor_get(v_x_3102_, 0);
v_vs_3154_ = lean_ctor_get(v_x_3102_, 1);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_x_3102_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3156_ = v_x_3102_;
v_isShared_3157_ = v_isSharedCheck_3174_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_vs_3154_);
lean_inc(v_ks_3153_);
lean_dec(v_x_3102_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3174_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_ks_3153_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_vs_3154_);
v___x_3159_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v_newNode_3160_; uint8_t v___y_3162_; size_t v___x_3168_; uint8_t v___x_3169_; 
v_newNode_3160_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3159_, v_x_3105_, v_x_3106_);
v___x_3168_ = ((size_t)7ULL);
v___x_3169_ = lean_usize_dec_le(v___x_3168_, v_x_3104_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v___x_3170_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3160_);
v___x_3171_ = lean_unsigned_to_nat(4u);
v___x_3172_ = lean_nat_dec_lt(v___x_3170_, v___x_3171_);
lean_dec(v___x_3170_);
v___y_3162_ = v___x_3172_;
goto v___jp_3161_;
}
else
{
v___y_3162_ = v___x_3169_;
goto v___jp_3161_;
}
v___jp_3161_:
{
if (v___y_3162_ == 0)
{
lean_object* v_ks_3163_; lean_object* v_vs_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v_ks_3163_ = lean_ctor_get(v_newNode_3160_, 0);
lean_inc_ref(v_ks_3163_);
v_vs_3164_ = lean_ctor_get(v_newNode_3160_, 1);
lean_inc_ref(v_vs_3164_);
lean_dec_ref(v_newNode_3160_);
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3104_, v_ks_3163_, v_vs_3164_, v___x_3165_, v___x_3166_);
lean_dec_ref(v_vs_3164_);
lean_dec_ref(v_ks_3163_);
return v___x_3167_;
}
else
{
return v_newNode_3160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3175_, lean_object* v_keys_3176_, lean_object* v_vals_3177_, lean_object* v_i_3178_, lean_object* v_entries_3179_){
_start:
{
lean_object* v___x_3180_; uint8_t v___x_3181_; 
v___x_3180_ = lean_array_get_size(v_keys_3176_);
v___x_3181_ = lean_nat_dec_lt(v_i_3178_, v___x_3180_);
if (v___x_3181_ == 0)
{
lean_dec(v_i_3178_);
return v_entries_3179_;
}
else
{
lean_object* v_k_3182_; lean_object* v_v_3183_; uint64_t v___x_3184_; size_t v_h_3185_; size_t v___x_3186_; lean_object* v___x_3187_; size_t v___x_3188_; size_t v___x_3189_; size_t v___x_3190_; size_t v_h_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_k_3182_ = lean_array_fget_borrowed(v_keys_3176_, v_i_3178_);
v_v_3183_ = lean_array_fget_borrowed(v_vals_3177_, v_i_3178_);
v___x_3184_ = l_Lean_instHashableMVarId_hash(v_k_3182_);
v_h_3185_ = lean_uint64_to_usize(v___x_3184_);
v___x_3186_ = ((size_t)5ULL);
v___x_3187_ = lean_unsigned_to_nat(1u);
v___x_3188_ = ((size_t)1ULL);
v___x_3189_ = lean_usize_sub(v_depth_3175_, v___x_3188_);
v___x_3190_ = lean_usize_mul(v___x_3186_, v___x_3189_);
v_h_3191_ = lean_usize_shift_right(v_h_3185_, v___x_3190_);
v___x_3192_ = lean_nat_add(v_i_3178_, v___x_3187_);
lean_dec(v_i_3178_);
lean_inc(v_v_3183_);
lean_inc(v_k_3182_);
v___x_3193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3179_, v_h_3191_, v_depth_3175_, v_k_3182_, v_v_3183_);
v_i_3178_ = v___x_3192_;
v_entries_3179_ = v___x_3193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3195_, lean_object* v_keys_3196_, lean_object* v_vals_3197_, lean_object* v_i_3198_, lean_object* v_entries_3199_){
_start:
{
size_t v_depth_boxed_3200_; lean_object* v_res_3201_; 
v_depth_boxed_3200_ = lean_unbox_usize(v_depth_3195_);
lean_dec(v_depth_3195_);
v_res_3201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3200_, v_keys_3196_, v_vals_3197_, v_i_3198_, v_entries_3199_);
lean_dec_ref(v_vals_3197_);
lean_dec_ref(v_keys_3196_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3202_, lean_object* v_x_3203_, lean_object* v_x_3204_, lean_object* v_x_3205_, lean_object* v_x_3206_){
_start:
{
size_t v_x_5645__boxed_3207_; size_t v_x_5646__boxed_3208_; lean_object* v_res_3209_; 
v_x_5645__boxed_3207_ = lean_unbox_usize(v_x_3203_);
lean_dec(v_x_3203_);
v_x_5646__boxed_3208_ = lean_unbox_usize(v_x_3204_);
lean_dec(v_x_3204_);
v_res_3209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3202_, v_x_5645__boxed_3207_, v_x_5646__boxed_3208_, v_x_3205_, v_x_3206_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3210_, lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
uint64_t v___x_3213_; size_t v___x_3214_; size_t v___x_3215_; lean_object* v___x_3216_; 
v___x_3213_ = l_Lean_instHashableMVarId_hash(v_x_3211_);
v___x_3214_ = lean_uint64_to_usize(v___x_3213_);
v___x_3215_ = ((size_t)1ULL);
v___x_3216_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3210_, v___x_3214_, v___x_3215_, v_x_3211_, v_x_3212_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3217_, lean_object* v_val_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___x_3221_; lean_object* v_mctx_3222_; lean_object* v_cache_3223_; lean_object* v_zetaDeltaFVarIds_3224_; lean_object* v_postponed_3225_; lean_object* v_diag_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3254_; 
v___x_3221_ = lean_st_ref_take(v___y_3219_);
v_mctx_3222_ = lean_ctor_get(v___x_3221_, 0);
v_cache_3223_ = lean_ctor_get(v___x_3221_, 1);
v_zetaDeltaFVarIds_3224_ = lean_ctor_get(v___x_3221_, 2);
v_postponed_3225_ = lean_ctor_get(v___x_3221_, 3);
v_diag_3226_ = lean_ctor_get(v___x_3221_, 4);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3228_ = v___x_3221_;
v_isShared_3229_ = v_isSharedCheck_3254_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_diag_3226_);
lean_inc(v_postponed_3225_);
lean_inc(v_zetaDeltaFVarIds_3224_);
lean_inc(v_cache_3223_);
lean_inc(v_mctx_3222_);
lean_dec(v___x_3221_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3254_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_depth_3230_; lean_object* v_levelAssignDepth_3231_; lean_object* v_lmvarCounter_3232_; lean_object* v_mvarCounter_3233_; lean_object* v_lDecls_3234_; lean_object* v_decls_3235_; lean_object* v_userNames_3236_; lean_object* v_lAssignment_3237_; lean_object* v_eAssignment_3238_; lean_object* v_dAssignment_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3253_; 
v_depth_3230_ = lean_ctor_get(v_mctx_3222_, 0);
v_levelAssignDepth_3231_ = lean_ctor_get(v_mctx_3222_, 1);
v_lmvarCounter_3232_ = lean_ctor_get(v_mctx_3222_, 2);
v_mvarCounter_3233_ = lean_ctor_get(v_mctx_3222_, 3);
v_lDecls_3234_ = lean_ctor_get(v_mctx_3222_, 4);
v_decls_3235_ = lean_ctor_get(v_mctx_3222_, 5);
v_userNames_3236_ = lean_ctor_get(v_mctx_3222_, 6);
v_lAssignment_3237_ = lean_ctor_get(v_mctx_3222_, 7);
v_eAssignment_3238_ = lean_ctor_get(v_mctx_3222_, 8);
v_dAssignment_3239_ = lean_ctor_get(v_mctx_3222_, 9);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_mctx_3222_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3241_ = v_mctx_3222_;
v_isShared_3242_ = v_isSharedCheck_3253_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_dAssignment_3239_);
lean_inc(v_eAssignment_3238_);
lean_inc(v_lAssignment_3237_);
lean_inc(v_userNames_3236_);
lean_inc(v_decls_3235_);
lean_inc(v_lDecls_3234_);
lean_inc(v_mvarCounter_3233_);
lean_inc(v_lmvarCounter_3232_);
lean_inc(v_levelAssignDepth_3231_);
lean_inc(v_depth_3230_);
lean_dec(v_mctx_3222_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3253_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3243_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3238_, v_mvarId_3217_, v_val_3218_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 8, v___x_3243_);
v___x_3245_ = v___x_3241_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_depth_3230_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v_levelAssignDepth_3231_);
lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_lmvarCounter_3232_);
lean_ctor_set(v_reuseFailAlloc_3252_, 3, v_mvarCounter_3233_);
lean_ctor_set(v_reuseFailAlloc_3252_, 4, v_lDecls_3234_);
lean_ctor_set(v_reuseFailAlloc_3252_, 5, v_decls_3235_);
lean_ctor_set(v_reuseFailAlloc_3252_, 6, v_userNames_3236_);
lean_ctor_set(v_reuseFailAlloc_3252_, 7, v_lAssignment_3237_);
lean_ctor_set(v_reuseFailAlloc_3252_, 8, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3252_, 9, v_dAssignment_3239_);
v___x_3245_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3247_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3245_);
v___x_3247_ = v___x_3228_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v_cache_3223_);
lean_ctor_set(v_reuseFailAlloc_3251_, 2, v_zetaDeltaFVarIds_3224_);
lean_ctor_set(v_reuseFailAlloc_3251_, 3, v_postponed_3225_);
lean_ctor_set(v_reuseFailAlloc_3251_, 4, v_diag_3226_);
v___x_3247_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = lean_st_ref_set(v___y_3219_, v___x_3247_);
v___x_3249_ = lean_box(0);
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
return v___x_3250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3255_, lean_object* v_val_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3255_, v_val_3256_, v___y_3257_);
lean_dec(v___y_3257_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3260_, lean_object* v_a_3261_, lean_object* v_x_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = lean_box(0);
lean_inc(v___y_3266_);
lean_inc_ref(v___y_3265_);
lean_inc(v___y_3264_);
lean_inc_ref(v___y_3263_);
v___x_3269_ = lean_apply_7(v___f_3260_, v___x_3268_, v_a_3261_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, lean_box(0));
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3270_, lean_object* v_a_3271_, lean_object* v_x_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3270_, v_a_3271_, v_x_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
return v_res_3278_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0));
v___x_3281_ = l_Lean_stringToMessageData(v___x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3282_, lean_object* v_a_3283_, lean_object* v_x_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1);
v___x_3291_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3290_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3293_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3291_, 1);
lean_inc(v___y_3288_);
lean_inc_ref(v___y_3287_);
lean_inc(v___y_3286_);
lean_inc_ref(v___y_3285_);
v___x_3293_ = lean_apply_7(v___f_3282_, v_a_3292_, v_a_3283_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, lean_box(0));
return v___x_3293_;
}
else
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
lean_dec(v_a_3283_);
lean_dec_ref(v___f_3282_);
v_a_3294_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3291_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3291_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3302_, lean_object* v_a_3303_, lean_object* v_x_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3302_, v_a_3303_, v_x_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v_x_3304_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3311_, lean_object* v_____r_3312_, lean_object* v_mvarId_u2082_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3313_, v___x_3311_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3329_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3329_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3329_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v_snd_3324_; lean_object* v___x_3325_; lean_object* v___x_3327_; 
v_snd_3324_ = lean_ctor_get(v_a_3320_, 1);
lean_inc(v_snd_3324_);
lean_dec(v_a_3320_);
v___x_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3325_, 0, v_snd_3324_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3325_);
v___x_3327_ = v___x_3322_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_a_3330_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3319_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3319_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3338_, lean_object* v_____r_3339_, lean_object* v_mvarId_u2082_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
uint8_t v___x_5937__boxed_3346_; lean_object* v_res_3347_; 
v___x_5937__boxed_3346_ = lean_unbox(v___x_3338_);
v_res_3347_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5937__boxed_3346_, v_____r_3339_, v_mvarId_u2082_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
return v_res_3347_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = lean_box(0);
v___x_3354_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2));
v___x_3355_ = l_Lean_mkConst(v___x_3354_, v___x_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v___y_3363_; lean_object* v___x_3383_; 
lean_inc(v_a_3356_);
v___x_3383_ = l_Lean_MVarId_getType(v_a_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3443_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3443_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3443_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
if (lean_obj_tag(v_a_3384_) == 7)
{
lean_object* v_binderType_3388_; lean_object* v_body_3389_; uint8_t v___x_3390_; 
v_binderType_3388_ = lean_ctor_get(v_a_3384_, 1);
lean_inc_ref(v_binderType_3388_);
v_body_3389_ = lean_ctor_get(v_a_3384_, 2);
lean_inc_ref(v_body_3389_);
lean_dec_ref_known(v_a_3384_, 3);
v___x_3390_ = l_Lean_Expr_hasLooseBVars(v_body_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
lean_del_object(v___x_3386_);
v___x_3391_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3388_, v___y_3358_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; lean_object* v___f_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3393_ = lean_box(v___x_3390_);
v___f_3394_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3394_, 0, v___x_3393_);
v___x_3395_ = l_Lean_Expr_cleanupAnnotations(v_a_3392_);
v___x_3396_ = l_Lean_Expr_isApp(v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_dec_ref(v___x_3395_);
lean_dec_ref(v_body_3389_);
v___x_3397_ = lean_box(0);
v___x_3398_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3394_, v_a_3356_, v___x_3397_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
v___y_3363_ = v___x_3398_;
goto v___jp_3362_;
}
else
{
lean_object* v_arg_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_arg_3399_ = lean_ctor_get(v___x_3395_, 1);
lean_inc_ref(v_arg_3399_);
v___x_3400_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3395_);
v___x_3401_ = l_Lean_Expr_isApp(v___x_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v___x_3400_);
lean_dec_ref(v_arg_3399_);
lean_dec_ref(v_body_3389_);
v___x_3402_ = lean_box(0);
v___x_3403_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3394_, v_a_3356_, v___x_3402_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
v___y_3363_ = v___x_3403_;
goto v___jp_3362_;
}
else
{
lean_object* v_arg_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v_arg_3404_ = lean_ctor_get(v___x_3400_, 1);
lean_inc_ref(v_arg_3404_);
v___x_3405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3400_);
v___x_3406_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3407_ = l_Lean_Expr_isConstOf(v___x_3405_, v___x_3406_);
lean_dec_ref(v___x_3405_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_dec_ref(v_arg_3404_);
lean_dec_ref(v_arg_3399_);
lean_dec_ref(v_body_3389_);
v___x_3408_ = lean_box(0);
v___x_3409_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3394_, v_a_3356_, v___x_3408_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
v___y_3363_ = v___x_3409_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3410_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3);
v___x_3411_ = l_Lean_mkApp3(v___x_3410_, v_arg_3404_, v_arg_3399_, v_body_3389_);
v___x_3412_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3356_);
v___x_3413_ = l_Lean_MVarId_applyN(v_a_3356_, v___x_3411_, v___x_3412_, v___x_3407_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
if (lean_obj_tag(v_a_3414_) == 1)
{
lean_object* v_tail_3415_; 
v_tail_3415_ = lean_ctor_get(v_a_3414_, 1);
if (lean_obj_tag(v_tail_3415_) == 0)
{
lean_object* v_head_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec_ref(v___f_3394_);
lean_dec(v_a_3356_);
v_head_3416_ = lean_ctor_get(v_a_3414_, 0);
lean_inc(v_head_3416_);
lean_dec_ref_known(v_a_3414_, 2);
v___x_3417_ = lean_box(0);
v___x_3418_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3390_, v___x_3417_, v_head_3416_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
v___y_3363_ = v___x_3418_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3419_; 
v___x_3419_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3394_, v_a_3356_, v_a_3414_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec_ref_known(v_a_3414_, 2);
v___y_3363_ = v___x_3419_;
goto v___jp_3362_;
}
}
else
{
lean_object* v___x_3420_; 
v___x_3420_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3394_, v_a_3356_, v_a_3414_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v_a_3414_);
v___y_3363_ = v___x_3420_;
goto v___jp_3362_;
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec_ref(v___f_3394_);
lean_dec(v_a_3356_);
v_a_3421_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3413_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3413_);
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
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec_ref(v_body_3389_);
lean_dec(v_a_3356_);
v_a_3429_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3391_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3391_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
else
{
lean_object* v___x_3438_; 
lean_dec_ref(v_body_3389_);
lean_dec_ref(v_binderType_3388_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v_a_3356_);
v___x_3438_ = v___x_3386_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3356_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
else
{
lean_object* v___x_3441_; 
lean_dec(v_a_3384_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v_a_3356_);
v___x_3441_ = v___x_3386_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3356_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec(v_a_3356_);
v_a_3444_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3383_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3383_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
v___jp_3362_:
{
if (lean_obj_tag(v___y_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3374_; 
v_a_3364_ = lean_ctor_get(v___y_3363_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___y_3363_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3366_ = v___y_3363_;
v_isShared_3367_ = v_isSharedCheck_3374_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___y_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3374_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
if (lean_obj_tag(v_a_3364_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; 
v_a_3368_ = lean_ctor_get(v_a_3364_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v_a_3364_, 1);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v_a_3368_);
v___x_3370_ = v___x_3366_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
else
{
lean_object* v_a_3372_; 
lean_del_object(v___x_3366_);
v_a_3372_ = lean_ctor_get(v_a_3364_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v_a_3364_, 1);
v_a_3356_ = v_a_3372_;
goto _start;
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
v_a_3375_ = lean_ctor_get(v___y_3363_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___y_3363_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___y_3363_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___y_3363_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
return v_res_3458_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = lean_box(0);
v___x_3465_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3466_ = l_Lean_mkConst(v___x_3465_, v___x_3464_);
return v___x_3466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3473_ = l_Lean_stringToMessageData(v___x_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3474_, lean_object* v_xs_3475_, lean_object* v_type_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = lean_box(0);
v___x_3483_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3476_, v___x_3482_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v_a_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; uint8_t v___x_3489_; lean_object* v___y_3491_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v___x_3485_ = l_Lean_Expr_mvarId_x21(v_a_3484_);
v___x_3486_ = lean_box(0);
v___x_3487_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3488_ = 1;
v___x_3489_ = 0;
v___x_3502_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3503_ = lean_box(0);
v___x_3504_ = l_Lean_MVarId_apply(v___x_3485_, v___x_3487_, v___x_3502_, v___x_3503_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3504_, 1);
if (lean_obj_tag(v_a_3505_) == 1)
{
lean_object* v_tail_3519_; 
v_tail_3519_ = lean_ctor_get(v_a_3505_, 1);
lean_inc(v_tail_3519_);
if (lean_obj_tag(v_tail_3519_) == 1)
{
lean_object* v_tail_3520_; 
v_tail_3520_ = lean_ctor_get(v_tail_3519_, 1);
if (lean_obj_tag(v_tail_3520_) == 0)
{
lean_object* v_toConstantVal_3521_; lean_object* v_head_3522_; lean_object* v_head_3523_; lean_object* v_name_3524_; lean_object* v_levelParams_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_toConstantVal_3521_ = lean_ctor_get(v_ctorVal_3474_, 0);
lean_inc_ref(v_toConstantVal_3521_);
lean_dec_ref(v_ctorVal_3474_);
v_head_3522_ = lean_ctor_get(v_a_3505_, 0);
lean_inc(v_head_3522_);
lean_dec_ref_known(v_a_3505_, 2);
v_head_3523_ = lean_ctor_get(v_tail_3519_, 0);
lean_inc(v_head_3523_);
lean_dec_ref_known(v_tail_3519_, 2);
v_name_3524_ = lean_ctor_get(v_toConstantVal_3521_, 0);
lean_inc_n(v_name_3524_, 2);
v_levelParams_3525_ = lean_ctor_get(v_toConstantVal_3521_, 1);
lean_inc(v_levelParams_3525_);
lean_dec_ref(v_toConstantVal_3521_);
v___x_3526_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3524_);
v___x_3527_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3525_, v___x_3486_);
v___x_3528_ = l_Lean_mkConst(v___x_3526_, v___x_3527_);
v___x_3529_ = l_Lean_mkAppN(v___x_3528_, v_xs_3475_);
v___x_3530_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3522_, v___x_3529_, v___y_3478_);
lean_dec_ref(v___x_3530_);
v___x_3531_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3523_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = l_Lean_MVarId_refl(v_a_3532_, v___x_3488_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_dec(v_name_3524_);
v___y_3491_ = v___x_3533_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3534_; uint8_t v___y_3536_; uint8_t v___x_3539_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
v___x_3539_ = l_Lean_Exception_isInterrupt(v_a_3534_);
if (v___x_3539_ == 0)
{
uint8_t v___x_3540_; 
v___x_3540_ = l_Lean_Exception_isRuntime(v_a_3534_);
v___y_3536_ = v___x_3540_;
goto v___jp_3535_;
}
else
{
lean_dec(v_a_3534_);
v___y_3536_ = v___x_3539_;
goto v___jp_3535_;
}
v___jp_3535_:
{
if (v___y_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_dec_ref_known(v___x_3533_, 1);
v___x_3537_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3524_);
v___x_3538_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3537_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
v___y_3491_ = v___x_3538_;
goto v___jp_3490_;
}
else
{
lean_dec(v_name_3524_);
v___y_3491_ = v___x_3533_;
goto v___jp_3490_;
}
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec(v_name_3524_);
lean_dec(v_a_3484_);
v_a_3541_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3531_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3531_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3519_, 2);
lean_dec_ref_known(v_a_3505_, 2);
lean_dec(v_a_3484_);
v___y_3507_ = v___y_3477_;
v___y_3508_ = v___y_3478_;
v___y_3509_ = v___y_3479_;
v___y_3510_ = v___y_3480_;
goto v___jp_3506_;
}
}
else
{
lean_dec_ref_known(v_a_3505_, 2);
lean_dec(v_tail_3519_);
lean_dec(v_a_3484_);
v___y_3507_ = v___y_3477_;
v___y_3508_ = v___y_3478_;
v___y_3509_ = v___y_3479_;
v___y_3510_ = v___y_3480_;
goto v___jp_3506_;
}
}
else
{
lean_dec(v_a_3505_);
lean_dec(v_a_3484_);
v___y_3507_ = v___y_3477_;
v___y_3508_ = v___y_3478_;
v___y_3509_ = v___y_3479_;
v___y_3510_ = v___y_3480_;
goto v___jp_3506_;
}
v___jp_3506_:
{
lean_object* v_toConstantVal_3511_; lean_object* v_name_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_toConstantVal_3511_ = lean_ctor_get(v_ctorVal_3474_, 0);
lean_inc_ref(v_toConstantVal_3511_);
lean_dec_ref(v_ctorVal_3474_);
v_name_3512_ = lean_ctor_get(v_toConstantVal_3511_, 0);
lean_inc(v_name_3512_);
lean_dec_ref(v_toConstantVal_3511_);
v___x_3513_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3514_ = l_Lean_MessageData_ofName(v_name_3512_);
v___x_3515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3513_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3515_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
v___x_3518_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3517_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
return v___x_3518_;
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec(v_a_3484_);
lean_dec_ref(v_ctorVal_3474_);
v_a_3549_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3504_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3504_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
v___jp_3490_:
{
if (lean_obj_tag(v___y_3491_) == 0)
{
uint8_t v___x_3492_; lean_object* v___x_3493_; 
lean_dec_ref_known(v___y_3491_, 1);
v___x_3492_ = 1;
v___x_3493_ = l_Lean_Meta_mkLambdaFVars(v_xs_3475_, v_a_3484_, v___x_3489_, v___x_3488_, v___x_3489_, v___x_3488_, v___x_3492_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
return v___x_3493_;
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec(v_a_3484_);
v_a_3494_ = lean_ctor_get(v___y_3491_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___y_3491_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___y_3491_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___y_3491_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorVal_3474_);
return v___x_3483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3557_, lean_object* v_xs_3558_, lean_object* v_type_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3557_, v_xs_3558_, v_type_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v_xs_3558_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3566_, lean_object* v_targetType_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___f_3573_; uint8_t v___x_3574_; lean_object* v___x_3575_; 
v___f_3573_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3573_, 0, v_ctorVal_3566_);
v___x_3574_ = 0;
v___x_3575_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3567_, v___f_3573_, v___x_3574_, v___x_3574_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3576_, lean_object* v_targetType_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3576_, v_targetType_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3584_, lean_object* v_val_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3584_, v_val_3585_, v___y_3587_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3592_, lean_object* v_val_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3592_, v_val_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3600_, lean_object* v_a_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3608_, lean_object* v_a_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3608_, v_a_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3616_, lean_object* v_x_3617_, lean_object* v_x_3618_, lean_object* v_x_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3617_, v_x_3618_, v_x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3621_, lean_object* v_x_3622_, size_t v_x_3623_, size_t v_x_3624_, lean_object* v_x_3625_, lean_object* v_x_3626_){
_start:
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3622_, v_x_3623_, v_x_3624_, v_x_3625_, v_x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3628_, lean_object* v_x_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_, lean_object* v_x_3633_){
_start:
{
size_t v_x_6488__boxed_3634_; size_t v_x_6489__boxed_3635_; lean_object* v_res_3636_; 
v_x_6488__boxed_3634_ = lean_unbox_usize(v_x_3630_);
lean_dec(v_x_3630_);
v_x_6489__boxed_3635_ = lean_unbox_usize(v_x_3631_);
lean_dec(v_x_3631_);
v_res_3636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3628_, v_x_3629_, v_x_6488__boxed_3634_, v_x_6489__boxed_3635_, v_x_3632_, v_x_3633_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3637_, lean_object* v_n_3638_, lean_object* v_k_3639_, lean_object* v_v_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3638_, v_k_3639_, v_v_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3642_, size_t v_depth_3643_, lean_object* v_keys_3644_, lean_object* v_vals_3645_, lean_object* v_heq_3646_, lean_object* v_i_3647_, lean_object* v_entries_3648_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3643_, v_keys_3644_, v_vals_3645_, v_i_3647_, v_entries_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3650_, lean_object* v_depth_3651_, lean_object* v_keys_3652_, lean_object* v_vals_3653_, lean_object* v_heq_3654_, lean_object* v_i_3655_, lean_object* v_entries_3656_){
_start:
{
size_t v_depth_boxed_3657_; lean_object* v_res_3658_; 
v_depth_boxed_3657_ = lean_unbox_usize(v_depth_3651_);
lean_dec(v_depth_3651_);
v_res_3658_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3650_, v_depth_boxed_3657_, v_keys_3652_, v_vals_3653_, v_heq_3654_, v_i_3655_, v_entries_3656_);
lean_dec_ref(v_vals_3653_);
lean_dec_ref(v_keys_3652_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3659_, lean_object* v_x_3660_, lean_object* v_x_3661_, lean_object* v_x_3662_, lean_object* v_x_3663_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3660_, v_x_3661_, v_x_3662_, v_x_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3665_, lean_object* v_val_3666_, lean_object* v_name_3667_, lean_object* v_levelParams_3668_, uint8_t v___x_3669_, uint8_t v_hasTrace_3670_, lean_object* v_____r_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v___x_3677_; 
lean_inc_ref(v_val_3666_);
v___x_3677_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3665_, v_val_3666_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3679_; lean_object* v_a_3680_; lean_object* v___x_3681_; lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3698_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3677_, 1);
v___x_3679_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3666_, v___y_3673_);
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref(v___x_3679_);
v___x_3681_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3678_, v___y_3673_);
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3684_ = v___x_3681_;
v_isShared_3685_ = v_isSharedCheck_3698_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3681_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3698_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
lean_inc_n(v_name_3667_, 2);
v___x_3686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3686_, 0, v_name_3667_);
lean_ctor_set(v___x_3686_, 1, v_levelParams_3668_);
lean_ctor_set(v___x_3686_, 2, v_a_3680_);
v___x_3687_ = lean_box(0);
v___x_3688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3688_, 0, v_name_3667_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3686_);
lean_ctor_set(v___x_3689_, 1, v_a_3682_);
lean_ctor_set(v___x_3689_, 2, v___x_3688_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set_tag(v___x_3684_, 2);
lean_ctor_set(v___x_3684_, 0, v___x_3689_);
v___x_3691_ = v___x_3684_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_addDecl(v___x_3691_, v___x_3669_, v___y_3674_, v___y_3675_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v___x_3693_; uint8_t v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
lean_dec_ref_known(v___x_3692_, 1);
v___x_3693_ = l_Lean_Meta_simpExtension;
v___x_3694_ = 0;
v___x_3695_ = lean_unsigned_to_nat(1000u);
v___x_3696_ = l_Lean_Meta_addSimpTheorem(v___x_3693_, v_name_3667_, v_hasTrace_3670_, v___x_3669_, v___x_3694_, v___x_3695_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
return v___x_3696_;
}
else
{
lean_dec(v_name_3667_);
return v___x_3692_;
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_levelParams_3668_);
lean_dec(v_name_3667_);
lean_dec_ref(v_val_3666_);
v_a_3699_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3677_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3677_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3707_, lean_object* v_val_3708_, lean_object* v_name_3709_, lean_object* v_levelParams_3710_, lean_object* v___x_3711_, lean_object* v_hasTrace_3712_, lean_object* v_____r_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v___x_9095__boxed_3719_; uint8_t v_hasTrace_boxed_3720_; lean_object* v_res_3721_; 
v___x_9095__boxed_3719_ = lean_unbox(v___x_3711_);
v_hasTrace_boxed_3720_ = lean_unbox(v_hasTrace_3712_);
v_res_3721_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3707_, v_val_3708_, v_name_3709_, v_levelParams_3710_, v___x_9095__boxed_3719_, v_hasTrace_boxed_3720_, v_____r_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3722_, lean_object* v_val_3723_, lean_object* v_name_3724_, lean_object* v_levelParams_3725_, uint8_t v___x_3726_, lean_object* v_____r_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
lean_inc_ref(v_val_3723_);
v___x_3733_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3722_, v_val_3723_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3755_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3723_, v___y_3729_);
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref(v___x_3735_);
v___x_3737_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3734_, v___y_3729_);
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3740_ = v___x_3737_;
v_isShared_3741_ = v_isSharedCheck_3755_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3737_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3755_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_inc_n(v_name_3724_, 2);
v___x_3742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3742_, 0, v_name_3724_);
lean_ctor_set(v___x_3742_, 1, v_levelParams_3725_);
lean_ctor_set(v___x_3742_, 2, v_a_3736_);
v___x_3743_ = lean_box(0);
v___x_3744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3744_, 0, v_name_3724_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3742_);
lean_ctor_set(v___x_3745_, 1, v_a_3738_);
lean_ctor_set(v___x_3745_, 2, v___x_3744_);
if (v_isShared_3741_ == 0)
{
lean_ctor_set_tag(v___x_3740_, 2);
lean_ctor_set(v___x_3740_, 0, v___x_3745_);
v___x_3747_ = v___x_3740_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
uint8_t v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = 0;
v___x_3749_ = l_Lean_addDecl(v___x_3747_, v___x_3748_, v___y_3730_, v___y_3731_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v___x_3750_; uint8_t v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_dec_ref_known(v___x_3749_, 1);
v___x_3750_ = l_Lean_Meta_simpExtension;
v___x_3751_ = 0;
v___x_3752_ = lean_unsigned_to_nat(1000u);
v___x_3753_ = l_Lean_Meta_addSimpTheorem(v___x_3750_, v_name_3724_, v___x_3726_, v___x_3748_, v___x_3751_, v___x_3752_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
return v___x_3753_;
}
else
{
lean_dec(v_name_3724_);
return v___x_3749_;
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec(v_levelParams_3725_);
lean_dec(v_name_3724_);
lean_dec_ref(v_val_3723_);
v_a_3756_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3733_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3733_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3764_, lean_object* v_val_3765_, lean_object* v_name_3766_, lean_object* v_levelParams_3767_, lean_object* v___x_3768_, lean_object* v_____r_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
uint8_t v___x_9183__boxed_3775_; lean_object* v_res_3776_; 
v___x_9183__boxed_3775_ = lean_unbox(v___x_3768_);
v_res_3776_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3764_, v_val_3765_, v_name_3766_, v_levelParams_3767_, v___x_9183__boxed_3775_, v_____r_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_toConstantVal_3783_; lean_object* v_options_3784_; lean_object* v_name_3785_; lean_object* v_levelParams_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_4006_; 
v_toConstantVal_3783_ = lean_ctor_get(v_ctorVal_3777_, 0);
lean_inc_ref(v_toConstantVal_3783_);
v_options_3784_ = lean_ctor_get(v_a_3780_, 2);
v_name_3785_ = lean_ctor_get(v_toConstantVal_3783_, 0);
v_levelParams_3786_ = lean_ctor_get(v_toConstantVal_3783_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_toConstantVal_3783_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; 
v_unused_4007_ = lean_ctor_get(v_toConstantVal_3783_, 2);
lean_dec(v_unused_4007_);
v___x_3788_ = v_toConstantVal_3783_;
v_isShared_3789_ = v_isSharedCheck_4006_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_levelParams_3786_);
lean_inc(v_name_3785_);
lean_dec(v_toConstantVal_3783_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_4006_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v_inheritedTraceOptions_3790_; uint8_t v_hasTrace_3791_; lean_object* v_name_3792_; 
v_inheritedTraceOptions_3790_ = lean_ctor_get(v_a_3780_, 13);
v_hasTrace_3791_ = lean_ctor_get_uint8(v_options_3784_, sizeof(void*)*1);
v_name_3792_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3785_);
if (v_hasTrace_3791_ == 0)
{
lean_object* v___x_3793_; 
lean_inc_ref(v_ctorVal_3777_);
v___x_3793_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3836_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3836_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3836_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
if (lean_obj_tag(v_a_3794_) == 1)
{
lean_object* v_val_3798_; lean_object* v___x_3799_; 
lean_del_object(v___x_3796_);
v_val_3798_ = lean_ctor_get(v_a_3794_, 0);
lean_inc_n(v_val_3798_, 2);
lean_dec_ref_known(v_a_3794_, 1);
v___x_3799_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3777_, v_val_3798_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3801_; lean_object* v_a_3802_; lean_object* v___x_3803_; lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3823_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v___x_3799_, 1);
v___x_3801_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3798_, v_a_3779_);
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref(v___x_3801_);
v___x_3803_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3800_, v_a_3779_);
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3823_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3823_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
lean_inc(v_name_3792_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 2, v_a_3802_);
lean_ctor_set(v___x_3788_, 0, v_name_3792_);
v___x_3809_ = v___x_3788_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_name_3792_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_levelParams_3786_);
lean_ctor_set(v_reuseFailAlloc_3822_, 2, v_a_3802_);
v___x_3809_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3810_ = lean_box(0);
lean_inc(v_name_3792_);
v___x_3811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3811_, 0, v_name_3792_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3809_);
lean_ctor_set(v___x_3812_, 1, v_a_3804_);
lean_ctor_set(v___x_3812_, 2, v___x_3811_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set_tag(v___x_3806_, 2);
lean_ctor_set(v___x_3806_, 0, v___x_3812_);
v___x_3814_ = v___x_3806_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Lean_addDecl(v___x_3814_, v_hasTrace_3791_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v___x_3816_; uint8_t v___x_3817_; uint8_t v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
lean_dec_ref_known(v___x_3815_, 1);
v___x_3816_ = l_Lean_Meta_simpExtension;
v___x_3817_ = 1;
v___x_3818_ = 0;
v___x_3819_ = lean_unsigned_to_nat(1000u);
v___x_3820_ = l_Lean_Meta_addSimpTheorem(v___x_3816_, v_name_3792_, v___x_3817_, v_hasTrace_3791_, v___x_3818_, v___x_3819_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
return v___x_3820_;
}
else
{
lean_dec(v_name_3792_);
return v___x_3815_;
}
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v_val_3798_);
lean_dec(v_name_3792_);
lean_del_object(v___x_3788_);
lean_dec(v_levelParams_3786_);
v_a_3824_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3799_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3799_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_dec(v_a_3794_);
lean_dec(v_name_3792_);
lean_del_object(v___x_3788_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v___x_3832_ = lean_box(0);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3832_);
v___x_3834_ = v___x_3796_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec(v_name_3792_);
lean_del_object(v___x_3788_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v_a_3837_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3793_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3793_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
else
{
lean_object* v___f_3845_; lean_object* v_cls_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v_a_3853_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v_a_3865_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v_a_3870_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v_a_3881_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v_a_3896_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v_a_3901_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; 
lean_inc(v_name_3792_);
v___f_3845_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3845_, 0, v_name_3792_);
v_cls_3846_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3847_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3848_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3849_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3790_, v_options_3784_, v___x_3848_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3944_ = l_Lean_trace_profiler;
v___x_3945_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3784_, v___x_3944_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3946_; 
lean_dec_ref(v___f_3845_);
lean_inc_ref(v_ctorVal_3777_);
v___x_3946_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3997_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3949_ = v___x_3946_;
v_isShared_3950_ = v_isSharedCheck_3997_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3946_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3997_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
if (lean_obj_tag(v_a_3947_) == 1)
{
lean_object* v_val_3951_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; 
lean_del_object(v___x_3949_);
v_val_3951_ = lean_ctor_get(v_a_3947_, 0);
lean_inc(v_val_3951_);
lean_dec_ref_known(v_a_3947_, 1);
if (v___x_3849_ == 0)
{
v___y_3953_ = v_a_3778_;
v___y_3954_ = v_a_3779_;
v___y_3955_ = v_a_3780_;
v___y_3956_ = v_a_3781_;
goto v___jp_3952_;
}
else
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3989_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3951_);
v___x_3990_ = l_Lean_MessageData_ofExpr(v_val_3951_);
v___x_3991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3989_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3846_, v___x_3991_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_dec_ref_known(v___x_3992_, 1);
v___y_3953_ = v_a_3778_;
v___y_3954_ = v_a_3779_;
v___y_3955_ = v_a_3780_;
v___y_3956_ = v_a_3781_;
goto v___jp_3952_;
}
else
{
lean_dec(v_val_3951_);
lean_dec(v_name_3792_);
lean_del_object(v___x_3788_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
return v___x_3992_;
}
}
v___jp_3952_:
{
lean_object* v___x_3957_; 
lean_inc(v_val_3951_);
v___x_3957_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3777_, v_val_3951_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3959_; lean_object* v_a_3960_; lean_object* v___x_3961_; lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3980_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3951_, v___y_3954_);
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref(v___x_3959_);
v___x_3961_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3958_, v___y_3954_);
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3964_ = v___x_3961_;
v_isShared_3965_ = v_isSharedCheck_3980_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3961_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3980_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
lean_inc(v_name_3792_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 2, v_a_3960_);
lean_ctor_set(v___x_3788_, 0, v_name_3792_);
v___x_3967_ = v___x_3788_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_name_3792_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_levelParams_3786_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_a_3960_);
v___x_3967_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3972_; 
v___x_3968_ = lean_box(0);
lean_inc(v_name_3792_);
v___x_3969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3969_, 0, v_name_3792_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3967_);
lean_ctor_set(v___x_3970_, 1, v_a_3962_);
lean_ctor_set(v___x_3970_, 2, v___x_3969_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set_tag(v___x_3964_, 2);
lean_ctor_set(v___x_3964_, 0, v___x_3970_);
v___x_3972_ = v___x_3964_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_addDecl(v___x_3972_, v___x_3945_, v___y_3955_, v___y_3956_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v___x_3974_; uint8_t v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_dec_ref_known(v___x_3973_, 1);
v___x_3974_ = l_Lean_Meta_simpExtension;
v___x_3975_ = 0;
v___x_3976_ = lean_unsigned_to_nat(1000u);
v___x_3977_ = l_Lean_Meta_addSimpTheorem(v___x_3974_, v_name_3792_, v_hasTrace_3791_, v___x_3945_, v___x_3975_, v___x_3976_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
return v___x_3977_;
}
else
{
lean_dec(v_name_3792_);
return v___x_3973_;
}
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec(v_val_3951_);
lean_dec(v_name_3792_);
lean_del_object(v___x_3788_);
lean_dec(v_levelParams_3786_);
v_a_3981_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3957_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3957_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3995_; 
lean_dec(v_a_3947_);
lean_dec(v_name_3792_);
lean_del_object(v___x_3788_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v___x_3993_ = lean_box(0);
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 0, v___x_3993_);
v___x_3995_ = v___x_3949_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec(v_name_3792_);
lean_del_object(v___x_3788_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v_a_3998_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3946_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3946_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
lean_del_object(v___x_3788_);
goto v___jp_3909_;
}
}
else
{
lean_del_object(v___x_3788_);
goto v___jp_3909_;
}
v___jp_3850_:
{
lean_object* v___x_3854_; double v___x_3855_; double v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3854_ = lean_io_get_num_heartbeats();
v___x_3855_ = lean_float_of_nat(v___y_3852_);
v___x_3856_ = lean_float_of_nat(v___x_3854_);
v___x_3857_ = lean_box_float(v___x_3855_);
v___x_3858_ = lean_box_float(v___x_3856_);
v___x_3859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3857_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3860_, 0, v_a_3853_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3846_, v_hasTrace_3791_, v___x_3847_, v_options_3784_, v___x_3849_, v___y_3851_, v___f_3845_, v___x_3860_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
return v___x_3861_;
}
v___jp_3862_:
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3866_, 0, v_a_3865_);
v___y_3851_ = v___y_3863_;
v___y_3852_ = v___y_3864_;
v_a_3853_ = v___x_3866_;
goto v___jp_3850_;
}
v___jp_3867_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3871_, 0, v_a_3870_);
v___y_3851_ = v___y_3868_;
v___y_3852_ = v___y_3869_;
v_a_3853_ = v___x_3871_;
goto v___jp_3850_;
}
v___jp_3872_:
{
if (lean_obj_tag(v___y_3875_) == 0)
{
lean_object* v_a_3876_; 
v_a_3876_ = lean_ctor_get(v___y_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___y_3875_, 1);
v___y_3868_ = v___y_3873_;
v___y_3869_ = v___y_3874_;
v_a_3870_ = v_a_3876_;
goto v___jp_3867_;
}
else
{
lean_object* v_a_3877_; 
v_a_3877_ = lean_ctor_get(v___y_3875_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___y_3875_, 1);
v___y_3863_ = v___y_3873_;
v___y_3864_ = v___y_3874_;
v_a_3865_ = v_a_3877_;
goto v___jp_3862_;
}
}
v___jp_3878_:
{
lean_object* v___x_3882_; double v___x_3883_; double v___x_3884_; double v___x_3885_; double v___x_3886_; double v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3882_ = lean_io_mono_nanos_now();
v___x_3883_ = lean_float_of_nat(v___y_3879_);
v___x_3884_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3885_ = lean_float_div(v___x_3883_, v___x_3884_);
v___x_3886_ = lean_float_of_nat(v___x_3882_);
v___x_3887_ = lean_float_div(v___x_3886_, v___x_3884_);
v___x_3888_ = lean_box_float(v___x_3885_);
v___x_3889_ = lean_box_float(v___x_3887_);
v___x_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3891_, 0, v_a_3881_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3846_, v_hasTrace_3791_, v___x_3847_, v_options_3784_, v___x_3849_, v___y_3880_, v___f_3845_, v___x_3891_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
return v___x_3892_;
}
v___jp_3893_:
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3897_, 0, v_a_3896_);
v___y_3879_ = v___y_3894_;
v___y_3880_ = v___y_3895_;
v_a_3881_ = v___x_3897_;
goto v___jp_3878_;
}
v___jp_3898_:
{
lean_object* v___x_3902_; 
v___x_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3902_, 0, v_a_3901_);
v___y_3879_ = v___y_3899_;
v___y_3880_ = v___y_3900_;
v_a_3881_ = v___x_3902_;
goto v___jp_3878_;
}
v___jp_3903_:
{
if (lean_obj_tag(v___y_3906_) == 0)
{
lean_object* v_a_3907_; 
v_a_3907_ = lean_ctor_get(v___y_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___y_3906_, 1);
v___y_3894_ = v___y_3904_;
v___y_3895_ = v___y_3905_;
v_a_3896_ = v_a_3907_;
goto v___jp_3893_;
}
else
{
lean_object* v_a_3908_; 
v_a_3908_ = lean_ctor_get(v___y_3906_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___y_3906_, 1);
v___y_3899_ = v___y_3904_;
v___y_3900_ = v___y_3905_;
v_a_3901_ = v_a_3908_;
goto v___jp_3898_;
}
}
v___jp_3909_:
{
lean_object* v___x_3910_; lean_object* v_a_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; 
v___x_3910_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3781_);
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref(v___x_3910_);
v___x_3912_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3913_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3784_, v___x_3912_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3777_);
v___x_3915_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
if (lean_obj_tag(v_a_3916_) == 1)
{
if (v___x_3849_ == 0)
{
lean_object* v_val_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_val_3917_ = lean_ctor_get(v_a_3916_, 0);
lean_inc(v_val_3917_);
lean_dec_ref_known(v_a_3916_, 1);
v___x_3918_ = lean_box(0);
v___x_3919_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3777_, v_val_3917_, v_name_3792_, v_levelParams_3786_, v___x_3913_, v_hasTrace_3791_, v___x_3918_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
v___y_3904_ = v___x_3914_;
v___y_3905_ = v_a_3911_;
v___y_3906_ = v___x_3919_;
goto v___jp_3903_;
}
else
{
lean_object* v_val_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_val_3920_ = lean_ctor_get(v_a_3916_, 0);
lean_inc_n(v_val_3920_, 2);
lean_dec_ref_known(v_a_3916_, 1);
v___x_3921_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3922_ = l_Lean_MessageData_ofExpr(v_val_3920_);
v___x_3923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3846_, v___x_3923_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3926_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3777_, v_val_3920_, v_name_3792_, v_levelParams_3786_, v___x_3913_, v_hasTrace_3791_, v_a_3925_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
v___y_3904_ = v___x_3914_;
v___y_3905_ = v_a_3911_;
v___y_3906_ = v___x_3926_;
goto v___jp_3903_;
}
else
{
lean_dec(v_val_3920_);
lean_dec(v_name_3792_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v___y_3904_ = v___x_3914_;
v___y_3905_ = v_a_3911_;
v___y_3906_ = v___x_3924_;
goto v___jp_3903_;
}
}
}
else
{
lean_object* v___x_3927_; 
lean_dec(v_a_3916_);
lean_dec(v_name_3792_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v___x_3927_ = lean_box(0);
v___y_3894_ = v___x_3914_;
v___y_3895_ = v_a_3911_;
v_a_3896_ = v___x_3927_;
goto v___jp_3893_;
}
}
else
{
lean_object* v_a_3928_; 
lean_dec(v_name_3792_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v_a_3928_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___x_3915_, 1);
v___y_3899_ = v___x_3914_;
v___y_3900_ = v_a_3911_;
v_a_3901_ = v_a_3928_;
goto v___jp_3898_;
}
}
else
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3777_);
v___x_3930_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3931_);
lean_dec_ref_known(v___x_3930_, 1);
if (lean_obj_tag(v_a_3931_) == 1)
{
if (v___x_3849_ == 0)
{
lean_object* v_val_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v_val_3932_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_val_3932_);
lean_dec_ref_known(v_a_3931_, 1);
v___x_3933_ = lean_box(0);
v___x_3934_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3777_, v_val_3932_, v_name_3792_, v_levelParams_3786_, v___x_3913_, v___x_3933_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
v___y_3873_ = v_a_3911_;
v___y_3874_ = v___x_3929_;
v___y_3875_ = v___x_3934_;
goto v___jp_3872_;
}
else
{
lean_object* v_val_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v_val_3935_ = lean_ctor_get(v_a_3931_, 0);
lean_inc_n(v_val_3935_, 2);
lean_dec_ref_known(v_a_3931_, 1);
v___x_3936_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3937_ = l_Lean_MessageData_ofExpr(v_val_3935_);
v___x_3938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3936_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3846_, v___x_3938_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3941_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
v___x_3941_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3777_, v_val_3935_, v_name_3792_, v_levelParams_3786_, v___x_3913_, v_a_3940_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
v___y_3873_ = v_a_3911_;
v___y_3874_ = v___x_3929_;
v___y_3875_ = v___x_3941_;
goto v___jp_3872_;
}
else
{
lean_dec(v_val_3935_);
lean_dec(v_name_3792_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v___y_3873_ = v_a_3911_;
v___y_3874_ = v___x_3929_;
v___y_3875_ = v___x_3939_;
goto v___jp_3872_;
}
}
}
else
{
lean_object* v___x_3942_; 
lean_dec(v_a_3931_);
lean_dec(v_name_3792_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v___x_3942_ = lean_box(0);
v___y_3868_ = v_a_3911_;
v___y_3869_ = v___x_3929_;
v_a_3870_ = v___x_3942_;
goto v___jp_3867_;
}
}
else
{
lean_object* v_a_3943_; 
lean_dec(v_name_3792_);
lean_dec(v_levelParams_3786_);
lean_dec_ref(v_ctorVal_3777_);
v_a_3943_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3930_, 1);
v___y_3863_ = v_a_3911_;
v___y_3864_ = v___x_3929_;
v_a_3865_ = v_a_3943_;
goto v___jp_3862_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_4015_, lean_object* v_decl_4016_, lean_object* v_ref_4017_){
_start:
{
lean_object* v_defValue_4019_; lean_object* v_descr_4020_; lean_object* v_deprecation_x3f_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v_defValue_4019_ = lean_ctor_get(v_decl_4016_, 0);
v_descr_4020_ = lean_ctor_get(v_decl_4016_, 1);
v_deprecation_x3f_4021_ = lean_ctor_get(v_decl_4016_, 2);
v___x_4022_ = lean_alloc_ctor(1, 0, 1);
v___x_4023_ = lean_unbox(v_defValue_4019_);
lean_ctor_set_uint8(v___x_4022_, 0, v___x_4023_);
lean_inc(v_deprecation_x3f_4021_);
lean_inc_ref(v_descr_4020_);
lean_inc_n(v_name_4015_, 2);
v___x_4024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4024_, 0, v_name_4015_);
lean_ctor_set(v___x_4024_, 1, v_ref_4017_);
lean_ctor_set(v___x_4024_, 2, v___x_4022_);
lean_ctor_set(v___x_4024_, 3, v_descr_4020_);
lean_ctor_set(v___x_4024_, 4, v_deprecation_x3f_4021_);
v___x_4025_ = lean_register_option(v_name_4015_, v___x_4024_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4033_; 
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4033_ == 0)
{
lean_object* v_unused_4034_; 
v_unused_4034_ = lean_ctor_get(v___x_4025_, 0);
lean_dec(v_unused_4034_);
v___x_4027_ = v___x_4025_;
v_isShared_4028_ = v_isSharedCheck_4033_;
goto v_resetjp_4026_;
}
else
{
lean_dec(v___x_4025_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4033_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4029_; lean_object* v___x_4031_; 
lean_inc(v_defValue_4019_);
v___x_4029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4029_, 0, v_name_4015_);
lean_ctor_set(v___x_4029_, 1, v_defValue_4019_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v___x_4029_);
v___x_4031_ = v___x_4027_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4029_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec(v_name_4015_);
v_a_4035_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4025_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4025_);
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
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4043_, lean_object* v_decl_4044_, lean_object* v_ref_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4043_, v_decl_4044_, v_ref_4045_);
lean_dec_ref(v_decl_4044_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4062_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4063_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4064_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4065_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4062_, v___x_4063_, v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4068_, uint8_t v_isExporting_4069_, lean_object* v___x_4070_, lean_object* v___y_4071_, lean_object* v___x_4072_, lean_object* v_a_x3f_4073_){
_start:
{
lean_object* v___x_4075_; lean_object* v_env_4076_; lean_object* v_nextMacroScope_4077_; lean_object* v_ngen_4078_; lean_object* v_auxDeclNGen_4079_; lean_object* v_traceState_4080_; lean_object* v_messages_4081_; lean_object* v_infoState_4082_; lean_object* v_snapshotTasks_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4108_; 
v___x_4075_ = lean_st_ref_take(v___y_4068_);
v_env_4076_ = lean_ctor_get(v___x_4075_, 0);
v_nextMacroScope_4077_ = lean_ctor_get(v___x_4075_, 1);
v_ngen_4078_ = lean_ctor_get(v___x_4075_, 2);
v_auxDeclNGen_4079_ = lean_ctor_get(v___x_4075_, 3);
v_traceState_4080_ = lean_ctor_get(v___x_4075_, 4);
v_messages_4081_ = lean_ctor_get(v___x_4075_, 6);
v_infoState_4082_ = lean_ctor_get(v___x_4075_, 7);
v_snapshotTasks_4083_ = lean_ctor_get(v___x_4075_, 8);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4108_ == 0)
{
lean_object* v_unused_4109_; 
v_unused_4109_ = lean_ctor_get(v___x_4075_, 5);
lean_dec(v_unused_4109_);
v___x_4085_ = v___x_4075_;
v_isShared_4086_ = v_isSharedCheck_4108_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_snapshotTasks_4083_);
lean_inc(v_infoState_4082_);
lean_inc(v_messages_4081_);
lean_inc(v_traceState_4080_);
lean_inc(v_auxDeclNGen_4079_);
lean_inc(v_ngen_4078_);
lean_inc(v_nextMacroScope_4077_);
lean_inc(v_env_4076_);
lean_dec(v___x_4075_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4108_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4087_; lean_object* v___x_4089_; 
v___x_4087_ = l_Lean_Environment_setExporting(v_env_4076_, v_isExporting_4069_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 5, v___x_4070_);
lean_ctor_set(v___x_4085_, 0, v___x_4087_);
v___x_4089_ = v___x_4085_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4087_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v_nextMacroScope_4077_);
lean_ctor_set(v_reuseFailAlloc_4107_, 2, v_ngen_4078_);
lean_ctor_set(v_reuseFailAlloc_4107_, 3, v_auxDeclNGen_4079_);
lean_ctor_set(v_reuseFailAlloc_4107_, 4, v_traceState_4080_);
lean_ctor_set(v_reuseFailAlloc_4107_, 5, v___x_4070_);
lean_ctor_set(v_reuseFailAlloc_4107_, 6, v_messages_4081_);
lean_ctor_set(v_reuseFailAlloc_4107_, 7, v_infoState_4082_);
lean_ctor_set(v_reuseFailAlloc_4107_, 8, v_snapshotTasks_4083_);
v___x_4089_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v_mctx_4092_; lean_object* v_zetaDeltaFVarIds_4093_; lean_object* v_postponed_4094_; lean_object* v_diag_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4105_; 
v___x_4090_ = lean_st_ref_set(v___y_4068_, v___x_4089_);
v___x_4091_ = lean_st_ref_take(v___y_4071_);
v_mctx_4092_ = lean_ctor_get(v___x_4091_, 0);
v_zetaDeltaFVarIds_4093_ = lean_ctor_get(v___x_4091_, 2);
v_postponed_4094_ = lean_ctor_get(v___x_4091_, 3);
v_diag_4095_ = lean_ctor_get(v___x_4091_, 4);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; 
v_unused_4106_ = lean_ctor_get(v___x_4091_, 1);
lean_dec(v_unused_4106_);
v___x_4097_ = v___x_4091_;
v_isShared_4098_ = v_isSharedCheck_4105_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_diag_4095_);
lean_inc(v_postponed_4094_);
lean_inc(v_zetaDeltaFVarIds_4093_);
lean_inc(v_mctx_4092_);
lean_dec(v___x_4091_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4105_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 1, v___x_4072_);
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_mctx_4092_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v___x_4072_);
lean_ctor_set(v_reuseFailAlloc_4104_, 2, v_zetaDeltaFVarIds_4093_);
lean_ctor_set(v_reuseFailAlloc_4104_, 3, v_postponed_4094_);
lean_ctor_set(v_reuseFailAlloc_4104_, 4, v_diag_4095_);
v___x_4100_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = lean_st_ref_set(v___y_4071_, v___x_4100_);
v___x_4102_ = lean_box(0);
v___x_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
return v___x_4103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4110_, lean_object* v_isExporting_4111_, lean_object* v___x_4112_, lean_object* v___y_4113_, lean_object* v___x_4114_, lean_object* v_a_x3f_4115_, lean_object* v___y_4116_){
_start:
{
uint8_t v_isExporting_boxed_4117_; lean_object* v_res_4118_; 
v_isExporting_boxed_4117_ = lean_unbox(v_isExporting_4111_);
v_res_4118_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4110_, v_isExporting_boxed_4117_, v___x_4112_, v___y_4113_, v___x_4114_, v_a_x3f_4115_);
lean_dec(v_a_x3f_4115_);
lean_dec(v___y_4113_);
lean_dec(v___y_4110_);
return v_res_4118_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4119_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
return v___x_4121_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4122_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
return v___x_4123_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4125_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
lean_ctor_set(v___x_4125_, 2, v___x_4124_);
lean_ctor_set(v___x_4125_, 3, v___x_4124_);
lean_ctor_set(v___x_4125_, 4, v___x_4124_);
lean_ctor_set(v___x_4125_, 5, v___x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4126_, uint8_t v_isExporting_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v___x_4133_; lean_object* v_env_4134_; uint8_t v_isExporting_4135_; lean_object* v___x_4136_; lean_object* v_env_4137_; lean_object* v_nextMacroScope_4138_; lean_object* v_ngen_4139_; lean_object* v_auxDeclNGen_4140_; lean_object* v_traceState_4141_; lean_object* v_messages_4142_; lean_object* v_infoState_4143_; lean_object* v_snapshotTasks_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4198_; 
v___x_4133_ = lean_st_ref_get(v___y_4131_);
v_env_4134_ = lean_ctor_get(v___x_4133_, 0);
lean_inc_ref(v_env_4134_);
lean_dec(v___x_4133_);
v_isExporting_4135_ = lean_ctor_get_uint8(v_env_4134_, sizeof(void*)*8);
lean_dec_ref(v_env_4134_);
v___x_4136_ = lean_st_ref_take(v___y_4131_);
v_env_4137_ = lean_ctor_get(v___x_4136_, 0);
v_nextMacroScope_4138_ = lean_ctor_get(v___x_4136_, 1);
v_ngen_4139_ = lean_ctor_get(v___x_4136_, 2);
v_auxDeclNGen_4140_ = lean_ctor_get(v___x_4136_, 3);
v_traceState_4141_ = lean_ctor_get(v___x_4136_, 4);
v_messages_4142_ = lean_ctor_get(v___x_4136_, 6);
v_infoState_4143_ = lean_ctor_get(v___x_4136_, 7);
v_snapshotTasks_4144_ = lean_ctor_get(v___x_4136_, 8);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4198_ == 0)
{
lean_object* v_unused_4199_; 
v_unused_4199_ = lean_ctor_get(v___x_4136_, 5);
lean_dec(v_unused_4199_);
v___x_4146_ = v___x_4136_;
v_isShared_4147_ = v_isSharedCheck_4198_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_snapshotTasks_4144_);
lean_inc(v_infoState_4143_);
lean_inc(v_messages_4142_);
lean_inc(v_traceState_4141_);
lean_inc(v_auxDeclNGen_4140_);
lean_inc(v_ngen_4139_);
lean_inc(v_nextMacroScope_4138_);
lean_inc(v_env_4137_);
lean_dec(v___x_4136_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4198_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4151_; 
v___x_4148_ = l_Lean_Environment_setExporting(v_env_4137_, v_isExporting_4127_);
v___x_4149_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 5, v___x_4149_);
lean_ctor_set(v___x_4146_, 0, v___x_4148_);
v___x_4151_ = v___x_4146_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4148_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v_nextMacroScope_4138_);
lean_ctor_set(v_reuseFailAlloc_4197_, 2, v_ngen_4139_);
lean_ctor_set(v_reuseFailAlloc_4197_, 3, v_auxDeclNGen_4140_);
lean_ctor_set(v_reuseFailAlloc_4197_, 4, v_traceState_4141_);
lean_ctor_set(v_reuseFailAlloc_4197_, 5, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4197_, 6, v_messages_4142_);
lean_ctor_set(v_reuseFailAlloc_4197_, 7, v_infoState_4143_);
lean_ctor_set(v_reuseFailAlloc_4197_, 8, v_snapshotTasks_4144_);
v___x_4151_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v_mctx_4154_; lean_object* v_zetaDeltaFVarIds_4155_; lean_object* v_postponed_4156_; lean_object* v_diag_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4195_; 
v___x_4152_ = lean_st_ref_set(v___y_4131_, v___x_4151_);
v___x_4153_ = lean_st_ref_take(v___y_4129_);
v_mctx_4154_ = lean_ctor_get(v___x_4153_, 0);
v_zetaDeltaFVarIds_4155_ = lean_ctor_get(v___x_4153_, 2);
v_postponed_4156_ = lean_ctor_get(v___x_4153_, 3);
v_diag_4157_ = lean_ctor_get(v___x_4153_, 4);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4195_ == 0)
{
lean_object* v_unused_4196_; 
v_unused_4196_ = lean_ctor_get(v___x_4153_, 1);
lean_dec(v_unused_4196_);
v___x_4159_ = v___x_4153_;
v_isShared_4160_ = v_isSharedCheck_4195_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_diag_4157_);
lean_inc(v_postponed_4156_);
lean_inc(v_zetaDeltaFVarIds_4155_);
lean_inc(v_mctx_4154_);
lean_dec(v___x_4153_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4195_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4161_; lean_object* v___x_4163_; 
v___x_4161_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 1, v___x_4161_);
v___x_4163_ = v___x_4159_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_mctx_4154_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4194_, 2, v_zetaDeltaFVarIds_4155_);
lean_ctor_set(v_reuseFailAlloc_4194_, 3, v_postponed_4156_);
lean_ctor_set(v_reuseFailAlloc_4194_, 4, v_diag_4157_);
v___x_4163_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4164_; lean_object* v_r_4165_; 
v___x_4164_ = lean_st_ref_set(v___y_4129_, v___x_4163_);
lean_inc(v___y_4131_);
lean_inc_ref(v___y_4130_);
lean_inc(v___y_4129_);
lean_inc_ref(v___y_4128_);
v_r_4165_ = lean_apply_5(v_x_4126_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, lean_box(0));
if (lean_obj_tag(v_r_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4182_; 
v_a_4166_ = lean_ctor_get(v_r_4165_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_r_4165_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4168_ = v_r_4165_;
v_isShared_4169_ = v_isSharedCheck_4182_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v_r_4165_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4182_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
lean_inc(v_a_4166_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set_tag(v___x_4168_, 1);
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
lean_object* v___x_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
v___x_4172_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4131_, v_isExporting_4135_, v___x_4149_, v___y_4129_, v___x_4161_, v___x_4171_);
lean_dec_ref(v___x_4171_);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4179_ == 0)
{
lean_object* v_unused_4180_; 
v_unused_4180_ = lean_ctor_get(v___x_4172_, 0);
lean_dec(v_unused_4180_);
v___x_4174_ = v___x_4172_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_dec(v___x_4172_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v_a_4166_);
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4166_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
v_a_4183_ = lean_ctor_get(v_r_4165_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v_r_4165_, 1);
v___x_4184_ = lean_box(0);
v___x_4185_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4131_, v_isExporting_4135_, v___x_4149_, v___y_4129_, v___x_4161_, v___x_4184_);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4192_ == 0)
{
lean_object* v_unused_4193_; 
v_unused_4193_ = lean_ctor_get(v___x_4185_, 0);
lean_dec(v_unused_4193_);
v___x_4187_ = v___x_4185_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_dec(v___x_4185_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
lean_ctor_set_tag(v___x_4187_, 1);
lean_ctor_set(v___x_4187_, 0, v_a_4183_);
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4183_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4200_, lean_object* v_isExporting_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
uint8_t v_isExporting_boxed_4207_; lean_object* v_res_4208_; 
v_isExporting_boxed_4207_ = lean_unbox(v_isExporting_4201_);
v_res_4208_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4200_, v_isExporting_boxed_4207_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4209_, lean_object* v_x_4210_, uint8_t v_isExporting_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4210_, v_isExporting_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4218_, lean_object* v_x_4219_, lean_object* v_isExporting_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v_isExporting_boxed_4226_; lean_object* v_res_4227_; 
v_isExporting_boxed_4226_ = lean_unbox(v_isExporting_4220_);
v_res_4227_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4218_, v_x_4219_, v_isExporting_boxed_4226_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4228_, lean_object* v_localInsts_4229_, lean_object* v_x_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4228_, v_localInsts_4229_, v_x_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
v_a_4245_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4236_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4236_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4253_, lean_object* v_localInsts_4254_, lean_object* v_x_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4253_, v_localInsts_4254_, v_x_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4262_, lean_object* v_lctx_4263_, lean_object* v_localInsts_4264_, lean_object* v_x_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4263_, v_localInsts_4264_, v_x_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4272_, lean_object* v_lctx_4273_, lean_object* v_localInsts_4274_, lean_object* v_x_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4272_, v_lctx_4273_, v_localInsts_4274_, v_x_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4282_, lean_object* v_x_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = l_Lean_MessageData_ofName(v_declName_4282_);
v___x_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4291_, lean_object* v_x_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4291_, v_x_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec_ref(v_x_4292_);
return v_res_4298_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_instMonadEIO(lean_box(0));
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v_toApplicative_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4373_; 
v___x_4310_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4311_ = l_StateRefT_x27_instMonad___redArg(v___x_4310_);
v_toApplicative_4312_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4373_ == 0)
{
lean_object* v_unused_4374_; 
v_unused_4374_ = lean_ctor_get(v___x_4311_, 1);
lean_dec(v_unused_4374_);
v___x_4314_ = v___x_4311_;
v_isShared_4315_ = v_isSharedCheck_4373_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_toApplicative_4312_);
lean_dec(v___x_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4373_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v_toFunctor_4316_; lean_object* v_toSeq_4317_; lean_object* v_toSeqLeft_4318_; lean_object* v_toSeqRight_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4371_; 
v_toFunctor_4316_ = lean_ctor_get(v_toApplicative_4312_, 0);
v_toSeq_4317_ = lean_ctor_get(v_toApplicative_4312_, 2);
v_toSeqLeft_4318_ = lean_ctor_get(v_toApplicative_4312_, 3);
v_toSeqRight_4319_ = lean_ctor_get(v_toApplicative_4312_, 4);
v_isSharedCheck_4371_ = !lean_is_exclusive(v_toApplicative_4312_);
if (v_isSharedCheck_4371_ == 0)
{
lean_object* v_unused_4372_; 
v_unused_4372_ = lean_ctor_get(v_toApplicative_4312_, 1);
lean_dec(v_unused_4372_);
v___x_4321_ = v_toApplicative_4312_;
v_isShared_4322_ = v_isSharedCheck_4371_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_toSeqRight_4319_);
lean_inc(v_toSeqLeft_4318_);
lean_inc(v_toSeq_4317_);
lean_inc(v_toFunctor_4316_);
lean_dec(v_toApplicative_4312_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4371_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___f_4323_; lean_object* v___f_4324_; lean_object* v___f_4325_; lean_object* v___f_4326_; lean_object* v___x_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___f_4330_; lean_object* v___x_4332_; 
v___f_4323_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4324_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4316_);
v___f_4325_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4325_, 0, v_toFunctor_4316_);
v___f_4326_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4326_, 0, v_toFunctor_4316_);
v___x_4327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___f_4325_);
lean_ctor_set(v___x_4327_, 1, v___f_4326_);
v___f_4328_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4328_, 0, v_toSeqRight_4319_);
v___f_4329_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4329_, 0, v_toSeqLeft_4318_);
v___f_4330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4330_, 0, v_toSeq_4317_);
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 4, v___f_4328_);
lean_ctor_set(v___x_4321_, 3, v___f_4329_);
lean_ctor_set(v___x_4321_, 2, v___f_4330_);
lean_ctor_set(v___x_4321_, 1, v___f_4323_);
lean_ctor_set(v___x_4321_, 0, v___x_4327_);
v___x_4332_ = v___x_4321_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v___f_4323_);
lean_ctor_set(v_reuseFailAlloc_4370_, 2, v___f_4330_);
lean_ctor_set(v_reuseFailAlloc_4370_, 3, v___f_4329_);
lean_ctor_set(v_reuseFailAlloc_4370_, 4, v___f_4328_);
v___x_4332_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
lean_object* v___x_4334_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 1, v___f_4324_);
lean_ctor_set(v___x_4314_, 0, v___x_4332_);
v___x_4334_ = v___x_4314_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4332_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v___f_4324_);
v___x_4334_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4335_; lean_object* v_toApplicative_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4367_; 
v___x_4335_ = l_StateRefT_x27_instMonad___redArg(v___x_4334_);
v_toApplicative_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4367_ == 0)
{
lean_object* v_unused_4368_; 
v_unused_4368_ = lean_ctor_get(v___x_4335_, 1);
lean_dec(v_unused_4368_);
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4367_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_toApplicative_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4367_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v_toFunctor_4340_; lean_object* v_toSeq_4341_; lean_object* v_toSeqLeft_4342_; lean_object* v_toSeqRight_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4365_; 
v_toFunctor_4340_ = lean_ctor_get(v_toApplicative_4336_, 0);
v_toSeq_4341_ = lean_ctor_get(v_toApplicative_4336_, 2);
v_toSeqLeft_4342_ = lean_ctor_get(v_toApplicative_4336_, 3);
v_toSeqRight_4343_ = lean_ctor_get(v_toApplicative_4336_, 4);
v_isSharedCheck_4365_ = !lean_is_exclusive(v_toApplicative_4336_);
if (v_isSharedCheck_4365_ == 0)
{
lean_object* v_unused_4366_; 
v_unused_4366_ = lean_ctor_get(v_toApplicative_4336_, 1);
lean_dec(v_unused_4366_);
v___x_4345_ = v_toApplicative_4336_;
v_isShared_4346_ = v_isSharedCheck_4365_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_toSeqRight_4343_);
lean_inc(v_toSeqLeft_4342_);
lean_inc(v_toSeq_4341_);
lean_inc(v_toFunctor_4340_);
lean_dec(v_toApplicative_4336_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4365_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___f_4347_; lean_object* v___f_4348_; lean_object* v___f_4349_; lean_object* v___f_4350_; lean_object* v___x_4351_; lean_object* v___f_4352_; lean_object* v___f_4353_; lean_object* v___f_4354_; lean_object* v___x_4356_; 
v___f_4347_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4348_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4340_);
v___f_4349_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4349_, 0, v_toFunctor_4340_);
v___f_4350_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4350_, 0, v_toFunctor_4340_);
v___x_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4351_, 0, v___f_4349_);
lean_ctor_set(v___x_4351_, 1, v___f_4350_);
v___f_4352_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4352_, 0, v_toSeqRight_4343_);
v___f_4353_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4353_, 0, v_toSeqLeft_4342_);
v___f_4354_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4354_, 0, v_toSeq_4341_);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 4, v___f_4352_);
lean_ctor_set(v___x_4345_, 3, v___f_4353_);
lean_ctor_set(v___x_4345_, 2, v___f_4354_);
lean_ctor_set(v___x_4345_, 1, v___f_4347_);
lean_ctor_set(v___x_4345_, 0, v___x_4351_);
v___x_4356_ = v___x_4345_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4351_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v___f_4347_);
lean_ctor_set(v_reuseFailAlloc_4364_, 2, v___f_4354_);
lean_ctor_set(v_reuseFailAlloc_4364_, 3, v___f_4353_);
lean_ctor_set(v_reuseFailAlloc_4364_, 4, v___f_4352_);
v___x_4356_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
lean_object* v___x_4358_; 
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 1, v___f_4348_);
lean_ctor_set(v___x_4338_, 0, v___x_4356_);
v___x_4358_ = v___x_4338_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4356_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v___f_4348_);
v___x_4358_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_19101__overap_4361_; lean_object* v___x_4362_; 
v___x_4359_ = lean_box(0);
v___x_4360_ = l_instInhabitedOfMonad___redArg(v___x_4358_, v___x_4359_);
v___x_19101__overap_4361_ = lean_panic_fn_borrowed(v___x_4360_, v_msg_4304_);
lean_dec(v___x_4360_);
lean_inc(v___y_4308_);
lean_inc_ref(v___y_4307_);
lean_inc(v___y_4306_);
lean_inc_ref(v___y_4305_);
v___x_4362_ = lean_apply_5(v___x_19101__overap_4361_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, lean_box(0));
return v___x_4362_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4381_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4384_ = l_Lean_stringToMessageData(v___x_4383_);
return v___x_4384_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4387_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4388_ = lean_unsigned_to_nat(11u);
v___x_4389_ = lean_unsigned_to_nat(122u);
v___x_4390_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4391_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4392_ = l_mkPanicMessageWithDecl(v___x_4391_, v___x_4390_, v___x_4389_, v___x_4388_, v___x_4387_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4407_; lean_object* v_env_4408_; uint8_t v___x_4409_; lean_object* v___x_4410_; 
v___x_4407_ = lean_st_ref_get(v___y_4397_);
v_env_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc_ref(v_env_4408_);
lean_dec(v___x_4407_);
v___x_4409_ = 0;
lean_inc(v_constName_4393_);
v___x_4410_ = l_Lean_Environment_findAsync_x3f(v_env_4408_, v_constName_4393_, v___x_4409_);
if (lean_obj_tag(v___x_4410_) == 1)
{
lean_object* v_val_4411_; uint8_t v_kind_4412_; 
v_val_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_val_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v_kind_4412_ = lean_ctor_get_uint8(v_val_4411_, sizeof(void*)*3);
if (v_kind_4412_ == 6)
{
lean_object* v___x_4413_; 
v___x_4413_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4411_);
if (lean_obj_tag(v___x_4413_) == 6)
{
lean_object* v_val_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
lean_dec(v_constName_4393_);
v_val_4414_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___x_4413_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_val_4414_);
lean_dec(v___x_4413_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set_tag(v___x_4416_, 0);
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_val_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
else
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
lean_dec_ref(v___x_4413_);
v___x_4422_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4423_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4422_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4432_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4426_ = v___x_4423_;
v_isShared_4427_ = v_isSharedCheck_4432_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4423_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4432_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
if (lean_obj_tag(v_a_4424_) == 0)
{
lean_del_object(v___x_4426_);
goto v___jp_4399_;
}
else
{
lean_object* v_val_4428_; lean_object* v___x_4430_; 
lean_dec(v_constName_4393_);
v_val_4428_ = lean_ctor_get(v_a_4424_, 0);
lean_inc(v_val_4428_);
lean_dec_ref_known(v_a_4424_, 1);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 0, v_val_4428_);
v___x_4430_ = v___x_4426_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_val_4428_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_constName_4393_);
v_a_4433_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4423_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4423_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
else
{
lean_dec(v_val_4411_);
goto v___jp_4399_;
}
}
else
{
lean_dec(v___x_4410_);
goto v___jp_4399_;
}
v___jp_4399_:
{
lean_object* v___x_4400_; uint8_t v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4400_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4401_ = 0;
v___x_4402_ = l_Lean_MessageData_ofConstName(v_constName_4393_, v___x_4401_);
v___x_4403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4400_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
v___x_4404_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4403_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
v___x_4406_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4405_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
return v___x_4406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4448_, lean_object* v___x_4449_, lean_object* v___x_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4448_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4468_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4459_ = v___x_4456_;
v_isShared_4460_ = v_isSharedCheck_4468_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4456_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4468_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_numFields_4461_; uint8_t v___x_4462_; 
v_numFields_4461_ = lean_ctor_get(v_a_4457_, 4);
v___x_4462_ = lean_nat_dec_lt(v___x_4449_, v_numFields_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4464_; 
lean_dec(v_a_4457_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4450_);
v___x_4464_ = v___x_4459_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4450_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
else
{
lean_object* v___x_4466_; 
lean_del_object(v___x_4459_);
lean_inc(v_a_4457_);
v___x_4466_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4457_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v___x_4467_; 
lean_dec_ref_known(v___x_4466_, 1);
v___x_4467_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4457_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
return v___x_4467_;
}
else
{
lean_dec(v_a_4457_);
return v___x_4466_;
}
}
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
v_a_4469_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4456_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4456_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4477_, lean_object* v___x_4478_, lean_object* v___x_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4477_, v___x_4478_, v___x_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___x_4478_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4486_, uint8_t v___x_4487_, lean_object* v_as_x27_4488_, lean_object* v_b_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
if (lean_obj_tag(v_as_x27_4488_) == 0)
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v_b_4489_);
return v___x_4495_;
}
else
{
lean_object* v_head_4496_; lean_object* v_tail_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___f_4500_; uint8_t v___y_4502_; uint8_t v___x_4505_; 
v_head_4496_ = lean_ctor_get(v_as_x27_4488_, 0);
v_tail_4497_ = lean_ctor_get(v_as_x27_4488_, 1);
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = lean_box(0);
lean_inc(v_head_4496_);
v___f_4500_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4500_, 0, v_head_4496_);
lean_closure_set(v___f_4500_, 1, v___x_4498_);
lean_closure_set(v___f_4500_, 2, v___x_4499_);
v___x_4505_ = l_Lean_isPrivateName(v_head_4496_);
if (v___x_4505_ == 0)
{
v___y_4502_ = v___y_4486_;
goto v___jp_4501_;
}
else
{
v___y_4502_ = v___x_4487_;
goto v___jp_4501_;
}
v___jp_4501_:
{
lean_object* v___x_4503_; 
v___x_4503_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4500_, v___y_4502_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_dec_ref_known(v___x_4503_, 1);
v_as_x27_4488_ = v_tail_4497_;
v_b_4489_ = v___x_4499_;
goto _start;
}
else
{
return v___x_4503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4506_, lean_object* v___x_4507_, lean_object* v_as_x27_4508_, lean_object* v_b_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
uint8_t v___y_20211__boxed_4515_; uint8_t v___x_20212__boxed_4516_; lean_object* v_res_4517_; 
v___y_20211__boxed_4515_ = lean_unbox(v___y_4506_);
v___x_20212__boxed_4516_ = lean_unbox(v___x_4507_);
v_res_4517_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_20211__boxed_4515_, v___x_20212__boxed_4516_, v_as_x27_4508_, v_b_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v_as_x27_4508_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4518_, uint8_t v_hasTrace_4519_, lean_object* v_ctors_4520_, lean_object* v___x_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v___x_4527_; 
v___x_4527_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4518_, v_hasTrace_4519_, v_ctors_4520_, v___x_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4534_; 
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4534_ == 0)
{
lean_object* v_unused_4535_; 
v_unused_4535_ = lean_ctor_get(v___x_4527_, 0);
lean_dec(v_unused_4535_);
v___x_4529_ = v___x_4527_;
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
else
{
lean_dec(v___x_4527_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4521_);
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4521_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
else
{
return v___x_4527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4536_, lean_object* v_hasTrace_4537_, lean_object* v_ctors_4538_, lean_object* v___x_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
uint8_t v___y_20256__boxed_4545_; uint8_t v_hasTrace_boxed_4546_; lean_object* v_res_4547_; 
v___y_20256__boxed_4545_ = lean_unbox(v___y_4536_);
v_hasTrace_boxed_4546_ = lean_unbox(v_hasTrace_4537_);
v_res_4547_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_20256__boxed_4545_, v_hasTrace_boxed_4546_, v_ctors_4538_, v___x_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v_ctors_4538_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t v_hasTrace_4548_, uint8_t v___x_4549_, lean_object* v_ctors_4550_, lean_object* v___x_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
lean_object* v___x_4557_; 
v___x_4557_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_hasTrace_4548_, v___x_4549_, v_ctors_4550_, v___x_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4564_ == 0)
{
lean_object* v_unused_4565_; 
v_unused_4565_ = lean_ctor_get(v___x_4557_, 0);
lean_dec(v_unused_4565_);
v___x_4559_ = v___x_4557_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_dec(v___x_4557_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 0, v___x_4551_);
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v___x_4551_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
else
{
return v___x_4557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object* v_hasTrace_4566_, lean_object* v___x_4567_, lean_object* v_ctors_4568_, lean_object* v___x_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
uint8_t v_hasTrace_boxed_4575_; uint8_t v___x_20297__boxed_4576_; lean_object* v_res_4577_; 
v_hasTrace_boxed_4575_ = lean_unbox(v_hasTrace_4566_);
v___x_20297__boxed_4576_ = lean_unbox(v___x_4567_);
v_res_4577_ = l_Lean_Meta_mkInjectiveTheorems___lam__2(v_hasTrace_boxed_4575_, v___x_20297__boxed_4576_, v_ctors_4568_, v___x_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v_ctors_4568_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t v___x_4578_, uint8_t v_isUnsafe_4579_, lean_object* v_ctors_4580_, lean_object* v___x_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v___x_4587_; 
v___x_4587_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4578_, v_isUnsafe_4579_, v_ctors_4580_, v___x_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; 
v_unused_4595_ = lean_ctor_get(v___x_4587_, 0);
lean_dec(v_unused_4595_);
v___x_4589_ = v___x_4587_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_dec(v___x_4587_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v___x_4581_);
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4581_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
else
{
return v___x_4587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object* v___x_4596_, lean_object* v_isUnsafe_4597_, lean_object* v_ctors_4598_, lean_object* v___x_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
uint8_t v___x_20338__boxed_4605_; uint8_t v_isUnsafe_boxed_4606_; lean_object* v_res_4607_; 
v___x_20338__boxed_4605_ = lean_unbox(v___x_4596_);
v_isUnsafe_boxed_4606_ = lean_unbox(v_isUnsafe_4597_);
v_res_4607_ = l_Lean_Meta_mkInjectiveTheorems___lam__3(v___x_20338__boxed_4605_, v_isUnsafe_boxed_4606_, v_ctors_4598_, v___x_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v_ctors_4598_);
return v_res_4607_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4609_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4610_ = l_Lean_stringToMessageData(v___x_4609_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v___x_4617_; lean_object* v_env_4618_; lean_object* v___x_4619_; 
v___x_4617_ = lean_st_ref_get(v___y_4615_);
v_env_4618_ = lean_ctor_get(v___x_4617_, 0);
lean_inc_ref(v_env_4618_);
lean_dec(v___x_4617_);
lean_inc(v_constName_4611_);
v___x_4619_ = l_Lean_isInductiveCore_x3f(v_env_4618_, v_constName_4611_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v___x_4620_; uint8_t v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4620_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4621_ = 0;
v___x_4622_ = l_Lean_MessageData_ofConstName(v_constName_4611_, v___x_4621_);
v___x_4623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4620_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
v___x_4624_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4623_);
lean_ctor_set(v___x_4625_, 1, v___x_4624_);
v___x_4626_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4625_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
return v___x_4626_;
}
else
{
lean_object* v_val_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
lean_dec(v_constName_4611_);
v_val_4627_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4619_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_val_4627_);
lean_dec(v___x_4619_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
lean_ctor_set_tag(v___x_4629_, 0);
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_val_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
return v_res_4641_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4642_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
return v___x_4644_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4645_ = lean_unsigned_to_nat(32u);
v___x_4646_ = lean_mk_empty_array_with_capacity(v___x_4645_);
v___x_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
return v___x_4647_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4648_ = ((size_t)5ULL);
v___x_4649_ = lean_unsigned_to_nat(0u);
v___x_4650_ = lean_unsigned_to_nat(32u);
v___x_4651_ = lean_mk_empty_array_with_capacity(v___x_4650_);
v___x_4652_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4653_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
lean_ctor_set(v___x_4653_, 1, v___x_4651_);
lean_ctor_set(v___x_4653_, 2, v___x_4649_);
lean_ctor_set(v___x_4653_, 3, v___x_4649_);
lean_ctor_set_usize(v___x_4653_, 4, v___x_4648_);
return v___x_4653_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4654_ = lean_box(1);
v___x_4655_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4656_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
lean_ctor_set(v___x_4657_, 1, v___x_4655_);
lean_ctor_set(v___x_4657_, 2, v___x_4654_);
return v___x_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4666_ = lean_st_ref_get(v_a_4664_);
lean_inc(v_declName_4660_);
v___x_4667_ = l_Lean_Meta_isInductivePredicate(v_declName_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4864_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4670_ = v___x_4667_;
v_isShared_4671_ = v_isSharedCheck_4864_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4667_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4864_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v_env_4677_; lean_object* v___f_4678_; lean_object* v___x_4679_; uint8_t v___x_4680_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; uint8_t v___y_4686_; lean_object* v___y_4687_; lean_object* v_a_4688_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___y_4700_; lean_object* v___y_4701_; uint8_t v___y_4702_; lean_object* v___y_4703_; lean_object* v_a_4704_; lean_object* v___y_4707_; lean_object* v___y_4708_; lean_object* v___y_4709_; lean_object* v___y_4710_; uint8_t v___y_4711_; lean_object* v___y_4712_; lean_object* v_a_4713_; lean_object* v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; lean_object* v___y_4719_; uint8_t v___y_4720_; lean_object* v___y_4721_; lean_object* v_a_4722_; lean_object* v___y_4735_; lean_object* v___y_4736_; lean_object* v___y_4737_; lean_object* v___y_4738_; uint8_t v___y_4739_; lean_object* v___y_4740_; lean_object* v_a_4741_; lean_object* v___y_4744_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; uint8_t v___y_4748_; lean_object* v___y_4749_; lean_object* v_a_4750_; uint8_t v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; uint8_t v___y_4756_; lean_object* v___y_4757_; uint8_t v___y_4795_; uint8_t v___x_4860_; 
v_env_4677_ = lean_ctor_get(v___x_4666_, 0);
lean_inc_ref(v_env_4677_);
lean_dec(v___x_4666_);
lean_inc(v_declName_4660_);
v___f_4678_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4678_, 0, v_declName_4660_);
v___x_4679_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4680_ = 1;
v___x_4860_ = l_Lean_Environment_contains(v_env_4677_, v___x_4679_, v___x_4680_);
if (v___x_4860_ == 0)
{
v___y_4795_ = v___x_4860_;
goto v___jp_4794_;
}
else
{
lean_object* v_options_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; 
v_options_4861_ = lean_ctor_get(v_a_4663_, 2);
v___x_4862_ = l_Lean_Meta_genInjectivity;
v___x_4863_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4861_, v___x_4862_);
v___y_4795_ = v___x_4863_;
goto v___jp_4794_;
}
v___jp_4672_:
{
lean_object* v___x_4673_; lean_object* v___x_4675_; 
v___x_4673_ = lean_box(0);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v___x_4673_);
v___x_4675_ = v___x_4670_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4673_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
v___jp_4681_:
{
lean_object* v___x_4689_; double v___x_4690_; double v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4689_ = lean_io_get_num_heartbeats();
v___x_4690_ = lean_float_of_nat(v___y_4684_);
v___x_4691_ = lean_float_of_nat(v___x_4689_);
v___x_4692_ = lean_box_float(v___x_4690_);
v___x_4693_ = lean_box_float(v___x_4691_);
v___x_4694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4692_);
lean_ctor_set(v___x_4694_, 1, v___x_4693_);
v___x_4695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4695_, 0, v_a_4688_);
lean_ctor_set(v___x_4695_, 1, v___x_4694_);
lean_inc_ref(v___y_4683_);
lean_inc(v___y_4687_);
v___x_4696_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4687_, v___x_4680_, v___y_4683_, v___y_4682_, v___y_4686_, v___y_4685_, v___f_4678_, v___x_4695_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
return v___x_4696_;
}
v___jp_4697_:
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4705_, 0, v_a_4704_);
v___y_4682_ = v___y_4698_;
v___y_4683_ = v___y_4699_;
v___y_4684_ = v___y_4700_;
v___y_4685_ = v___y_4701_;
v___y_4686_ = v___y_4702_;
v___y_4687_ = v___y_4703_;
v_a_4688_ = v___x_4705_;
goto v___jp_4681_;
}
v___jp_4706_:
{
lean_object* v___x_4714_; 
v___x_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4714_, 0, v_a_4713_);
v___y_4682_ = v___y_4707_;
v___y_4683_ = v___y_4708_;
v___y_4684_ = v___y_4709_;
v___y_4685_ = v___y_4710_;
v___y_4686_ = v___y_4711_;
v___y_4687_ = v___y_4712_;
v_a_4688_ = v___x_4714_;
goto v___jp_4681_;
}
v___jp_4715_:
{
lean_object* v___x_4723_; double v___x_4724_; double v___x_4725_; double v___x_4726_; double v___x_4727_; double v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4723_ = lean_io_mono_nanos_now();
v___x_4724_ = lean_float_of_nat(v___y_4718_);
v___x_4725_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4726_ = lean_float_div(v___x_4724_, v___x_4725_);
v___x_4727_ = lean_float_of_nat(v___x_4723_);
v___x_4728_ = lean_float_div(v___x_4727_, v___x_4725_);
v___x_4729_ = lean_box_float(v___x_4726_);
v___x_4730_ = lean_box_float(v___x_4728_);
v___x_4731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4729_);
lean_ctor_set(v___x_4731_, 1, v___x_4730_);
v___x_4732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4732_, 0, v_a_4722_);
lean_ctor_set(v___x_4732_, 1, v___x_4731_);
lean_inc_ref(v___y_4717_);
lean_inc(v___y_4721_);
v___x_4733_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4721_, v___x_4680_, v___y_4717_, v___y_4716_, v___y_4720_, v___y_4719_, v___f_4678_, v___x_4732_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
return v___x_4733_;
}
v___jp_4734_:
{
lean_object* v___x_4742_; 
v___x_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4742_, 0, v_a_4741_);
v___y_4716_ = v___y_4735_;
v___y_4717_ = v___y_4736_;
v___y_4718_ = v___y_4737_;
v___y_4719_ = v___y_4738_;
v___y_4720_ = v___y_4739_;
v___y_4721_ = v___y_4740_;
v_a_4722_ = v___x_4742_;
goto v___jp_4715_;
}
v___jp_4743_:
{
lean_object* v___x_4751_; 
v___x_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4751_, 0, v_a_4750_);
v___y_4716_ = v___y_4744_;
v___y_4717_ = v___y_4745_;
v___y_4718_ = v___y_4746_;
v___y_4719_ = v___y_4747_;
v___y_4720_ = v___y_4748_;
v___y_4721_ = v___y_4749_;
v_a_4722_ = v___x_4751_;
goto v___jp_4715_;
}
v___jp_4752_:
{
lean_object* v___x_4758_; lean_object* v_a_4759_; lean_object* v___x_4760_; uint8_t v___x_4761_; 
v___x_4758_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4664_);
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4759_);
lean_dec_ref(v___x_4758_);
v___x_4760_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4761_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4754_, v___x_4760_);
if (v___x_4761_ == 0)
{
lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4762_ = lean_io_mono_nanos_now();
v___x_4763_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4763_) == 0)
{
lean_object* v_a_4764_; uint8_t v_isUnsafe_4765_; 
v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
lean_inc(v_a_4764_);
lean_dec_ref_known(v___x_4763_, 1);
v_isUnsafe_4765_ = lean_ctor_get_uint8(v_a_4764_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4765_ == 0)
{
lean_object* v_ctors_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___f_4772_; lean_object* v___x_4773_; 
v_ctors_4766_ = lean_ctor_get(v_a_4764_, 4);
lean_inc(v_ctors_4766_);
lean_dec(v_a_4764_);
v___x_4767_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4768_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4769_ = lean_box(0);
v___x_4770_ = lean_box(v___y_4753_);
v___x_4771_ = lean_box(v___x_4761_);
v___f_4772_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4772_, 0, v___x_4770_);
lean_closure_set(v___f_4772_, 1, v___x_4771_);
lean_closure_set(v___f_4772_, 2, v_ctors_4766_);
lean_closure_set(v___f_4772_, 3, v___x_4769_);
v___x_4773_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4767_, v___x_4768_, v___f_4772_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4774_);
lean_dec_ref_known(v___x_4773_, 1);
v___y_4735_ = v___y_4754_;
v___y_4736_ = v___y_4755_;
v___y_4737_ = v___x_4762_;
v___y_4738_ = v_a_4759_;
v___y_4739_ = v___y_4756_;
v___y_4740_ = v___y_4757_;
v_a_4741_ = v_a_4774_;
goto v___jp_4734_;
}
else
{
lean_object* v_a_4775_; 
v_a_4775_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4775_);
lean_dec_ref_known(v___x_4773_, 1);
v___y_4744_ = v___y_4754_;
v___y_4745_ = v___y_4755_;
v___y_4746_ = v___x_4762_;
v___y_4747_ = v_a_4759_;
v___y_4748_ = v___y_4756_;
v___y_4749_ = v___y_4757_;
v_a_4750_ = v_a_4775_;
goto v___jp_4743_;
}
}
else
{
lean_object* v___x_4776_; 
lean_dec(v_a_4764_);
v___x_4776_ = lean_box(0);
v___y_4735_ = v___y_4754_;
v___y_4736_ = v___y_4755_;
v___y_4737_ = v___x_4762_;
v___y_4738_ = v_a_4759_;
v___y_4739_ = v___y_4756_;
v___y_4740_ = v___y_4757_;
v_a_4741_ = v___x_4776_;
goto v___jp_4734_;
}
}
else
{
lean_object* v_a_4777_; 
v_a_4777_ = lean_ctor_get(v___x_4763_, 0);
lean_inc(v_a_4777_);
lean_dec_ref_known(v___x_4763_, 1);
v___y_4744_ = v___y_4754_;
v___y_4745_ = v___y_4755_;
v___y_4746_ = v___x_4762_;
v___y_4747_ = v_a_4759_;
v___y_4748_ = v___y_4756_;
v___y_4749_ = v___y_4757_;
v_a_4750_ = v_a_4777_;
goto v___jp_4743_;
}
}
else
{
lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4778_ = lean_io_get_num_heartbeats();
v___x_4779_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; uint8_t v_isUnsafe_4781_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4780_);
lean_dec_ref_known(v___x_4779_, 1);
v_isUnsafe_4781_ = lean_ctor_get_uint8(v_a_4780_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4781_ == 0)
{
lean_object* v_ctors_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___f_4788_; lean_object* v___x_4789_; 
v_ctors_4782_ = lean_ctor_get(v_a_4780_, 4);
lean_inc(v_ctors_4782_);
lean_dec(v_a_4780_);
v___x_4783_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4784_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4785_ = lean_box(0);
v___x_4786_ = lean_box(v___x_4761_);
v___x_4787_ = lean_box(v_isUnsafe_4781_);
v___f_4788_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed), 9, 4);
lean_closure_set(v___f_4788_, 0, v___x_4786_);
lean_closure_set(v___f_4788_, 1, v___x_4787_);
lean_closure_set(v___f_4788_, 2, v_ctors_4782_);
lean_closure_set(v___f_4788_, 3, v___x_4785_);
v___x_4789_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4783_, v___x_4784_, v___f_4788_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4790_);
lean_dec_ref_known(v___x_4789_, 1);
v___y_4698_ = v___y_4754_;
v___y_4699_ = v___y_4755_;
v___y_4700_ = v___x_4778_;
v___y_4701_ = v_a_4759_;
v___y_4702_ = v___y_4756_;
v___y_4703_ = v___y_4757_;
v_a_4704_ = v_a_4790_;
goto v___jp_4697_;
}
else
{
lean_object* v_a_4791_; 
v_a_4791_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4791_);
lean_dec_ref_known(v___x_4789_, 1);
v___y_4707_ = v___y_4754_;
v___y_4708_ = v___y_4755_;
v___y_4709_ = v___x_4778_;
v___y_4710_ = v_a_4759_;
v___y_4711_ = v___y_4756_;
v___y_4712_ = v___y_4757_;
v_a_4713_ = v_a_4791_;
goto v___jp_4706_;
}
}
else
{
lean_object* v___x_4792_; 
lean_dec(v_a_4780_);
v___x_4792_ = lean_box(0);
v___y_4698_ = v___y_4754_;
v___y_4699_ = v___y_4755_;
v___y_4700_ = v___x_4778_;
v___y_4701_ = v_a_4759_;
v___y_4702_ = v___y_4756_;
v___y_4703_ = v___y_4757_;
v_a_4704_ = v___x_4792_;
goto v___jp_4697_;
}
}
else
{
lean_object* v_a_4793_; 
v_a_4793_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4793_);
lean_dec_ref_known(v___x_4779_, 1);
v___y_4707_ = v___y_4754_;
v___y_4708_ = v___y_4755_;
v___y_4709_ = v___x_4778_;
v___y_4710_ = v_a_4759_;
v___y_4711_ = v___y_4756_;
v___y_4712_ = v___y_4757_;
v_a_4713_ = v_a_4793_;
goto v___jp_4706_;
}
}
}
v___jp_4794_:
{
if (v___y_4795_ == 0)
{
lean_dec_ref(v___f_4678_);
lean_dec(v_a_4668_);
lean_dec(v_declName_4660_);
goto v___jp_4672_;
}
else
{
uint8_t v___x_4796_; 
v___x_4796_ = lean_unbox(v_a_4668_);
lean_dec(v_a_4668_);
if (v___x_4796_ == 0)
{
lean_object* v_options_4797_; uint8_t v_hasTrace_4798_; 
lean_del_object(v___x_4670_);
v_options_4797_ = lean_ctor_get(v_a_4663_, 2);
v_hasTrace_4798_ = lean_ctor_get_uint8(v_options_4797_, sizeof(void*)*1);
if (v_hasTrace_4798_ == 0)
{
lean_object* v___x_4799_; 
lean_dec_ref(v___f_4678_);
v___x_4799_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4817_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4817_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4817_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
uint8_t v_isUnsafe_4804_; 
v_isUnsafe_4804_ = lean_ctor_get_uint8(v_a_4800_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4804_ == 0)
{
lean_object* v_ctors_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___f_4811_; lean_object* v___x_4812_; 
lean_del_object(v___x_4802_);
v_ctors_4805_ = lean_ctor_get(v_a_4800_, 4);
lean_inc(v_ctors_4805_);
lean_dec(v_a_4800_);
v___x_4806_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4807_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4808_ = lean_box(0);
v___x_4809_ = lean_box(v___y_4795_);
v___x_4810_ = lean_box(v_hasTrace_4798_);
v___f_4811_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4811_, 0, v___x_4809_);
lean_closure_set(v___f_4811_, 1, v___x_4810_);
lean_closure_set(v___f_4811_, 2, v_ctors_4805_);
lean_closure_set(v___f_4811_, 3, v___x_4808_);
v___x_4812_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4806_, v___x_4807_, v___f_4811_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
return v___x_4812_;
}
else
{
lean_object* v___x_4813_; lean_object* v___x_4815_; 
lean_dec(v_a_4800_);
v___x_4813_ = lean_box(0);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v___x_4813_);
v___x_4815_ = v___x_4802_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
else
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
v_a_4818_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4799_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4799_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v_inheritedTraceOptions_4826_ = lean_ctor_get(v_a_4663_, 13);
v___x_4827_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4828_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4829_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4830_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4826_, v_options_4797_, v___x_4829_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4831_ = l_Lean_trace_profiler;
v___x_4832_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4797_, v___x_4831_);
if (v___x_4832_ == 0)
{
lean_object* v___x_4833_; 
lean_dec_ref(v___f_4678_);
v___x_4833_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4851_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4836_ = v___x_4833_;
v_isShared_4837_ = v_isSharedCheck_4851_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4833_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4851_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
uint8_t v_isUnsafe_4838_; 
v_isUnsafe_4838_ = lean_ctor_get_uint8(v_a_4834_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4838_ == 0)
{
lean_object* v_ctors_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___f_4845_; lean_object* v___x_4846_; 
lean_del_object(v___x_4836_);
v_ctors_4839_ = lean_ctor_get(v_a_4834_, 4);
lean_inc(v_ctors_4839_);
lean_dec(v_a_4834_);
v___x_4840_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4841_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4842_ = lean_box(0);
v___x_4843_ = lean_box(v_hasTrace_4798_);
v___x_4844_ = lean_box(v___x_4832_);
v___f_4845_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4845_, 0, v___x_4843_);
lean_closure_set(v___f_4845_, 1, v___x_4844_);
lean_closure_set(v___f_4845_, 2, v_ctors_4839_);
lean_closure_set(v___f_4845_, 3, v___x_4842_);
v___x_4846_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4840_, v___x_4841_, v___f_4845_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
return v___x_4846_;
}
else
{
lean_object* v___x_4847_; lean_object* v___x_4849_; 
lean_dec(v_a_4834_);
v___x_4847_ = lean_box(0);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 0, v___x_4847_);
v___x_4849_ = v___x_4836_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
else
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4859_; 
v_a_4852_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4854_ = v___x_4833_;
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4833_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
else
{
v___y_4753_ = v_hasTrace_4798_;
v___y_4754_ = v_options_4797_;
v___y_4755_ = v___x_4828_;
v___y_4756_ = v___x_4830_;
v___y_4757_ = v___x_4827_;
goto v___jp_4752_;
}
}
else
{
v___y_4753_ = v_hasTrace_4798_;
v___y_4754_ = v_options_4797_;
v___y_4755_ = v___x_4828_;
v___y_4756_ = v___x_4830_;
v___y_4757_ = v___x_4827_;
goto v___jp_4752_;
}
}
}
else
{
lean_dec_ref(v___f_4678_);
lean_dec(v_declName_4660_);
goto v___jp_4672_;
}
}
}
}
}
else
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
lean_dec(v___x_4666_);
lean_dec(v_declName_4660_);
v_a_4865_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4667_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4667_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_);
lean_dec(v_a_4877_);
lean_dec_ref(v_a_4876_);
lean_dec(v_a_4875_);
lean_dec_ref(v_a_4874_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4880_, uint8_t v___x_4881_, lean_object* v_as_4882_, lean_object* v_as_x27_4883_, lean_object* v_b_4884_, lean_object* v_a_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
lean_object* v___x_4891_; 
v___x_4891_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4880_, v___x_4881_, v_as_x27_4883_, v_b_4884_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4892_, lean_object* v___x_4893_, lean_object* v_as_4894_, lean_object* v_as_x27_4895_, lean_object* v_b_4896_, lean_object* v_a_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
uint8_t v___y_20965__boxed_4903_; uint8_t v___x_20966__boxed_4904_; lean_object* v_res_4905_; 
v___y_20965__boxed_4903_ = lean_unbox(v___y_4892_);
v___x_20966__boxed_4904_ = lean_unbox(v___x_4893_);
v_res_4905_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_20965__boxed_4903_, v___x_20966__boxed_4904_, v_as_4894_, v_as_x27_4895_, v_b_4896_, v_a_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
lean_dec(v___y_4899_);
lean_dec_ref(v___y_4898_);
lean_dec(v_as_x27_4895_);
lean_dec(v_as_4894_);
return v_res_4905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4946_ = lean_unsigned_to_nat(4172903888u);
v___x_4947_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4948_ = l_Lean_Name_num___override(v___x_4947_, v___x_4946_);
return v___x_4948_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4950_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4951_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4952_ = l_Lean_Name_str___override(v___x_4951_, v___x_4950_);
return v___x_4952_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4954_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4955_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4956_ = l_Lean_Name_str___override(v___x_4955_, v___x_4954_);
return v___x_4956_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4957_ = lean_unsigned_to_nat(2u);
v___x_4958_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4959_ = l_Lean_Name_num___override(v___x_4958_, v___x_4957_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4961_; uint8_t v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4961_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4962_ = 0;
v___x_4963_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4964_ = l_Lean_registerTraceClass(v___x_4961_, v___x_4962_, v___x_4963_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4967_, lean_object* v_b_4968_){
_start:
{
lean_object* v_array_4969_; lean_object* v_start_4970_; lean_object* v_stop_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4984_; 
v_array_4969_ = lean_ctor_get(v_a_4967_, 0);
v_start_4970_ = lean_ctor_get(v_a_4967_, 1);
v_stop_4971_ = lean_ctor_get(v_a_4967_, 2);
v_isSharedCheck_4984_ = !lean_is_exclusive(v_a_4967_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4973_ = v_a_4967_;
v_isShared_4974_ = v_isSharedCheck_4984_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_stop_4971_);
lean_inc(v_start_4970_);
lean_inc(v_array_4969_);
lean_dec(v_a_4967_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4984_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
uint8_t v___x_4975_; 
v___x_4975_ = lean_nat_dec_lt(v_start_4970_, v_stop_4971_);
if (v___x_4975_ == 0)
{
lean_del_object(v___x_4973_);
lean_dec(v_stop_4971_);
lean_dec(v_start_4970_);
lean_dec_ref(v_array_4969_);
return v_b_4968_;
}
else
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4979_; 
v___x_4976_ = lean_unsigned_to_nat(1u);
v___x_4977_ = lean_nat_add(v_start_4970_, v___x_4976_);
lean_inc_ref(v_array_4969_);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 1, v___x_4977_);
v___x_4979_ = v___x_4973_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_array_4969_);
lean_ctor_set(v_reuseFailAlloc_4983_, 1, v___x_4977_);
lean_ctor_set(v_reuseFailAlloc_4983_, 2, v_stop_4971_);
v___x_4979_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4980_ = lean_array_fget(v_array_4969_, v_start_4970_);
lean_dec(v_start_4970_);
lean_dec_ref(v_array_4969_);
v___x_4981_ = lean_array_push(v_b_4968_, v___x_4980_);
v_a_4967_ = v___x_4979_;
v_b_4968_ = v___x_4981_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4985_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
v___x_4986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
return v___x_4987_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4988_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4989_ = lean_unsigned_to_nat(0u);
v___x_4990_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
lean_ctor_set(v___x_4990_, 2, v___x_4989_);
lean_ctor_set(v___x_4990_, 3, v___x_4989_);
lean_ctor_set(v___x_4990_, 4, v___x_4988_);
lean_ctor_set(v___x_4990_, 5, v___x_4988_);
lean_ctor_set(v___x_4990_, 6, v___x_4988_);
lean_ctor_set(v___x_4990_, 7, v___x_4988_);
lean_ctor_set(v___x_4990_, 8, v___x_4988_);
lean_ctor_set(v___x_4990_, 9, v___x_4988_);
return v___x_4990_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4991_ = lean_box(1);
v___x_4992_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
lean_ctor_set(v___x_4994_, 1, v___x_4992_);
lean_ctor_set(v___x_4994_, 2, v___x_4991_);
return v___x_4994_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4996_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4997_ = l_Lean_stringToMessageData(v___x_4996_);
return v___x_4997_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4999_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_5000_ = l_Lean_stringToMessageData(v___x_4999_);
return v___x_5000_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5002_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_5003_ = l_Lean_stringToMessageData(v___x_5002_);
return v___x_5003_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5005_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_5006_ = l_Lean_stringToMessageData(v___x_5005_);
return v___x_5006_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_5009_ = l_Lean_stringToMessageData(v___x_5008_);
return v___x_5009_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_5012_ = l_Lean_stringToMessageData(v___x_5011_);
return v___x_5012_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5014_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_5015_ = l_Lean_stringToMessageData(v___x_5014_);
return v___x_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_5016_, lean_object* v_declHint_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v___x_5020_; lean_object* v_env_5021_; uint8_t v___x_5022_; 
v___x_5020_ = lean_st_ref_get(v___y_5018_);
v_env_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc_ref(v_env_5021_);
lean_dec(v___x_5020_);
v___x_5022_ = l_Lean_Name_isAnonymous(v_declHint_5017_);
if (v___x_5022_ == 0)
{
uint8_t v_isExporting_5023_; 
v_isExporting_5023_ = lean_ctor_get_uint8(v_env_5021_, sizeof(void*)*8);
if (v_isExporting_5023_ == 0)
{
lean_object* v___x_5024_; 
lean_dec_ref(v_env_5021_);
lean_dec(v_declHint_5017_);
v___x_5024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5024_, 0, v_msg_5016_);
return v___x_5024_;
}
else
{
lean_object* v___x_5025_; uint8_t v___x_5026_; 
lean_inc_ref(v_env_5021_);
v___x_5025_ = l_Lean_Environment_setExporting(v_env_5021_, v___x_5022_);
lean_inc(v_declHint_5017_);
lean_inc_ref(v___x_5025_);
v___x_5026_ = l_Lean_Environment_contains(v___x_5025_, v_declHint_5017_, v_isExporting_5023_);
if (v___x_5026_ == 0)
{
lean_object* v___x_5027_; 
lean_dec_ref(v___x_5025_);
lean_dec_ref(v_env_5021_);
lean_dec(v_declHint_5017_);
v___x_5027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5027_, 0, v_msg_5016_);
return v___x_5027_;
}
else
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v_c_5033_; lean_object* v___x_5034_; 
v___x_5028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_5029_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_5030_ = l_Lean_Options_empty;
v___x_5031_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5025_);
lean_ctor_set(v___x_5031_, 1, v___x_5028_);
lean_ctor_set(v___x_5031_, 2, v___x_5029_);
lean_ctor_set(v___x_5031_, 3, v___x_5030_);
lean_inc(v_declHint_5017_);
v___x_5032_ = l_Lean_MessageData_ofConstName(v_declHint_5017_, v___x_5022_);
v_c_5033_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_5033_, 0, v___x_5031_);
lean_ctor_set(v_c_5033_, 1, v___x_5032_);
v___x_5034_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5021_, v_declHint_5017_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
lean_dec_ref(v_env_5021_);
lean_dec(v_declHint_5017_);
v___x_5035_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_5036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
lean_ctor_set(v___x_5036_, 1, v_c_5033_);
v___x_5037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_5038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5036_);
lean_ctor_set(v___x_5038_, 1, v___x_5037_);
v___x_5039_ = l_Lean_MessageData_note(v___x_5038_);
v___x_5040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5040_, 0, v_msg_5016_);
lean_ctor_set(v___x_5040_, 1, v___x_5039_);
v___x_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5041_, 0, v___x_5040_);
return v___x_5041_;
}
else
{
lean_object* v_val_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5077_; 
v_val_5042_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5044_ = v___x_5034_;
v_isShared_5045_ = v_isSharedCheck_5077_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_val_5042_);
lean_dec(v___x_5034_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5077_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v_mod_5049_; uint8_t v___x_5050_; 
v___x_5046_ = lean_box(0);
v___x_5047_ = l_Lean_Environment_header(v_env_5021_);
lean_dec_ref(v_env_5021_);
v___x_5048_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5047_);
v_mod_5049_ = lean_array_get(v___x_5046_, v___x_5048_, v_val_5042_);
lean_dec(v_val_5042_);
lean_dec_ref(v___x_5048_);
v___x_5050_ = l_Lean_isPrivateName(v_declHint_5017_);
lean_dec(v_declHint_5017_);
if (v___x_5050_ == 0)
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5062_; 
v___x_5051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_5052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5051_);
lean_ctor_set(v___x_5052_, 1, v_c_5033_);
v___x_5053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_5054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5052_);
lean_ctor_set(v___x_5054_, 1, v___x_5053_);
v___x_5055_ = l_Lean_MessageData_ofName(v_mod_5049_);
v___x_5056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5054_);
lean_ctor_set(v___x_5056_, 1, v___x_5055_);
v___x_5057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_5058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5056_);
lean_ctor_set(v___x_5058_, 1, v___x_5057_);
v___x_5059_ = l_Lean_MessageData_note(v___x_5058_);
v___x_5060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5060_, 0, v_msg_5016_);
lean_ctor_set(v___x_5060_, 1, v___x_5059_);
if (v_isShared_5045_ == 0)
{
lean_ctor_set_tag(v___x_5044_, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5060_);
v___x_5062_ = v___x_5044_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
else
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5075_; 
v___x_5064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_5065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5064_);
lean_ctor_set(v___x_5065_, 1, v_c_5033_);
v___x_5066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_5067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5065_);
lean_ctor_set(v___x_5067_, 1, v___x_5066_);
v___x_5068_ = l_Lean_MessageData_ofName(v_mod_5049_);
v___x_5069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5067_);
lean_ctor_set(v___x_5069_, 1, v___x_5068_);
v___x_5070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_5071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5069_);
lean_ctor_set(v___x_5071_, 1, v___x_5070_);
v___x_5072_ = l_Lean_MessageData_note(v___x_5071_);
v___x_5073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5073_, 0, v_msg_5016_);
lean_ctor_set(v___x_5073_, 1, v___x_5072_);
if (v_isShared_5045_ == 0)
{
lean_ctor_set_tag(v___x_5044_, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5073_);
v___x_5075_ = v___x_5044_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5073_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5078_; 
lean_dec_ref(v_env_5021_);
lean_dec(v_declHint_5017_);
v___x_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5078_, 0, v_msg_5016_);
return v___x_5078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_5079_, lean_object* v_declHint_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v_res_5083_; 
v_res_5083_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5079_, v_declHint_5080_, v___y_5081_);
lean_dec(v___y_5081_);
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_5084_, lean_object* v_declHint_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v___x_5091_; lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5101_; 
v___x_5091_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5084_, v_declHint_5085_, v___y_5089_);
v_a_5092_ = lean_ctor_get(v___x_5091_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5091_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5094_ = v___x_5091_;
v_isShared_5095_ = v_isSharedCheck_5101_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v___x_5091_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5101_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5099_; 
v___x_5096_ = l_Lean_unknownIdentifierMessageTag;
v___x_5097_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5096_);
lean_ctor_set(v___x_5097_, 1, v_a_5092_);
if (v_isShared_5095_ == 0)
{
lean_ctor_set(v___x_5094_, 0, v___x_5097_);
v___x_5099_ = v___x_5094_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5097_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5102_, lean_object* v_declHint_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5102_, v_declHint_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
lean_dec(v___y_5105_);
lean_dec_ref(v___y_5104_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5110_, lean_object* v_msg_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_){
_start:
{
lean_object* v_fileName_5117_; lean_object* v_fileMap_5118_; lean_object* v_options_5119_; lean_object* v_currRecDepth_5120_; lean_object* v_maxRecDepth_5121_; lean_object* v_ref_5122_; lean_object* v_currNamespace_5123_; lean_object* v_openDecls_5124_; lean_object* v_initHeartbeats_5125_; lean_object* v_maxHeartbeats_5126_; lean_object* v_quotContext_5127_; lean_object* v_currMacroScope_5128_; uint8_t v_diag_5129_; lean_object* v_cancelTk_x3f_5130_; uint8_t v_suppressElabErrors_5131_; lean_object* v_inheritedTraceOptions_5132_; lean_object* v_ref_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; 
v_fileName_5117_ = lean_ctor_get(v___y_5114_, 0);
v_fileMap_5118_ = lean_ctor_get(v___y_5114_, 1);
v_options_5119_ = lean_ctor_get(v___y_5114_, 2);
v_currRecDepth_5120_ = lean_ctor_get(v___y_5114_, 3);
v_maxRecDepth_5121_ = lean_ctor_get(v___y_5114_, 4);
v_ref_5122_ = lean_ctor_get(v___y_5114_, 5);
v_currNamespace_5123_ = lean_ctor_get(v___y_5114_, 6);
v_openDecls_5124_ = lean_ctor_get(v___y_5114_, 7);
v_initHeartbeats_5125_ = lean_ctor_get(v___y_5114_, 8);
v_maxHeartbeats_5126_ = lean_ctor_get(v___y_5114_, 9);
v_quotContext_5127_ = lean_ctor_get(v___y_5114_, 10);
v_currMacroScope_5128_ = lean_ctor_get(v___y_5114_, 11);
v_diag_5129_ = lean_ctor_get_uint8(v___y_5114_, sizeof(void*)*14);
v_cancelTk_x3f_5130_ = lean_ctor_get(v___y_5114_, 12);
v_suppressElabErrors_5131_ = lean_ctor_get_uint8(v___y_5114_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5132_ = lean_ctor_get(v___y_5114_, 13);
v_ref_5133_ = l_Lean_replaceRef(v_ref_5110_, v_ref_5122_);
lean_inc_ref(v_inheritedTraceOptions_5132_);
lean_inc(v_cancelTk_x3f_5130_);
lean_inc(v_currMacroScope_5128_);
lean_inc(v_quotContext_5127_);
lean_inc(v_maxHeartbeats_5126_);
lean_inc(v_initHeartbeats_5125_);
lean_inc(v_openDecls_5124_);
lean_inc(v_currNamespace_5123_);
lean_inc(v_maxRecDepth_5121_);
lean_inc(v_currRecDepth_5120_);
lean_inc_ref(v_options_5119_);
lean_inc_ref(v_fileMap_5118_);
lean_inc_ref(v_fileName_5117_);
v___x_5134_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5134_, 0, v_fileName_5117_);
lean_ctor_set(v___x_5134_, 1, v_fileMap_5118_);
lean_ctor_set(v___x_5134_, 2, v_options_5119_);
lean_ctor_set(v___x_5134_, 3, v_currRecDepth_5120_);
lean_ctor_set(v___x_5134_, 4, v_maxRecDepth_5121_);
lean_ctor_set(v___x_5134_, 5, v_ref_5133_);
lean_ctor_set(v___x_5134_, 6, v_currNamespace_5123_);
lean_ctor_set(v___x_5134_, 7, v_openDecls_5124_);
lean_ctor_set(v___x_5134_, 8, v_initHeartbeats_5125_);
lean_ctor_set(v___x_5134_, 9, v_maxHeartbeats_5126_);
lean_ctor_set(v___x_5134_, 10, v_quotContext_5127_);
lean_ctor_set(v___x_5134_, 11, v_currMacroScope_5128_);
lean_ctor_set(v___x_5134_, 12, v_cancelTk_x3f_5130_);
lean_ctor_set(v___x_5134_, 13, v_inheritedTraceOptions_5132_);
lean_ctor_set_uint8(v___x_5134_, sizeof(void*)*14, v_diag_5129_);
lean_ctor_set_uint8(v___x_5134_, sizeof(void*)*14 + 1, v_suppressElabErrors_5131_);
v___x_5135_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5111_, v___y_5112_, v___y_5113_, v___x_5134_, v___y_5115_);
lean_dec_ref_known(v___x_5134_, 14);
return v___x_5135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5136_, lean_object* v_msg_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5136_, v_msg_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v_ref_5136_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5144_, lean_object* v_msg_5145_, lean_object* v_declHint_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_){
_start:
{
lean_object* v___x_5152_; lean_object* v_a_5153_; lean_object* v___x_5154_; 
v___x_5152_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5145_, v_declHint_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_);
v_a_5153_ = lean_ctor_get(v___x_5152_, 0);
lean_inc(v_a_5153_);
lean_dec_ref(v___x_5152_);
v___x_5154_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5144_, v_a_5153_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5155_, lean_object* v_msg_5156_, lean_object* v_declHint_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5155_, v_msg_5156_, v_declHint_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
lean_dec(v___y_5161_);
lean_dec_ref(v___y_5160_);
lean_dec(v___y_5159_);
lean_dec_ref(v___y_5158_);
lean_dec(v_ref_5155_);
return v_res_5163_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5165_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5166_ = l_Lean_stringToMessageData(v___x_5165_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5167_, lean_object* v_constName_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_){
_start:
{
lean_object* v___x_5174_; uint8_t v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5174_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5175_ = 0;
lean_inc(v_constName_5168_);
v___x_5176_ = l_Lean_MessageData_ofConstName(v_constName_5168_, v___x_5175_);
v___x_5177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5174_);
lean_ctor_set(v___x_5177_, 1, v___x_5176_);
v___x_5178_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5177_);
lean_ctor_set(v___x_5179_, 1, v___x_5178_);
v___x_5180_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5167_, v___x_5179_, v_constName_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5181_, lean_object* v_constName_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5181_, v_constName_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec(v_ref_5181_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
lean_object* v_ref_5195_; lean_object* v___x_5196_; 
v_ref_5195_ = lean_ctor_get(v___y_5192_, 5);
v___x_5196_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5195_, v_constName_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_);
lean_dec(v___y_5201_);
lean_dec_ref(v___y_5200_);
lean_dec(v___y_5199_);
lean_dec_ref(v___y_5198_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v___x_5210_; lean_object* v_env_5211_; uint8_t v___x_5212_; lean_object* v___x_5213_; 
v___x_5210_ = lean_st_ref_get(v___y_5208_);
v_env_5211_ = lean_ctor_get(v___x_5210_, 0);
lean_inc_ref(v_env_5211_);
lean_dec(v___x_5210_);
v___x_5212_ = 0;
lean_inc(v_constName_5204_);
v___x_5213_ = l_Lean_Environment_find_x3f(v_env_5211_, v_constName_5204_, v___x_5212_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_object* v___x_5214_; 
v___x_5214_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
return v___x_5214_;
}
else
{
lean_object* v_val_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5222_; 
lean_dec(v_constName_5204_);
v_val_5215_ = lean_ctor_get(v___x_5213_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5213_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5217_ = v___x_5213_;
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_val_5215_);
lean_dec(v___x_5213_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5220_; 
if (v_isShared_5218_ == 0)
{
lean_ctor_set_tag(v___x_5217_, 0);
v___x_5220_ = v___x_5217_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_val_5215_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_);
lean_dec(v___y_5227_);
lean_dec_ref(v___y_5226_);
lean_dec(v___y_5225_);
lean_dec_ref(v___y_5224_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5232_, lean_object* v_x_5233_, lean_object* v_x_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_){
_start:
{
if (lean_obj_tag(v_x_5232_) == 5)
{
lean_object* v_fn_5240_; lean_object* v_arg_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; 
v_fn_5240_ = lean_ctor_get(v_x_5232_, 0);
lean_inc_ref(v_fn_5240_);
v_arg_5241_ = lean_ctor_get(v_x_5232_, 1);
lean_inc_ref(v_arg_5241_);
lean_dec_ref_known(v_x_5232_, 2);
v___x_5242_ = lean_array_set(v_x_5233_, v_x_5234_, v_arg_5241_);
v___x_5243_ = lean_unsigned_to_nat(1u);
v___x_5244_ = lean_nat_sub(v_x_5234_, v___x_5243_);
lean_dec(v_x_5234_);
v_x_5232_ = v_fn_5240_;
v_x_5233_ = v___x_5242_;
v_x_5234_ = v___x_5244_;
goto _start;
}
else
{
lean_dec(v_x_5234_);
if (lean_obj_tag(v_x_5232_) == 4)
{
lean_object* v_declName_5246_; lean_object* v___x_5247_; 
v_declName_5246_ = lean_ctor_get(v_x_5232_, 0);
lean_inc(v_declName_5246_);
lean_dec_ref_known(v_x_5232_, 2);
v___x_5247_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5246_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; lean_object* v___x_5250_; uint8_t v_isShared_5251_; uint8_t v_isSharedCheck_5279_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_5247_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5250_ = v___x_5247_;
v_isShared_5251_ = v_isSharedCheck_5279_;
goto v_resetjp_5249_;
}
else
{
lean_inc(v_a_5248_);
lean_dec(v___x_5247_);
v___x_5250_ = lean_box(0);
v_isShared_5251_ = v_isSharedCheck_5279_;
goto v_resetjp_5249_;
}
v_resetjp_5249_:
{
lean_object* v_lower_5253_; lean_object* v_upper_5254_; 
if (lean_obj_tag(v_a_5248_) == 5)
{
lean_object* v_val_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5276_; 
v_val_5262_ = lean_ctor_get(v_a_5248_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v_a_5248_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5264_ = v_a_5248_;
v_isShared_5265_ = v_isSharedCheck_5276_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_val_5262_);
lean_dec(v_a_5248_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5276_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v_numParams_5266_; lean_object* v_numIndices_5267_; lean_object* v___x_5268_; uint8_t v___x_5269_; 
v_numParams_5266_ = lean_ctor_get(v_val_5262_, 1);
lean_inc(v_numParams_5266_);
v_numIndices_5267_ = lean_ctor_get(v_val_5262_, 2);
lean_inc(v_numIndices_5267_);
lean_dec_ref(v_val_5262_);
v___x_5268_ = lean_unsigned_to_nat(0u);
v___x_5269_ = lean_nat_dec_eq(v_numIndices_5267_, v___x_5268_);
lean_dec(v_numIndices_5267_);
if (v___x_5269_ == 0)
{
lean_object* v___x_5270_; uint8_t v___x_5271_; 
lean_del_object(v___x_5264_);
v___x_5270_ = lean_array_get_size(v_x_5233_);
v___x_5271_ = lean_nat_dec_le(v_numParams_5266_, v___x_5268_);
if (v___x_5271_ == 0)
{
v_lower_5253_ = v_numParams_5266_;
v_upper_5254_ = v___x_5270_;
goto v___jp_5252_;
}
else
{
lean_dec(v_numParams_5266_);
v_lower_5253_ = v___x_5268_;
v_upper_5254_ = v___x_5270_;
goto v___jp_5252_;
}
}
else
{
lean_object* v___x_5272_; lean_object* v___x_5274_; 
lean_dec(v_numParams_5266_);
lean_del_object(v___x_5250_);
lean_dec_ref(v_x_5233_);
v___x_5272_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5265_ == 0)
{
lean_ctor_set_tag(v___x_5264_, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5272_);
v___x_5274_ = v___x_5264_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5272_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
}
else
{
lean_object* v___x_5277_; lean_object* v___x_5278_; 
lean_del_object(v___x_5250_);
lean_dec(v_a_5248_);
lean_dec_ref(v_x_5233_);
v___x_5277_ = lean_box(0);
v___x_5278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5277_);
return v___x_5278_;
}
v___jp_5252_:
{
lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5260_; 
v___x_5255_ = l_Array_toSubarray___redArg(v_x_5233_, v_lower_5253_, v_upper_5254_);
v___x_5256_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5257_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5255_, v___x_5256_);
v___x_5258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5258_, 0, v___x_5257_);
if (v_isShared_5251_ == 0)
{
lean_ctor_set(v___x_5250_, 0, v___x_5258_);
v___x_5260_ = v___x_5250_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v___x_5258_);
v___x_5260_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
return v___x_5260_;
}
}
}
}
else
{
lean_object* v_a_5280_; lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5287_; 
lean_dec_ref(v_x_5233_);
v_a_5280_ = lean_ctor_get(v___x_5247_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5247_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5282_ = v___x_5247_;
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
else
{
lean_inc(v_a_5280_);
lean_dec(v___x_5247_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5285_; 
if (v_isShared_5283_ == 0)
{
v___x_5285_ = v___x_5282_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
else
{
lean_object* v___x_5288_; lean_object* v___x_5289_; 
lean_dec_ref(v_x_5233_);
lean_dec_ref(v_x_5232_);
v___x_5288_ = lean_box(0);
v___x_5289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5288_);
return v___x_5289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5290_, lean_object* v_x_5291_, lean_object* v_x_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5290_, v_x_5291_, v_x_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
lean_dec(v___y_5296_);
lean_dec_ref(v___y_5295_);
lean_dec(v___y_5294_);
lean_dec_ref(v___y_5293_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_){
_start:
{
lean_object* v___x_5305_; 
lean_inc(v_a_5303_);
lean_inc_ref(v_a_5302_);
lean_inc(v_a_5301_);
lean_inc_ref(v_a_5300_);
v___x_5305_ = lean_infer_type(v_ctorApp_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5307_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
lean_inc(v_a_5306_);
lean_dec_ref_known(v___x_5305_, 1);
v___x_5307_ = l_Lean_Meta_whnfD(v_a_5306_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v_dummy_5309_; lean_object* v_nargs_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
lean_dec_ref_known(v___x_5307_, 1);
v_dummy_5309_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5310_ = l_Lean_Expr_getAppNumArgs(v_a_5308_);
lean_inc(v_nargs_5310_);
v___x_5311_ = lean_mk_array(v_nargs_5310_, v_dummy_5309_);
v___x_5312_ = lean_unsigned_to_nat(1u);
v___x_5313_ = lean_nat_sub(v_nargs_5310_, v___x_5312_);
lean_dec(v_nargs_5310_);
v___x_5314_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5308_, v___x_5311_, v___x_5313_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
return v___x_5314_;
}
else
{
lean_object* v_a_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5322_; 
v_a_5315_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5317_ = v___x_5307_;
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_a_5315_);
lean_dec(v___x_5307_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5320_; 
if (v_isShared_5318_ == 0)
{
v___x_5320_ = v___x_5317_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5315_);
v___x_5320_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
return v___x_5320_;
}
}
}
}
else
{
lean_object* v_a_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5330_; 
v_a_5323_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5325_ = v___x_5305_;
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_a_5323_);
lean_dec(v___x_5305_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
lean_dec(v_a_5335_);
lean_dec_ref(v_a_5334_);
lean_dec(v_a_5333_);
lean_dec_ref(v_a_5332_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5338_, lean_object* v_R_5339_, lean_object* v_a_5340_, lean_object* v_b_5341_){
_start:
{
lean_object* v___x_5342_; 
v___x_5342_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5340_, v_b_5341_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5343_, lean_object* v_constName_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_){
_start:
{
lean_object* v___x_5350_; 
v___x_5350_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
return v___x_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5351_, lean_object* v_constName_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5351_, v_constName_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_);
lean_dec(v___y_5356_);
lean_dec_ref(v___y_5355_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5359_, lean_object* v_ref_5360_, lean_object* v_constName_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v___x_5367_; 
v___x_5367_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5360_, v_constName_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
return v___x_5367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5368_, lean_object* v_ref_5369_, lean_object* v_constName_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5368_, v_ref_5369_, v_constName_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v_ref_5369_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5377_, lean_object* v_ref_5378_, lean_object* v_msg_5379_, lean_object* v_declHint_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_){
_start:
{
lean_object* v___x_5386_; 
v___x_5386_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5378_, v_msg_5379_, v_declHint_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
return v___x_5386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5387_, lean_object* v_ref_5388_, lean_object* v_msg_5389_, lean_object* v_declHint_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5387_, v_ref_5388_, v_msg_5389_, v_declHint_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec(v_ref_5388_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5397_, lean_object* v_declHint_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_){
_start:
{
lean_object* v___x_5404_; 
v___x_5404_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5397_, v_declHint_5398_, v___y_5402_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5405_, lean_object* v_declHint_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v_res_5412_; 
v_res_5412_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5405_, v_declHint_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
return v_res_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5413_, lean_object* v_ref_5414_, lean_object* v_msg_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
lean_object* v___x_5421_; 
v___x_5421_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5414_, v_msg_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5422_, lean_object* v_ref_5423_, lean_object* v_msg_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_){
_start:
{
lean_object* v_res_5430_; 
v_res_5430_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5422_, v_ref_5423_, v_msg_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_);
lean_dec(v___y_5428_);
lean_dec_ref(v___y_5427_);
lean_dec(v___y_5426_);
lean_dec_ref(v___y_5425_);
lean_dec(v_ref_5423_);
return v_res_5430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5431_, lean_object* v_body_5432_, lean_object* v_args2_5433_, lean_object* v_ctorVal_5434_, lean_object* v_args1_5435_, lean_object* v_k_5436_, lean_object* v_arg2_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_){
_start:
{
lean_object* v_res_5443_; 
v_res_5443_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5431_, v_body_5432_, v_args2_5433_, v_ctorVal_5434_, v_args1_5435_, v_k_5436_, v_arg2_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
lean_dec(v___y_5439_);
lean_dec_ref(v___y_5438_);
lean_dec_ref(v_body_5432_);
lean_dec(v_i_5431_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5444_, lean_object* v_args1_5445_, lean_object* v_k_5446_, lean_object* v_i_5447_, lean_object* v_type_5448_, lean_object* v_args2_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_){
_start:
{
lean_object* v___x_5455_; uint8_t v___x_5456_; 
v___x_5455_ = lean_array_get_size(v_args1_5445_);
v___x_5456_ = lean_nat_dec_lt(v_i_5447_, v___x_5455_);
if (v___x_5456_ == 0)
{
lean_object* v___x_5457_; 
lean_dec_ref(v_type_5448_);
lean_dec(v_i_5447_);
lean_dec_ref(v_args1_5445_);
lean_dec_ref(v_ctorVal_5444_);
lean_inc(v_a_5453_);
lean_inc_ref(v_a_5452_);
lean_inc(v_a_5451_);
lean_inc_ref(v_a_5450_);
v___x_5457_ = lean_apply_6(v_k_5446_, v_args2_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, lean_box(0));
return v___x_5457_;
}
else
{
lean_object* v___x_5458_; 
lean_inc(v_a_5453_);
lean_inc_ref(v_a_5452_);
lean_inc(v_a_5451_);
lean_inc_ref(v_a_5450_);
v___x_5458_ = lean_whnf(v_type_5448_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_);
if (lean_obj_tag(v___x_5458_) == 0)
{
lean_object* v_a_5459_; 
v_a_5459_ = lean_ctor_get(v___x_5458_, 0);
lean_inc(v_a_5459_);
lean_dec_ref_known(v___x_5458_, 1);
if (lean_obj_tag(v_a_5459_) == 7)
{
lean_object* v_binderName_5460_; lean_object* v_binderType_5461_; lean_object* v_body_5462_; lean_object* v___f_5463_; uint8_t v___x_5464_; uint8_t v___x_5465_; lean_object* v___x_5466_; 
v_binderName_5460_ = lean_ctor_get(v_a_5459_, 0);
lean_inc(v_binderName_5460_);
v_binderType_5461_ = lean_ctor_get(v_a_5459_, 1);
lean_inc_ref(v_binderType_5461_);
v_body_5462_ = lean_ctor_get(v_a_5459_, 2);
lean_inc_ref(v_body_5462_);
lean_dec_ref_known(v_a_5459_, 3);
v___f_5463_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5463_, 0, v_i_5447_);
lean_closure_set(v___f_5463_, 1, v_body_5462_);
lean_closure_set(v___f_5463_, 2, v_args2_5449_);
lean_closure_set(v___f_5463_, 3, v_ctorVal_5444_);
lean_closure_set(v___f_5463_, 4, v_args1_5445_);
lean_closure_set(v___f_5463_, 5, v_k_5446_);
v___x_5464_ = 1;
v___x_5465_ = 0;
v___x_5466_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5460_, v___x_5464_, v_binderType_5461_, v___f_5463_, v___x_5465_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_);
return v___x_5466_;
}
else
{
lean_object* v_toConstantVal_5467_; lean_object* v_name_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; 
lean_dec(v_a_5459_);
lean_dec_ref(v_args2_5449_);
lean_dec(v_i_5447_);
lean_dec_ref(v_k_5446_);
lean_dec_ref(v_args1_5445_);
v_toConstantVal_5467_ = lean_ctor_get(v_ctorVal_5444_, 0);
lean_inc_ref(v_toConstantVal_5467_);
lean_dec_ref(v_ctorVal_5444_);
v_name_5468_ = lean_ctor_get(v_toConstantVal_5467_, 0);
lean_inc(v_name_5468_);
lean_dec_ref(v_toConstantVal_5467_);
v___x_5469_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5470_ = l_Lean_MessageData_ofName(v_name_5468_);
v___x_5471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5471_, 0, v___x_5469_);
lean_ctor_set(v___x_5471_, 1, v___x_5470_);
v___x_5472_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5473_, 0, v___x_5471_);
lean_ctor_set(v___x_5473_, 1, v___x_5472_);
v___x_5474_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5473_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_);
return v___x_5474_;
}
}
else
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
lean_dec_ref(v_args2_5449_);
lean_dec(v_i_5447_);
lean_dec_ref(v_k_5446_);
lean_dec_ref(v_args1_5445_);
lean_dec_ref(v_ctorVal_5444_);
v_a_5475_ = lean_ctor_get(v___x_5458_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5458_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5477_ = v___x_5458_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5458_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5480_; 
if (v_isShared_5478_ == 0)
{
v___x_5480_ = v___x_5477_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_a_5475_);
v___x_5480_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
return v___x_5480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5483_, lean_object* v_body_5484_, lean_object* v_args2_5485_, lean_object* v_ctorVal_5486_, lean_object* v_args1_5487_, lean_object* v_k_5488_, lean_object* v_arg2_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_){
_start:
{
lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
v___x_5495_ = lean_unsigned_to_nat(1u);
v___x_5496_ = lean_nat_add(v_i_5483_, v___x_5495_);
v___x_5497_ = lean_expr_instantiate1(v_body_5484_, v_arg2_5489_);
v___x_5498_ = lean_array_push(v_args2_5485_, v_arg2_5489_);
v___x_5499_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5486_, v_args1_5487_, v_k_5488_, v___x_5496_, v___x_5497_, v___x_5498_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
return v___x_5499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5500_, lean_object* v_args1_5501_, lean_object* v_k_5502_, lean_object* v_i_5503_, lean_object* v_type_5504_, lean_object* v_args2_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_){
_start:
{
lean_object* v_res_5511_; 
v_res_5511_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5500_, v_args1_5501_, v_k_5502_, v_i_5503_, v_type_5504_, v_args2_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_);
lean_dec(v_a_5509_);
lean_dec_ref(v_a_5508_);
lean_dec(v_a_5507_);
lean_dec_ref(v_a_5506_);
return v_res_5511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5512_, lean_object* v_us_5513_, lean_object* v_args1_5514_, lean_object* v___x_5515_, lean_object* v_numParams_5516_, lean_object* v___x_5517_, lean_object* v_args2_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_){
_start:
{
lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; 
lean_inc(v_us_5513_);
v___x_5524_ = l_Lean_mkConst(v_name_5512_, v_us_5513_);
lean_inc_ref(v___x_5524_);
v___x_5525_ = l_Lean_mkAppN(v___x_5524_, v_args1_5514_);
v___x_5526_ = l_Lean_mkAppN(v___x_5524_, v_args2_5518_);
lean_inc_ref(v___x_5526_);
lean_inc_ref(v___x_5525_);
v___x_5527_ = l_Lean_Meta_mkEqHEq(v___x_5525_, v___x_5526_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
if (lean_obj_tag(v___x_5527_) == 0)
{
lean_object* v_a_5528_; lean_object* v___x_5529_; uint8_t v___x_5530_; lean_object* v___x_5531_; 
v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
lean_inc(v_a_5528_);
lean_dec_ref_known(v___x_5527_, 1);
lean_inc_ref_n(v_args2_5518_, 2);
v___x_5529_ = l_Array_toSubarray___redArg(v_args2_5518_, v___x_5515_, v_numParams_5516_);
v___x_5530_ = 1;
v___x_5531_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5514_, v_args2_5518_, v___x_5530_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
if (lean_obj_tag(v___x_5531_) == 0)
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5652_; 
v_a_5532_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5652_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5652_ == 0)
{
v___x_5534_ = v___x_5531_;
v_isShared_5535_ = v_isSharedCheck_5652_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5531_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5652_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5536_; 
v___x_5536_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5532_);
if (lean_obj_tag(v___x_5536_) == 1)
{
lean_object* v_val_5537_; lean_object* v___x_5538_; 
lean_del_object(v___x_5534_);
v_val_5537_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_val_5537_);
lean_dec_ref_known(v___x_5536_, 1);
v___x_5538_ = l_Lean_mkArrow(v_a_5528_, v_val_5537_, v___y_5521_, v___y_5522_);
if (lean_obj_tag(v___x_5538_) == 0)
{
lean_object* v_a_5539_; lean_object* v___x_5540_; 
v_a_5539_ = lean_ctor_get(v___x_5538_, 0);
lean_inc(v_a_5539_);
lean_dec_ref_known(v___x_5538_, 1);
v___x_5540_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5525_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
if (lean_obj_tag(v___x_5540_) == 0)
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5631_; 
v_a_5541_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5543_ = v___x_5540_;
v_isShared_5544_ = v_isSharedCheck_5631_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5540_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5631_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
if (lean_obj_tag(v_a_5541_) == 1)
{
lean_object* v_val_5545_; lean_object* v___x_5546_; 
lean_del_object(v___x_5543_);
v_val_5545_ = lean_ctor_get(v_a_5541_, 0);
lean_inc(v_val_5545_);
lean_dec_ref_known(v_a_5541_, 1);
v___x_5546_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5526_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
if (lean_obj_tag(v___x_5546_) == 0)
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5618_; 
v_a_5547_ = lean_ctor_get(v___x_5546_, 0);
v_isSharedCheck_5618_ = !lean_is_exclusive(v___x_5546_);
if (v_isSharedCheck_5618_ == 0)
{
v___x_5549_ = v___x_5546_;
v_isShared_5550_ = v_isSharedCheck_5618_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5546_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5618_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
if (lean_obj_tag(v_a_5547_) == 1)
{
lean_object* v_val_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5613_; 
lean_del_object(v___x_5549_);
v_val_5551_ = lean_ctor_get(v_a_5547_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v_a_5547_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5553_ = v_a_5547_;
v_isShared_5554_ = v_isSharedCheck_5613_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_val_5551_);
lean_dec(v_a_5547_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5613_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; uint8_t v___x_5559_; lean_object* v___x_5560_; 
v___x_5555_ = l_Subarray_copy___redArg(v___x_5517_);
v___x_5556_ = l_Array_append___redArg(v___x_5555_, v_val_5545_);
v___x_5557_ = l_Subarray_copy___redArg(v___x_5529_);
v___x_5558_ = l_Array_append___redArg(v___x_5557_, v_val_5551_);
lean_dec(v_val_5551_);
v___x_5559_ = 0;
v___x_5560_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5556_, v___x_5558_, v___x_5559_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
lean_dec_ref(v___x_5556_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v_a_5561_; lean_object* v___x_5562_; 
v_a_5561_ = lean_ctor_get(v___x_5560_, 0);
lean_inc(v_a_5561_);
lean_dec_ref_known(v___x_5560_, 1);
v___x_5562_ = l_Lean_mkArrowN(v_a_5561_, v_a_5539_, v___y_5521_, v___y_5522_);
lean_dec(v_a_5561_);
if (lean_obj_tag(v___x_5562_) == 0)
{
lean_object* v_a_5563_; uint8_t v___x_5564_; lean_object* v___x_5565_; 
v_a_5563_ = lean_ctor_get(v___x_5562_, 0);
lean_inc(v_a_5563_);
lean_dec_ref_known(v___x_5562_, 1);
v___x_5564_ = 1;
v___x_5565_ = l_Lean_Meta_mkForallFVars(v_args2_5518_, v_a_5563_, v___x_5559_, v___x_5530_, v___x_5530_, v___x_5564_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
lean_dec_ref(v_args2_5518_);
if (lean_obj_tag(v___x_5565_) == 0)
{
lean_object* v_a_5566_; lean_object* v___x_5567_; 
v_a_5566_ = lean_ctor_get(v___x_5565_, 0);
lean_inc(v_a_5566_);
lean_dec_ref_known(v___x_5565_, 1);
v___x_5567_ = l_Lean_Meta_mkForallFVars(v_args1_5514_, v_a_5566_, v___x_5559_, v___x_5530_, v___x_5530_, v___x_5564_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
if (lean_obj_tag(v___x_5567_) == 0)
{
lean_object* v_a_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5580_; 
v_a_5568_ = lean_ctor_get(v___x_5567_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5567_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5570_ = v___x_5567_;
v_isShared_5571_ = v_isSharedCheck_5580_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_a_5568_);
lean_dec(v___x_5567_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5580_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5575_; 
v___x_5572_ = lean_array_get_size(v_val_5545_);
lean_dec(v_val_5545_);
v___x_5573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5573_, 0, v_a_5568_);
lean_ctor_set(v___x_5573_, 1, v_us_5513_);
lean_ctor_set(v___x_5573_, 2, v___x_5572_);
if (v_isShared_5554_ == 0)
{
lean_ctor_set(v___x_5553_, 0, v___x_5573_);
v___x_5575_ = v___x_5553_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5573_);
v___x_5575_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
lean_object* v___x_5577_; 
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 0, v___x_5575_);
v___x_5577_ = v___x_5570_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5575_);
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
else
{
lean_object* v_a_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5588_; 
lean_del_object(v___x_5553_);
lean_dec(v_val_5545_);
lean_dec(v_us_5513_);
v_a_5581_ = lean_ctor_get(v___x_5567_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5567_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5583_ = v___x_5567_;
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5567_);
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
lean_del_object(v___x_5553_);
lean_dec(v_val_5545_);
lean_dec(v_us_5513_);
v_a_5589_ = lean_ctor_get(v___x_5565_, 0);
v_isSharedCheck_5596_ = !lean_is_exclusive(v___x_5565_);
if (v_isSharedCheck_5596_ == 0)
{
v___x_5591_ = v___x_5565_;
v_isShared_5592_ = v_isSharedCheck_5596_;
goto v_resetjp_5590_;
}
else
{
lean_inc(v_a_5589_);
lean_dec(v___x_5565_);
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
else
{
lean_object* v_a_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5604_; 
lean_del_object(v___x_5553_);
lean_dec(v_val_5545_);
lean_dec_ref(v_args2_5518_);
lean_dec(v_us_5513_);
v_a_5597_ = lean_ctor_get(v___x_5562_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5562_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5599_ = v___x_5562_;
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_a_5597_);
lean_dec(v___x_5562_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5602_; 
if (v_isShared_5600_ == 0)
{
v___x_5602_ = v___x_5599_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_a_5597_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
}
else
{
lean_object* v_a_5605_; lean_object* v___x_5607_; uint8_t v_isShared_5608_; uint8_t v_isSharedCheck_5612_; 
lean_del_object(v___x_5553_);
lean_dec(v_val_5545_);
lean_dec(v_a_5539_);
lean_dec_ref(v_args2_5518_);
lean_dec(v_us_5513_);
v_a_5605_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5612_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5612_ == 0)
{
v___x_5607_ = v___x_5560_;
v_isShared_5608_ = v_isSharedCheck_5612_;
goto v_resetjp_5606_;
}
else
{
lean_inc(v_a_5605_);
lean_dec(v___x_5560_);
v___x_5607_ = lean_box(0);
v_isShared_5608_ = v_isSharedCheck_5612_;
goto v_resetjp_5606_;
}
v_resetjp_5606_:
{
lean_object* v___x_5610_; 
if (v_isShared_5608_ == 0)
{
v___x_5610_ = v___x_5607_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v_a_5605_);
v___x_5610_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
return v___x_5610_;
}
}
}
}
}
else
{
lean_object* v___x_5614_; lean_object* v___x_5616_; 
lean_dec(v_a_5547_);
lean_dec(v_val_5545_);
lean_dec(v_a_5539_);
lean_dec_ref(v___x_5529_);
lean_dec_ref(v_args2_5518_);
lean_dec_ref(v___x_5517_);
lean_dec(v_us_5513_);
v___x_5614_ = lean_box(0);
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 0, v___x_5614_);
v___x_5616_ = v___x_5549_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v___x_5614_);
v___x_5616_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
return v___x_5616_;
}
}
}
}
else
{
lean_object* v_a_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5626_; 
lean_dec(v_val_5545_);
lean_dec(v_a_5539_);
lean_dec_ref(v___x_5529_);
lean_dec_ref(v_args2_5518_);
lean_dec_ref(v___x_5517_);
lean_dec(v_us_5513_);
v_a_5619_ = lean_ctor_get(v___x_5546_, 0);
v_isSharedCheck_5626_ = !lean_is_exclusive(v___x_5546_);
if (v_isSharedCheck_5626_ == 0)
{
v___x_5621_ = v___x_5546_;
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_a_5619_);
lean_dec(v___x_5546_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5624_; 
if (v_isShared_5622_ == 0)
{
v___x_5624_ = v___x_5621_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v_a_5619_);
v___x_5624_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
return v___x_5624_;
}
}
}
}
else
{
lean_object* v___x_5627_; lean_object* v___x_5629_; 
lean_dec(v_a_5541_);
lean_dec(v_a_5539_);
lean_dec_ref(v___x_5529_);
lean_dec_ref(v___x_5526_);
lean_dec_ref(v_args2_5518_);
lean_dec_ref(v___x_5517_);
lean_dec(v_us_5513_);
v___x_5627_ = lean_box(0);
if (v_isShared_5544_ == 0)
{
lean_ctor_set(v___x_5543_, 0, v___x_5627_);
v___x_5629_ = v___x_5543_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5627_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec(v_a_5539_);
lean_dec_ref(v___x_5529_);
lean_dec_ref(v___x_5526_);
lean_dec_ref(v_args2_5518_);
lean_dec_ref(v___x_5517_);
lean_dec(v_us_5513_);
v_a_5632_ = lean_ctor_get(v___x_5540_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5540_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5540_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5540_);
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
lean_object* v_a_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5647_; 
lean_dec_ref(v___x_5529_);
lean_dec_ref(v___x_5526_);
lean_dec_ref(v___x_5525_);
lean_dec_ref(v_args2_5518_);
lean_dec_ref(v___x_5517_);
lean_dec(v_us_5513_);
v_a_5640_ = lean_ctor_get(v___x_5538_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5538_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5642_ = v___x_5538_;
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_a_5640_);
lean_dec(v___x_5538_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v___x_5645_; 
if (v_isShared_5643_ == 0)
{
v___x_5645_ = v___x_5642_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_a_5640_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
else
{
lean_object* v___x_5648_; lean_object* v___x_5650_; 
lean_dec(v___x_5536_);
lean_dec_ref(v___x_5529_);
lean_dec(v_a_5528_);
lean_dec_ref(v___x_5526_);
lean_dec_ref(v___x_5525_);
lean_dec_ref(v_args2_5518_);
lean_dec_ref(v___x_5517_);
lean_dec(v_us_5513_);
v___x_5648_ = lean_box(0);
if (v_isShared_5535_ == 0)
{
lean_ctor_set(v___x_5534_, 0, v___x_5648_);
v___x_5650_ = v___x_5534_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5648_);
v___x_5650_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
return v___x_5650_;
}
}
}
}
else
{
lean_object* v_a_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5660_; 
lean_dec_ref(v___x_5529_);
lean_dec(v_a_5528_);
lean_dec_ref(v___x_5526_);
lean_dec_ref(v___x_5525_);
lean_dec_ref(v_args2_5518_);
lean_dec_ref(v___x_5517_);
lean_dec(v_us_5513_);
v_a_5653_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5660_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5660_ == 0)
{
v___x_5655_ = v___x_5531_;
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_a_5653_);
lean_dec(v___x_5531_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v___x_5658_; 
if (v_isShared_5656_ == 0)
{
v___x_5658_ = v___x_5655_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
v___x_5658_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
return v___x_5658_;
}
}
}
}
else
{
lean_object* v_a_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5668_; 
lean_dec_ref(v___x_5526_);
lean_dec_ref(v___x_5525_);
lean_dec_ref(v_args2_5518_);
lean_dec_ref(v___x_5517_);
lean_dec(v_numParams_5516_);
lean_dec(v___x_5515_);
lean_dec(v_us_5513_);
v_a_5661_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5668_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5668_ == 0)
{
v___x_5663_ = v___x_5527_;
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_a_5661_);
lean_dec(v___x_5527_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5666_; 
if (v_isShared_5664_ == 0)
{
v___x_5666_ = v___x_5663_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_a_5661_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5669_, lean_object* v_us_5670_, lean_object* v_args1_5671_, lean_object* v___x_5672_, lean_object* v_numParams_5673_, lean_object* v___x_5674_, lean_object* v_args2_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_){
_start:
{
lean_object* v_res_5681_; 
v_res_5681_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5669_, v_us_5670_, v_args1_5671_, v___x_5672_, v_numParams_5673_, v___x_5674_, v_args2_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec_ref(v_args1_5671_);
return v_res_5681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5682_, lean_object* v_name_5683_, lean_object* v_us_5684_, lean_object* v_ctorVal_5685_, lean_object* v_a_5686_, lean_object* v_args1_5687_, lean_object* v_x_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___f_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5694_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5682_);
lean_inc_ref_n(v_args1_5687_, 3);
v___x_5695_ = l_Array_toSubarray___redArg(v_args1_5687_, v___x_5694_, v_numParams_5682_);
v___f_5696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5696_, 0, v_name_5683_);
lean_closure_set(v___f_5696_, 1, v_us_5684_);
lean_closure_set(v___f_5696_, 2, v_args1_5687_);
lean_closure_set(v___f_5696_, 3, v___x_5694_);
lean_closure_set(v___f_5696_, 4, v_numParams_5682_);
lean_closure_set(v___f_5696_, 5, v___x_5695_);
v___x_5697_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5698_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5698_, 0, v_ctorVal_5685_);
lean_closure_set(v___x_5698_, 1, v_args1_5687_);
lean_closure_set(v___x_5698_, 2, v___f_5696_);
lean_closure_set(v___x_5698_, 3, v___x_5694_);
lean_closure_set(v___x_5698_, 4, v_a_5686_);
lean_closure_set(v___x_5698_, 5, v___x_5697_);
v___x_5699_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5687_, v___x_5698_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
return v___x_5699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5700_, lean_object* v_name_5701_, lean_object* v_us_5702_, lean_object* v_ctorVal_5703_, lean_object* v_a_5704_, lean_object* v_args1_5705_, lean_object* v_x_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_){
_start:
{
lean_object* v_res_5712_; 
v_res_5712_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5700_, v_name_5701_, v_us_5702_, v_ctorVal_5703_, v_a_5704_, v_args1_5705_, v_x_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_);
lean_dec(v___y_5710_);
lean_dec_ref(v___y_5709_);
lean_dec(v___y_5708_);
lean_dec_ref(v___y_5707_);
lean_dec_ref(v_x_5706_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_){
_start:
{
lean_object* v_toConstantVal_5719_; lean_object* v_numParams_5720_; lean_object* v_name_5721_; lean_object* v_levelParams_5722_; lean_object* v_type_5723_; lean_object* v___x_5724_; 
v_toConstantVal_5719_ = lean_ctor_get(v_ctorVal_5713_, 0);
v_numParams_5720_ = lean_ctor_get(v_ctorVal_5713_, 3);
lean_inc(v_numParams_5720_);
v_name_5721_ = lean_ctor_get(v_toConstantVal_5719_, 0);
lean_inc(v_name_5721_);
v_levelParams_5722_ = lean_ctor_get(v_toConstantVal_5719_, 1);
v_type_5723_ = lean_ctor_get(v_toConstantVal_5719_, 2);
lean_inc_ref(v_type_5723_);
v___x_5724_ = l_Lean_Meta_elimOptParam(v_type_5723_, v_a_5716_, v_a_5717_);
if (lean_obj_tag(v___x_5724_) == 0)
{
lean_object* v_a_5725_; lean_object* v___x_5726_; lean_object* v_us_5727_; lean_object* v___f_5728_; uint8_t v___x_5729_; lean_object* v___x_5730_; 
v_a_5725_ = lean_ctor_get(v___x_5724_, 0);
lean_inc_n(v_a_5725_, 2);
lean_dec_ref_known(v___x_5724_, 1);
v___x_5726_ = lean_box(0);
lean_inc(v_levelParams_5722_);
v_us_5727_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5722_, v___x_5726_);
v___f_5728_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5728_, 0, v_numParams_5720_);
lean_closure_set(v___f_5728_, 1, v_name_5721_);
lean_closure_set(v___f_5728_, 2, v_us_5727_);
lean_closure_set(v___f_5728_, 3, v_ctorVal_5713_);
lean_closure_set(v___f_5728_, 4, v_a_5725_);
v___x_5729_ = 0;
v___x_5730_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5725_, v___f_5728_, v___x_5729_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_);
return v___x_5730_;
}
else
{
lean_object* v_a_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5738_; 
lean_dec(v_name_5721_);
lean_dec(v_numParams_5720_);
lean_dec_ref(v_ctorVal_5713_);
v_a_5731_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5738_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5738_ == 0)
{
v___x_5733_ = v___x_5724_;
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_a_5731_);
lean_dec(v___x_5724_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v___x_5736_; 
if (v_isShared_5734_ == 0)
{
v___x_5736_ = v___x_5733_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_a_5731_);
v___x_5736_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
return v___x_5736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_){
_start:
{
lean_object* v_res_5745_; 
v_res_5745_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5739_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_);
lean_dec(v_a_5743_);
lean_dec_ref(v_a_5742_);
lean_dec(v_a_5741_);
lean_dec_ref(v_a_5740_);
return v_res_5745_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; 
v___x_5747_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5748_ = l_Lean_stringToMessageData(v___x_5747_);
return v___x_5748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_, lean_object* v_a_5753_){
_start:
{
lean_object* v_toConstantVal_5755_; lean_object* v_name_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; 
v_toConstantVal_5755_ = lean_ctor_get(v_ctorVal_5749_, 0);
lean_inc_ref(v_toConstantVal_5755_);
lean_dec_ref(v_ctorVal_5749_);
v_name_5756_ = lean_ctor_get(v_toConstantVal_5755_, 0);
lean_inc(v_name_5756_);
lean_dec_ref(v_toConstantVal_5755_);
v___x_5757_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5758_ = l_Lean_MessageData_ofName(v_name_5756_);
v___x_5759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5759_, 0, v___x_5757_);
lean_ctor_set(v___x_5759_, 1, v___x_5758_);
v___x_5760_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5761_, 0, v___x_5759_);
lean_ctor_set(v___x_5761_, 1, v___x_5760_);
v___x_5762_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5761_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_);
return v___x_5762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_){
_start:
{
lean_object* v_res_5769_; 
v_res_5769_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_);
lean_dec(v_a_5767_);
lean_dec_ref(v_a_5766_);
lean_dec(v_a_5765_);
lean_dec_ref(v_a_5764_);
return v_res_5769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5770_, lean_object* v_ctorVal_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_){
_start:
{
lean_object* v___x_5777_; 
v___x_5777_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_);
return v___x_5777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5778_, lean_object* v_ctorVal_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_){
_start:
{
lean_object* v_res_5785_; 
v_res_5785_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5778_, v_ctorVal_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_);
lean_dec(v_a_5783_);
lean_dec_ref(v_a_5782_);
lean_dec(v_a_5781_);
lean_dec_ref(v_a_5780_);
return v_res_5785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5791_, size_t v_sz_5792_, size_t v_i_5793_, lean_object* v_bs_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_){
_start:
{
uint8_t v___x_5800_; 
v___x_5800_ = lean_usize_dec_lt(v_i_5793_, v_sz_5792_);
if (v___x_5800_ == 0)
{
lean_object* v___x_5801_; 
lean_dec_ref(v_ctorVal_5791_);
v___x_5801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5801_, 0, v_bs_5794_);
return v___x_5801_;
}
else
{
lean_object* v_v_5802_; lean_object* v___x_5803_; 
v_v_5802_ = lean_array_uget_borrowed(v_bs_5794_, v_i_5793_);
lean_inc(v___y_5798_);
lean_inc_ref(v___y_5797_);
lean_inc(v___y_5796_);
lean_inc_ref(v___y_5795_);
lean_inc(v_v_5802_);
v___x_5803_ = lean_infer_type(v_v_5802_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
if (lean_obj_tag(v___x_5803_) == 0)
{
lean_object* v_a_5804_; lean_object* v___x_5805_; 
v_a_5804_ = lean_ctor_get(v___x_5803_, 0);
lean_inc(v_a_5804_);
lean_dec_ref_known(v___x_5803_, 1);
v___x_5805_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5804_, v___y_5796_);
if (lean_obj_tag(v___x_5805_) == 0)
{
lean_object* v_a_5806_; lean_object* v___x_5807_; lean_object* v_bs_x27_5808_; lean_object* v_a_5810_; lean_object* v___y_5816_; lean_object* v_lhs_5827_; lean_object* v_rhs_5828_; lean_object* v___x_5830_; uint8_t v___x_5831_; 
v_a_5806_ = lean_ctor_get(v___x_5805_, 0);
lean_inc(v_a_5806_);
lean_dec_ref_known(v___x_5805_, 1);
v___x_5807_ = lean_unsigned_to_nat(0u);
v_bs_x27_5808_ = lean_array_uset(v_bs_5794_, v_i_5793_, v___x_5807_);
v___x_5830_ = l_Lean_Expr_cleanupAnnotations(v_a_5806_);
v___x_5831_ = l_Lean_Expr_isApp(v___x_5830_);
if (v___x_5831_ == 0)
{
lean_object* v___x_5832_; 
lean_dec_ref(v___x_5830_);
lean_inc_ref(v_ctorVal_5791_);
v___x_5832_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5791_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
v___y_5816_ = v___x_5832_;
goto v___jp_5815_;
}
else
{
lean_object* v_arg_5833_; lean_object* v___x_5834_; uint8_t v___x_5835_; 
v_arg_5833_ = lean_ctor_get(v___x_5830_, 1);
lean_inc_ref(v_arg_5833_);
v___x_5834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5830_);
v___x_5835_ = l_Lean_Expr_isApp(v___x_5834_);
if (v___x_5835_ == 0)
{
lean_object* v___x_5836_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v_arg_5833_);
lean_inc_ref(v_ctorVal_5791_);
v___x_5836_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5791_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
v___y_5816_ = v___x_5836_;
goto v___jp_5815_;
}
else
{
lean_object* v_arg_5837_; lean_object* v___x_5838_; uint8_t v___x_5839_; 
v_arg_5837_ = lean_ctor_get(v___x_5834_, 1);
lean_inc_ref(v_arg_5837_);
v___x_5838_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5834_);
v___x_5839_ = l_Lean_Expr_isApp(v___x_5838_);
if (v___x_5839_ == 0)
{
lean_object* v___x_5840_; 
lean_dec_ref(v___x_5838_);
lean_dec_ref(v_arg_5837_);
lean_dec_ref(v_arg_5833_);
lean_inc_ref(v_ctorVal_5791_);
v___x_5840_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5791_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
v___y_5816_ = v___x_5840_;
goto v___jp_5815_;
}
else
{
lean_object* v_arg_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; uint8_t v___x_5844_; 
v_arg_5841_ = lean_ctor_get(v___x_5838_, 1);
lean_inc_ref(v_arg_5841_);
v___x_5842_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5838_);
v___x_5843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5844_ = l_Lean_Expr_isConstOf(v___x_5842_, v___x_5843_);
if (v___x_5844_ == 0)
{
uint8_t v___x_5845_; 
lean_dec_ref(v_arg_5837_);
v___x_5845_ = l_Lean_Expr_isApp(v___x_5842_);
if (v___x_5845_ == 0)
{
lean_object* v___x_5846_; 
lean_dec_ref(v___x_5842_);
lean_dec_ref(v_arg_5841_);
lean_dec_ref(v_arg_5833_);
lean_inc_ref(v_ctorVal_5791_);
v___x_5846_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5791_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
v___y_5816_ = v___x_5846_;
goto v___jp_5815_;
}
else
{
lean_object* v___x_5847_; lean_object* v___x_5848_; uint8_t v___x_5849_; 
v___x_5847_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5842_);
v___x_5848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5849_ = l_Lean_Expr_isConstOf(v___x_5847_, v___x_5848_);
lean_dec_ref(v___x_5847_);
if (v___x_5849_ == 0)
{
lean_object* v___x_5850_; 
lean_dec_ref(v_arg_5841_);
lean_dec_ref(v_arg_5833_);
lean_inc_ref(v_ctorVal_5791_);
v___x_5850_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5791_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
v___y_5816_ = v___x_5850_;
goto v___jp_5815_;
}
else
{
v_lhs_5827_ = v_arg_5841_;
v_rhs_5828_ = v_arg_5833_;
goto v___jp_5826_;
}
}
}
else
{
lean_dec_ref(v___x_5842_);
lean_dec_ref(v_arg_5841_);
v_lhs_5827_ = v_arg_5837_;
v_rhs_5828_ = v_arg_5833_;
goto v___jp_5826_;
}
}
}
}
v___jp_5809_:
{
size_t v___x_5811_; size_t v___x_5812_; lean_object* v___x_5813_; 
v___x_5811_ = ((size_t)1ULL);
v___x_5812_ = lean_usize_add(v_i_5793_, v___x_5811_);
v___x_5813_ = lean_array_uset(v_bs_x27_5808_, v_i_5793_, v_a_5810_);
v_i_5793_ = v___x_5812_;
v_bs_5794_ = v___x_5813_;
goto _start;
}
v___jp_5815_:
{
if (lean_obj_tag(v___y_5816_) == 0)
{
lean_object* v_a_5817_; 
v_a_5817_ = lean_ctor_get(v___y_5816_, 0);
lean_inc(v_a_5817_);
lean_dec_ref_known(v___y_5816_, 1);
v_a_5810_ = v_a_5817_;
goto v___jp_5809_;
}
else
{
lean_object* v_a_5818_; lean_object* v___x_5820_; uint8_t v_isShared_5821_; uint8_t v_isSharedCheck_5825_; 
lean_dec_ref(v_bs_x27_5808_);
lean_dec_ref(v_ctorVal_5791_);
v_a_5818_ = lean_ctor_get(v___y_5816_, 0);
v_isSharedCheck_5825_ = !lean_is_exclusive(v___y_5816_);
if (v_isSharedCheck_5825_ == 0)
{
v___x_5820_ = v___y_5816_;
v_isShared_5821_ = v_isSharedCheck_5825_;
goto v_resetjp_5819_;
}
else
{
lean_inc(v_a_5818_);
lean_dec(v___y_5816_);
v___x_5820_ = lean_box(0);
v_isShared_5821_ = v_isSharedCheck_5825_;
goto v_resetjp_5819_;
}
v_resetjp_5819_:
{
lean_object* v___x_5823_; 
if (v_isShared_5821_ == 0)
{
v___x_5823_ = v___x_5820_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_a_5818_);
v___x_5823_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
return v___x_5823_;
}
}
}
}
v___jp_5826_:
{
lean_object* v___x_5829_; 
v___x_5829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5829_, 0, v_lhs_5827_);
lean_ctor_set(v___x_5829_, 1, v_rhs_5828_);
v_a_5810_ = v___x_5829_;
goto v___jp_5809_;
}
}
else
{
lean_object* v_a_5851_; lean_object* v___x_5853_; uint8_t v_isShared_5854_; uint8_t v_isSharedCheck_5858_; 
lean_dec_ref(v_bs_5794_);
lean_dec_ref(v_ctorVal_5791_);
v_a_5851_ = lean_ctor_get(v___x_5805_, 0);
v_isSharedCheck_5858_ = !lean_is_exclusive(v___x_5805_);
if (v_isSharedCheck_5858_ == 0)
{
v___x_5853_ = v___x_5805_;
v_isShared_5854_ = v_isSharedCheck_5858_;
goto v_resetjp_5852_;
}
else
{
lean_inc(v_a_5851_);
lean_dec(v___x_5805_);
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
else
{
lean_object* v_a_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5866_; 
lean_dec_ref(v_bs_5794_);
lean_dec_ref(v_ctorVal_5791_);
v_a_5859_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5866_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5866_ == 0)
{
v___x_5861_ = v___x_5803_;
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_a_5859_);
lean_dec(v___x_5803_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v___x_5864_; 
if (v_isShared_5862_ == 0)
{
v___x_5864_ = v___x_5861_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5865_; 
v_reuseFailAlloc_5865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_a_5859_);
v___x_5864_ = v_reuseFailAlloc_5865_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
return v___x_5864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5867_, lean_object* v_sz_5868_, lean_object* v_i_5869_, lean_object* v_bs_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_){
_start:
{
size_t v_sz_boxed_5876_; size_t v_i_boxed_5877_; lean_object* v_res_5878_; 
v_sz_boxed_5876_ = lean_unbox_usize(v_sz_5868_);
lean_dec(v_sz_5868_);
v_i_boxed_5877_ = lean_unbox_usize(v_i_5869_);
lean_dec(v_i_5869_);
v_res_5878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5867_, v_sz_boxed_5876_, v_i_boxed_5877_, v_bs_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_);
lean_dec(v___y_5874_);
lean_dec_ref(v___y_5873_);
lean_dec(v___y_5872_);
lean_dec_ref(v___y_5871_);
return v_res_5878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5880_; lean_object* v___x_5881_; 
v___x_5880_ = lean_unsigned_to_nat(0u);
v___x_5881_ = l_Lean_Level_ofNat(v___x_5880_);
return v___x_5881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5882_, lean_object* v_us_5883_, lean_object* v_numIndices_5884_, lean_object* v_xs_5885_, lean_object* v_type_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_){
_start:
{
lean_object* v_toConstantVal_5892_; lean_object* v_induct_5893_; lean_object* v_numParams_5894_; lean_object* v___x_5895_; lean_object* v_noConfusionName_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v_noConfusion_5900_; lean_object* v_noConfusion_5901_; lean_object* v_lower_5903_; lean_object* v_upper_5904_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v_n_6015_; uint8_t v___x_6016_; 
v_toConstantVal_5892_ = lean_ctor_get(v_ctorVal_5882_, 0);
v_induct_5893_ = lean_ctor_get(v_ctorVal_5882_, 1);
v_numParams_5894_ = lean_ctor_get(v_ctorVal_5882_, 3);
v___x_5895_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5893_);
v_noConfusionName_5896_ = l_Lean_Name_str___override(v_induct_5893_, v___x_5895_);
v___x_5897_ = lean_unsigned_to_nat(0u);
v___x_5898_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5898_);
lean_ctor_set(v___x_5899_, 1, v_us_5883_);
v_noConfusion_5900_ = l_Lean_mkConst(v_noConfusionName_5896_, v___x_5899_);
v_noConfusion_5901_ = l_Lean_Expr_app___override(v_noConfusion_5900_, v_type_5886_);
v___x_6011_ = lean_array_get_size(v_xs_5885_);
v___x_6012_ = lean_nat_sub(v___x_6011_, v_numParams_5894_);
v___x_6013_ = lean_nat_sub(v___x_6012_, v_numIndices_5884_);
lean_dec(v___x_6012_);
v___x_6014_ = lean_unsigned_to_nat(1u);
v_n_6015_ = lean_nat_sub(v___x_6013_, v___x_6014_);
lean_dec(v___x_6013_);
v___x_6016_ = lean_nat_dec_le(v_n_6015_, v___x_5897_);
if (v___x_6016_ == 0)
{
v_lower_5903_ = v_n_6015_;
v_upper_5904_ = v___x_6011_;
goto v___jp_5902_;
}
else
{
lean_dec(v_n_6015_);
v_lower_5903_ = v___x_5897_;
v_upper_5904_ = v___x_6011_;
goto v___jp_5902_;
}
v___jp_5902_:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v_eqs_5907_; size_t v_sz_5908_; size_t v___x_5909_; lean_object* v___x_5910_; 
lean_inc_ref(v_xs_5885_);
v___x_5905_ = l_Array_toSubarray___redArg(v_xs_5885_, v_lower_5903_, v_upper_5904_);
v___x_5906_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5907_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5905_, v___x_5906_);
v_sz_5908_ = lean_array_size(v_eqs_5907_);
v___x_5909_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5907_);
lean_inc_ref(v_ctorVal_5882_);
v___x_5910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5882_, v_sz_5908_, v___x_5909_, v_eqs_5907_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_);
if (lean_obj_tag(v___x_5910_) == 0)
{
lean_object* v_a_5911_; lean_object* v___x_5912_; lean_object* v_fst_5913_; lean_object* v_snd_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; 
v_a_5911_ = lean_ctor_get(v___x_5910_, 0);
lean_inc(v_a_5911_);
lean_dec_ref_known(v___x_5910_, 1);
v___x_5912_ = l_Array_unzip___redArg(v_a_5911_);
lean_dec(v_a_5911_);
v_fst_5913_ = lean_ctor_get(v___x_5912_, 0);
lean_inc(v_fst_5913_);
v_snd_5914_ = lean_ctor_get(v___x_5912_, 1);
lean_inc(v_snd_5914_);
lean_dec_ref(v___x_5912_);
v___x_5915_ = l_Lean_mkAppN(v_noConfusion_5901_, v_fst_5913_);
lean_dec(v_fst_5913_);
v___x_5916_ = l_Lean_mkAppN(v___x_5915_, v_snd_5914_);
lean_dec(v_snd_5914_);
v___x_5917_ = l_Lean_mkAppN(v___x_5916_, v_eqs_5907_);
lean_dec_ref(v_eqs_5907_);
lean_inc(v___y_5890_);
lean_inc_ref(v___y_5889_);
lean_inc(v___y_5888_);
lean_inc_ref(v___y_5887_);
lean_inc_ref(v___x_5917_);
v___x_5918_ = lean_infer_type(v___x_5917_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_);
if (lean_obj_tag(v___x_5918_) == 0)
{
lean_object* v_a_5919_; lean_object* v___x_5920_; 
v_a_5919_ = lean_ctor_get(v___x_5918_, 0);
lean_inc(v_a_5919_);
lean_dec_ref_known(v___x_5918_, 1);
lean_inc(v___y_5890_);
lean_inc_ref(v___y_5889_);
lean_inc(v___y_5888_);
lean_inc_ref(v___y_5887_);
v___x_5920_ = lean_whnf(v_a_5919_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_);
if (lean_obj_tag(v___x_5920_) == 0)
{
lean_object* v_a_5921_; 
v_a_5921_ = lean_ctor_get(v___x_5920_, 0);
lean_inc(v_a_5921_);
lean_dec_ref_known(v___x_5920_, 1);
if (lean_obj_tag(v_a_5921_) == 7)
{
lean_object* v_binderType_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; 
lean_inc_ref(v_toConstantVal_5892_);
lean_dec_ref(v_ctorVal_5882_);
v_binderType_5922_ = lean_ctor_get(v_a_5921_, 1);
lean_inc_ref(v_binderType_5922_);
lean_dec_ref_known(v_a_5921_, 3);
v___x_5923_ = lean_box(0);
v___x_5924_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5922_, v___x_5923_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_);
if (lean_obj_tag(v___x_5924_) == 0)
{
lean_object* v_a_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; 
v_a_5925_ = lean_ctor_get(v___x_5924_, 0);
lean_inc(v_a_5925_);
lean_dec_ref_known(v___x_5924_, 1);
v___x_5926_ = l_Lean_Expr_mvarId_x21(v_a_5925_);
v___x_5927_ = l_Lean_MVarId_intros(v___x_5926_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_);
if (lean_obj_tag(v___x_5927_) == 0)
{
lean_object* v_a_5928_; lean_object* v_snd_5929_; lean_object* v_name_5930_; lean_object* v___x_5931_; 
v_a_5928_ = lean_ctor_get(v___x_5927_, 0);
lean_inc(v_a_5928_);
lean_dec_ref_known(v___x_5927_, 1);
v_snd_5929_ = lean_ctor_get(v_a_5928_, 1);
lean_inc(v_snd_5929_);
lean_dec(v_a_5928_);
v_name_5930_ = lean_ctor_get(v_toConstantVal_5892_, 0);
lean_inc(v_name_5930_);
lean_dec_ref(v_toConstantVal_5892_);
v___x_5931_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5929_, v_name_5930_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_);
if (lean_obj_tag(v___x_5931_) == 0)
{
lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v_a_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5961_; 
lean_dec_ref_known(v___x_5931_, 1);
v___x_5932_ = l_Lean_Expr_app___override(v___x_5917_, v_a_5925_);
v___x_5933_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5932_, v___y_5888_);
v_a_5934_ = lean_ctor_get(v___x_5933_, 0);
v_isSharedCheck_5961_ = !lean_is_exclusive(v___x_5933_);
if (v_isSharedCheck_5961_ == 0)
{
v___x_5936_ = v___x_5933_;
v_isShared_5937_ = v_isSharedCheck_5961_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_a_5934_);
lean_dec(v___x_5933_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5961_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
uint8_t v___x_5938_; uint8_t v___x_5939_; uint8_t v___x_5940_; lean_object* v___x_5941_; 
v___x_5938_ = 0;
v___x_5939_ = 1;
v___x_5940_ = 1;
v___x_5941_ = l_Lean_Meta_mkLambdaFVars(v_xs_5885_, v_a_5934_, v___x_5938_, v___x_5939_, v___x_5938_, v___x_5939_, v___x_5940_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_);
lean_dec_ref(v_xs_5885_);
if (lean_obj_tag(v___x_5941_) == 0)
{
lean_object* v_a_5942_; lean_object* v___x_5944_; uint8_t v_isShared_5945_; uint8_t v_isSharedCheck_5952_; 
v_a_5942_ = lean_ctor_get(v___x_5941_, 0);
v_isSharedCheck_5952_ = !lean_is_exclusive(v___x_5941_);
if (v_isSharedCheck_5952_ == 0)
{
v___x_5944_ = v___x_5941_;
v_isShared_5945_ = v_isSharedCheck_5952_;
goto v_resetjp_5943_;
}
else
{
lean_inc(v_a_5942_);
lean_dec(v___x_5941_);
v___x_5944_ = lean_box(0);
v_isShared_5945_ = v_isSharedCheck_5952_;
goto v_resetjp_5943_;
}
v_resetjp_5943_:
{
lean_object* v___x_5947_; 
if (v_isShared_5937_ == 0)
{
lean_ctor_set_tag(v___x_5936_, 1);
lean_ctor_set(v___x_5936_, 0, v_a_5942_);
v___x_5947_ = v___x_5936_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5951_; 
v_reuseFailAlloc_5951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5951_, 0, v_a_5942_);
v___x_5947_ = v_reuseFailAlloc_5951_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
lean_object* v___x_5949_; 
if (v_isShared_5945_ == 0)
{
lean_ctor_set(v___x_5944_, 0, v___x_5947_);
v___x_5949_ = v___x_5944_;
goto v_reusejp_5948_;
}
else
{
lean_object* v_reuseFailAlloc_5950_; 
v_reuseFailAlloc_5950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5950_, 0, v___x_5947_);
v___x_5949_ = v_reuseFailAlloc_5950_;
goto v_reusejp_5948_;
}
v_reusejp_5948_:
{
return v___x_5949_;
}
}
}
}
else
{
lean_object* v_a_5953_; lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_5960_; 
lean_del_object(v___x_5936_);
v_a_5953_ = lean_ctor_get(v___x_5941_, 0);
v_isSharedCheck_5960_ = !lean_is_exclusive(v___x_5941_);
if (v_isSharedCheck_5960_ == 0)
{
v___x_5955_ = v___x_5941_;
v_isShared_5956_ = v_isSharedCheck_5960_;
goto v_resetjp_5954_;
}
else
{
lean_inc(v_a_5953_);
lean_dec(v___x_5941_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_5960_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
lean_object* v___x_5958_; 
if (v_isShared_5956_ == 0)
{
v___x_5958_ = v___x_5955_;
goto v_reusejp_5957_;
}
else
{
lean_object* v_reuseFailAlloc_5959_; 
v_reuseFailAlloc_5959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_a_5953_);
v___x_5958_ = v_reuseFailAlloc_5959_;
goto v_reusejp_5957_;
}
v_reusejp_5957_:
{
return v___x_5958_;
}
}
}
}
}
else
{
lean_object* v_a_5962_; lean_object* v___x_5964_; uint8_t v_isShared_5965_; uint8_t v_isSharedCheck_5969_; 
lean_dec(v_a_5925_);
lean_dec_ref(v___x_5917_);
lean_dec_ref(v_xs_5885_);
v_a_5962_ = lean_ctor_get(v___x_5931_, 0);
v_isSharedCheck_5969_ = !lean_is_exclusive(v___x_5931_);
if (v_isSharedCheck_5969_ == 0)
{
v___x_5964_ = v___x_5931_;
v_isShared_5965_ = v_isSharedCheck_5969_;
goto v_resetjp_5963_;
}
else
{
lean_inc(v_a_5962_);
lean_dec(v___x_5931_);
v___x_5964_ = lean_box(0);
v_isShared_5965_ = v_isSharedCheck_5969_;
goto v_resetjp_5963_;
}
v_resetjp_5963_:
{
lean_object* v___x_5967_; 
if (v_isShared_5965_ == 0)
{
v___x_5967_ = v___x_5964_;
goto v_reusejp_5966_;
}
else
{
lean_object* v_reuseFailAlloc_5968_; 
v_reuseFailAlloc_5968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5968_, 0, v_a_5962_);
v___x_5967_ = v_reuseFailAlloc_5968_;
goto v_reusejp_5966_;
}
v_reusejp_5966_:
{
return v___x_5967_;
}
}
}
}
else
{
lean_object* v_a_5970_; lean_object* v___x_5972_; uint8_t v_isShared_5973_; uint8_t v_isSharedCheck_5977_; 
lean_dec(v_a_5925_);
lean_dec_ref(v___x_5917_);
lean_dec_ref(v_toConstantVal_5892_);
lean_dec_ref(v_xs_5885_);
v_a_5970_ = lean_ctor_get(v___x_5927_, 0);
v_isSharedCheck_5977_ = !lean_is_exclusive(v___x_5927_);
if (v_isSharedCheck_5977_ == 0)
{
v___x_5972_ = v___x_5927_;
v_isShared_5973_ = v_isSharedCheck_5977_;
goto v_resetjp_5971_;
}
else
{
lean_inc(v_a_5970_);
lean_dec(v___x_5927_);
v___x_5972_ = lean_box(0);
v_isShared_5973_ = v_isSharedCheck_5977_;
goto v_resetjp_5971_;
}
v_resetjp_5971_:
{
lean_object* v___x_5975_; 
if (v_isShared_5973_ == 0)
{
v___x_5975_ = v___x_5972_;
goto v_reusejp_5974_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v_a_5970_);
v___x_5975_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5974_;
}
v_reusejp_5974_:
{
return v___x_5975_;
}
}
}
}
else
{
lean_object* v_a_5978_; lean_object* v___x_5980_; uint8_t v_isShared_5981_; uint8_t v_isSharedCheck_5985_; 
lean_dec_ref(v___x_5917_);
lean_dec_ref(v_toConstantVal_5892_);
lean_dec_ref(v_xs_5885_);
v_a_5978_ = lean_ctor_get(v___x_5924_, 0);
v_isSharedCheck_5985_ = !lean_is_exclusive(v___x_5924_);
if (v_isSharedCheck_5985_ == 0)
{
v___x_5980_ = v___x_5924_;
v_isShared_5981_ = v_isSharedCheck_5985_;
goto v_resetjp_5979_;
}
else
{
lean_inc(v_a_5978_);
lean_dec(v___x_5924_);
v___x_5980_ = lean_box(0);
v_isShared_5981_ = v_isSharedCheck_5985_;
goto v_resetjp_5979_;
}
v_resetjp_5979_:
{
lean_object* v___x_5983_; 
if (v_isShared_5981_ == 0)
{
v___x_5983_ = v___x_5980_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v_a_5978_);
v___x_5983_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
return v___x_5983_;
}
}
}
}
else
{
lean_object* v___x_5986_; 
lean_dec(v_a_5921_);
lean_dec_ref(v___x_5917_);
lean_dec_ref(v_xs_5885_);
v___x_5986_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5882_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_);
return v___x_5986_;
}
}
else
{
lean_object* v_a_5987_; lean_object* v___x_5989_; uint8_t v_isShared_5990_; uint8_t v_isSharedCheck_5994_; 
lean_dec_ref(v___x_5917_);
lean_dec_ref(v_xs_5885_);
lean_dec_ref(v_ctorVal_5882_);
v_a_5987_ = lean_ctor_get(v___x_5920_, 0);
v_isSharedCheck_5994_ = !lean_is_exclusive(v___x_5920_);
if (v_isSharedCheck_5994_ == 0)
{
v___x_5989_ = v___x_5920_;
v_isShared_5990_ = v_isSharedCheck_5994_;
goto v_resetjp_5988_;
}
else
{
lean_inc(v_a_5987_);
lean_dec(v___x_5920_);
v___x_5989_ = lean_box(0);
v_isShared_5990_ = v_isSharedCheck_5994_;
goto v_resetjp_5988_;
}
v_resetjp_5988_:
{
lean_object* v___x_5992_; 
if (v_isShared_5990_ == 0)
{
v___x_5992_ = v___x_5989_;
goto v_reusejp_5991_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v_a_5987_);
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
else
{
lean_object* v_a_5995_; lean_object* v___x_5997_; uint8_t v_isShared_5998_; uint8_t v_isSharedCheck_6002_; 
lean_dec_ref(v___x_5917_);
lean_dec_ref(v_xs_5885_);
lean_dec_ref(v_ctorVal_5882_);
v_a_5995_ = lean_ctor_get(v___x_5918_, 0);
v_isSharedCheck_6002_ = !lean_is_exclusive(v___x_5918_);
if (v_isSharedCheck_6002_ == 0)
{
v___x_5997_ = v___x_5918_;
v_isShared_5998_ = v_isSharedCheck_6002_;
goto v_resetjp_5996_;
}
else
{
lean_inc(v_a_5995_);
lean_dec(v___x_5918_);
v___x_5997_ = lean_box(0);
v_isShared_5998_ = v_isSharedCheck_6002_;
goto v_resetjp_5996_;
}
v_resetjp_5996_:
{
lean_object* v___x_6000_; 
if (v_isShared_5998_ == 0)
{
v___x_6000_ = v___x_5997_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v_a_5995_);
v___x_6000_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
return v___x_6000_;
}
}
}
}
else
{
lean_object* v_a_6003_; lean_object* v___x_6005_; uint8_t v_isShared_6006_; uint8_t v_isSharedCheck_6010_; 
lean_dec_ref(v_eqs_5907_);
lean_dec_ref(v_noConfusion_5901_);
lean_dec_ref(v_xs_5885_);
lean_dec_ref(v_ctorVal_5882_);
v_a_6003_ = lean_ctor_get(v___x_5910_, 0);
v_isSharedCheck_6010_ = !lean_is_exclusive(v___x_5910_);
if (v_isSharedCheck_6010_ == 0)
{
v___x_6005_ = v___x_5910_;
v_isShared_6006_ = v_isSharedCheck_6010_;
goto v_resetjp_6004_;
}
else
{
lean_inc(v_a_6003_);
lean_dec(v___x_5910_);
v___x_6005_ = lean_box(0);
v_isShared_6006_ = v_isSharedCheck_6010_;
goto v_resetjp_6004_;
}
v_resetjp_6004_:
{
lean_object* v___x_6008_; 
if (v_isShared_6006_ == 0)
{
v___x_6008_ = v___x_6005_;
goto v_reusejp_6007_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v_a_6003_);
v___x_6008_ = v_reuseFailAlloc_6009_;
goto v_reusejp_6007_;
}
v_reusejp_6007_:
{
return v___x_6008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_6017_, lean_object* v_us_6018_, lean_object* v_numIndices_6019_, lean_object* v_xs_6020_, lean_object* v_type_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_){
_start:
{
lean_object* v_res_6027_; 
v_res_6027_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_6017_, v_us_6018_, v_numIndices_6019_, v_xs_6020_, v_type_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_);
lean_dec(v___y_6025_);
lean_dec_ref(v___y_6024_);
lean_dec(v___y_6023_);
lean_dec_ref(v___y_6022_);
lean_dec(v_numIndices_6019_);
return v_res_6027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_6028_, lean_object* v_typeInfo_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_){
_start:
{
lean_object* v_thmType_6035_; lean_object* v_us_6036_; lean_object* v_numIndices_6037_; lean_object* v___f_6038_; uint8_t v___x_6039_; lean_object* v___x_6040_; 
v_thmType_6035_ = lean_ctor_get(v_typeInfo_6029_, 0);
lean_inc_ref(v_thmType_6035_);
v_us_6036_ = lean_ctor_get(v_typeInfo_6029_, 1);
lean_inc(v_us_6036_);
v_numIndices_6037_ = lean_ctor_get(v_typeInfo_6029_, 2);
lean_inc(v_numIndices_6037_);
lean_dec_ref(v_typeInfo_6029_);
v___f_6038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6038_, 0, v_ctorVal_6028_);
lean_closure_set(v___f_6038_, 1, v_us_6036_);
lean_closure_set(v___f_6038_, 2, v_numIndices_6037_);
v___x_6039_ = 0;
v___x_6040_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_6035_, v___f_6038_, v___x_6039_, v___x_6039_, v_a_6030_, v_a_6031_, v_a_6032_, v_a_6033_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_6041_, lean_object* v_typeInfo_6042_, lean_object* v_a_6043_, lean_object* v_a_6044_, lean_object* v_a_6045_, lean_object* v_a_6046_, lean_object* v_a_6047_){
_start:
{
lean_object* v_res_6048_; 
v_res_6048_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_6041_, v_typeInfo_6042_, v_a_6043_, v_a_6044_, v_a_6045_, v_a_6046_);
lean_dec(v_a_6046_);
lean_dec_ref(v_a_6045_);
lean_dec(v_a_6044_);
lean_dec_ref(v_a_6043_);
return v_res_6048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_6051_){
_start:
{
lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6052_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6053_ = l_Lean_Name_str___override(v_ctorName_6051_, v___x_6052_);
return v___x_6053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_6054_, lean_object* v_ctorVal_6055_, lean_object* v_a_6056_, lean_object* v_a_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_){
_start:
{
lean_object* v___x_6061_; 
lean_inc_ref(v_ctorVal_6055_);
v___x_6061_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_6055_, v_a_6056_, v_a_6057_, v_a_6058_, v_a_6059_);
if (lean_obj_tag(v___x_6061_) == 0)
{
lean_object* v_a_6062_; lean_object* v___x_6064_; uint8_t v_isShared_6065_; uint8_t v_isSharedCheck_6123_; 
v_a_6062_ = lean_ctor_get(v___x_6061_, 0);
v_isSharedCheck_6123_ = !lean_is_exclusive(v___x_6061_);
if (v_isSharedCheck_6123_ == 0)
{
v___x_6064_ = v___x_6061_;
v_isShared_6065_ = v_isSharedCheck_6123_;
goto v_resetjp_6063_;
}
else
{
lean_inc(v_a_6062_);
lean_dec(v___x_6061_);
v___x_6064_ = lean_box(0);
v_isShared_6065_ = v_isSharedCheck_6123_;
goto v_resetjp_6063_;
}
v_resetjp_6063_:
{
if (lean_obj_tag(v_a_6062_) == 1)
{
lean_object* v_val_6066_; lean_object* v___x_6067_; 
lean_del_object(v___x_6064_);
v_val_6066_ = lean_ctor_get(v_a_6062_, 0);
lean_inc_n(v_val_6066_, 2);
lean_dec_ref_known(v_a_6062_, 1);
lean_inc_ref(v_ctorVal_6055_);
v___x_6067_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_6055_, v_val_6066_, v_a_6056_, v_a_6057_, v_a_6058_, v_a_6059_);
if (lean_obj_tag(v___x_6067_) == 0)
{
lean_object* v_a_6068_; lean_object* v___x_6070_; uint8_t v_isShared_6071_; uint8_t v_isSharedCheck_6110_; 
v_a_6068_ = lean_ctor_get(v___x_6067_, 0);
v_isSharedCheck_6110_ = !lean_is_exclusive(v___x_6067_);
if (v_isSharedCheck_6110_ == 0)
{
v___x_6070_ = v___x_6067_;
v_isShared_6071_ = v_isSharedCheck_6110_;
goto v_resetjp_6069_;
}
else
{
lean_inc(v_a_6068_);
lean_dec(v___x_6067_);
v___x_6070_ = lean_box(0);
v_isShared_6071_ = v_isSharedCheck_6110_;
goto v_resetjp_6069_;
}
v_resetjp_6069_:
{
if (lean_obj_tag(v_a_6068_) == 1)
{
lean_object* v_toConstantVal_6072_; lean_object* v_val_6073_; lean_object* v___x_6075_; uint8_t v_isShared_6076_; uint8_t v_isSharedCheck_6105_; 
v_toConstantVal_6072_ = lean_ctor_get(v_ctorVal_6055_, 0);
lean_inc_ref(v_toConstantVal_6072_);
lean_dec_ref(v_ctorVal_6055_);
v_val_6073_ = lean_ctor_get(v_a_6068_, 0);
v_isSharedCheck_6105_ = !lean_is_exclusive(v_a_6068_);
if (v_isSharedCheck_6105_ == 0)
{
v___x_6075_ = v_a_6068_;
v_isShared_6076_ = v_isSharedCheck_6105_;
goto v_resetjp_6074_;
}
else
{
lean_inc(v_val_6073_);
lean_dec(v_a_6068_);
v___x_6075_ = lean_box(0);
v_isShared_6076_ = v_isSharedCheck_6105_;
goto v_resetjp_6074_;
}
v_resetjp_6074_:
{
lean_object* v_levelParams_6077_; lean_object* v___x_6079_; uint8_t v_isShared_6080_; uint8_t v_isSharedCheck_6102_; 
v_levelParams_6077_ = lean_ctor_get(v_toConstantVal_6072_, 1);
v_isSharedCheck_6102_ = !lean_is_exclusive(v_toConstantVal_6072_);
if (v_isSharedCheck_6102_ == 0)
{
lean_object* v_unused_6103_; lean_object* v_unused_6104_; 
v_unused_6103_ = lean_ctor_get(v_toConstantVal_6072_, 2);
lean_dec(v_unused_6103_);
v_unused_6104_ = lean_ctor_get(v_toConstantVal_6072_, 0);
lean_dec(v_unused_6104_);
v___x_6079_ = v_toConstantVal_6072_;
v_isShared_6080_ = v_isSharedCheck_6102_;
goto v_resetjp_6078_;
}
else
{
lean_inc(v_levelParams_6077_);
lean_dec(v_toConstantVal_6072_);
v___x_6079_ = lean_box(0);
v_isShared_6080_ = v_isSharedCheck_6102_;
goto v_resetjp_6078_;
}
v_resetjp_6078_:
{
lean_object* v_thmType_6081_; lean_object* v___x_6083_; uint8_t v_isShared_6084_; uint8_t v_isSharedCheck_6099_; 
v_thmType_6081_ = lean_ctor_get(v_val_6066_, 0);
v_isSharedCheck_6099_ = !lean_is_exclusive(v_val_6066_);
if (v_isSharedCheck_6099_ == 0)
{
lean_object* v_unused_6100_; lean_object* v_unused_6101_; 
v_unused_6100_ = lean_ctor_get(v_val_6066_, 2);
lean_dec(v_unused_6100_);
v_unused_6101_ = lean_ctor_get(v_val_6066_, 1);
lean_dec(v_unused_6101_);
v___x_6083_ = v_val_6066_;
v_isShared_6084_ = v_isSharedCheck_6099_;
goto v_resetjp_6082_;
}
else
{
lean_inc(v_thmType_6081_);
lean_dec(v_val_6066_);
v___x_6083_ = lean_box(0);
v_isShared_6084_ = v_isSharedCheck_6099_;
goto v_resetjp_6082_;
}
v_resetjp_6082_:
{
lean_object* v___x_6086_; 
lean_inc(v_thmName_6054_);
if (v_isShared_6080_ == 0)
{
lean_ctor_set(v___x_6079_, 2, v_thmType_6081_);
lean_ctor_set(v___x_6079_, 0, v_thmName_6054_);
v___x_6086_ = v___x_6079_;
goto v_reusejp_6085_;
}
else
{
lean_object* v_reuseFailAlloc_6098_; 
v_reuseFailAlloc_6098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_thmName_6054_);
lean_ctor_set(v_reuseFailAlloc_6098_, 1, v_levelParams_6077_);
lean_ctor_set(v_reuseFailAlloc_6098_, 2, v_thmType_6081_);
v___x_6086_ = v_reuseFailAlloc_6098_;
goto v_reusejp_6085_;
}
v_reusejp_6085_:
{
lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6090_; 
v___x_6087_ = lean_box(0);
v___x_6088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6088_, 0, v_thmName_6054_);
lean_ctor_set(v___x_6088_, 1, v___x_6087_);
if (v_isShared_6084_ == 0)
{
lean_ctor_set(v___x_6083_, 2, v___x_6088_);
lean_ctor_set(v___x_6083_, 1, v_val_6073_);
lean_ctor_set(v___x_6083_, 0, v___x_6086_);
v___x_6090_ = v___x_6083_;
goto v_reusejp_6089_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v___x_6086_);
lean_ctor_set(v_reuseFailAlloc_6097_, 1, v_val_6073_);
lean_ctor_set(v_reuseFailAlloc_6097_, 2, v___x_6088_);
v___x_6090_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6089_;
}
v_reusejp_6089_:
{
lean_object* v___x_6092_; 
if (v_isShared_6076_ == 0)
{
lean_ctor_set(v___x_6075_, 0, v___x_6090_);
v___x_6092_ = v___x_6075_;
goto v_reusejp_6091_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v___x_6090_);
v___x_6092_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6091_;
}
v_reusejp_6091_:
{
lean_object* v___x_6094_; 
if (v_isShared_6071_ == 0)
{
lean_ctor_set(v___x_6070_, 0, v___x_6092_);
v___x_6094_ = v___x_6070_;
goto v_reusejp_6093_;
}
else
{
lean_object* v_reuseFailAlloc_6095_; 
v_reuseFailAlloc_6095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6095_, 0, v___x_6092_);
v___x_6094_ = v_reuseFailAlloc_6095_;
goto v_reusejp_6093_;
}
v_reusejp_6093_:
{
return v___x_6094_;
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
lean_object* v___x_6106_; lean_object* v___x_6108_; 
lean_dec(v_a_6068_);
lean_dec(v_val_6066_);
lean_dec_ref(v_ctorVal_6055_);
lean_dec(v_thmName_6054_);
v___x_6106_ = lean_box(0);
if (v_isShared_6071_ == 0)
{
lean_ctor_set(v___x_6070_, 0, v___x_6106_);
v___x_6108_ = v___x_6070_;
goto v_reusejp_6107_;
}
else
{
lean_object* v_reuseFailAlloc_6109_; 
v_reuseFailAlloc_6109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6109_, 0, v___x_6106_);
v___x_6108_ = v_reuseFailAlloc_6109_;
goto v_reusejp_6107_;
}
v_reusejp_6107_:
{
return v___x_6108_;
}
}
}
}
else
{
lean_object* v_a_6111_; lean_object* v___x_6113_; uint8_t v_isShared_6114_; uint8_t v_isSharedCheck_6118_; 
lean_dec(v_val_6066_);
lean_dec_ref(v_ctorVal_6055_);
lean_dec(v_thmName_6054_);
v_a_6111_ = lean_ctor_get(v___x_6067_, 0);
v_isSharedCheck_6118_ = !lean_is_exclusive(v___x_6067_);
if (v_isSharedCheck_6118_ == 0)
{
v___x_6113_ = v___x_6067_;
v_isShared_6114_ = v_isSharedCheck_6118_;
goto v_resetjp_6112_;
}
else
{
lean_inc(v_a_6111_);
lean_dec(v___x_6067_);
v___x_6113_ = lean_box(0);
v_isShared_6114_ = v_isSharedCheck_6118_;
goto v_resetjp_6112_;
}
v_resetjp_6112_:
{
lean_object* v___x_6116_; 
if (v_isShared_6114_ == 0)
{
v___x_6116_ = v___x_6113_;
goto v_reusejp_6115_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_a_6111_);
v___x_6116_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6115_;
}
v_reusejp_6115_:
{
return v___x_6116_;
}
}
}
}
else
{
lean_object* v___x_6119_; lean_object* v___x_6121_; 
lean_dec(v_a_6062_);
lean_dec_ref(v_ctorVal_6055_);
lean_dec(v_thmName_6054_);
v___x_6119_ = lean_box(0);
if (v_isShared_6065_ == 0)
{
lean_ctor_set(v___x_6064_, 0, v___x_6119_);
v___x_6121_ = v___x_6064_;
goto v_reusejp_6120_;
}
else
{
lean_object* v_reuseFailAlloc_6122_; 
v_reuseFailAlloc_6122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6122_, 0, v___x_6119_);
v___x_6121_ = v_reuseFailAlloc_6122_;
goto v_reusejp_6120_;
}
v_reusejp_6120_:
{
return v___x_6121_;
}
}
}
}
else
{
lean_object* v_a_6124_; lean_object* v___x_6126_; uint8_t v_isShared_6127_; uint8_t v_isSharedCheck_6131_; 
lean_dec_ref(v_ctorVal_6055_);
lean_dec(v_thmName_6054_);
v_a_6124_ = lean_ctor_get(v___x_6061_, 0);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6061_);
if (v_isSharedCheck_6131_ == 0)
{
v___x_6126_ = v___x_6061_;
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
else
{
lean_inc(v_a_6124_);
lean_dec(v___x_6061_);
v___x_6126_ = lean_box(0);
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
v_resetjp_6125_:
{
lean_object* v___x_6129_; 
if (v_isShared_6127_ == 0)
{
v___x_6129_ = v___x_6126_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_a_6124_);
v___x_6129_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
return v___x_6129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6132_, lean_object* v_ctorVal_6133_, lean_object* v_a_6134_, lean_object* v_a_6135_, lean_object* v_a_6136_, lean_object* v_a_6137_, lean_object* v_a_6138_){
_start:
{
lean_object* v_res_6139_; 
v_res_6139_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6132_, v_ctorVal_6133_, v_a_6134_, v_a_6135_, v_a_6136_, v_a_6137_);
lean_dec(v_a_6137_);
lean_dec_ref(v_a_6136_);
lean_dec(v_a_6135_);
lean_dec_ref(v_a_6134_);
return v_res_6139_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6140_, lean_object* v_n_6141_){
_start:
{
if (lean_obj_tag(v_n_6141_) == 1)
{
lean_object* v_pre_6142_; lean_object* v_str_6143_; lean_object* v___x_6144_; uint8_t v___x_6145_; 
v_pre_6142_ = lean_ctor_get(v_n_6141_, 0);
lean_inc(v_pre_6142_);
v_str_6143_ = lean_ctor_get(v_n_6141_, 1);
lean_inc_ref(v_str_6143_);
lean_dec_ref_known(v_n_6141_, 2);
v___x_6144_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6145_ = lean_string_dec_eq(v_str_6143_, v___x_6144_);
lean_dec_ref(v_str_6143_);
if (v___x_6145_ == 0)
{
lean_dec(v_pre_6142_);
lean_dec_ref(v_env_6140_);
return v___x_6145_;
}
else
{
uint8_t v___x_6146_; lean_object* v___x_6147_; 
v___x_6146_ = 0;
v___x_6147_ = l_Lean_Environment_find_x3f(v_env_6140_, v_pre_6142_, v___x_6146_);
if (lean_obj_tag(v___x_6147_) == 1)
{
lean_object* v_val_6148_; 
v_val_6148_ = lean_ctor_get(v___x_6147_, 0);
lean_inc(v_val_6148_);
lean_dec_ref_known(v___x_6147_, 1);
if (lean_obj_tag(v_val_6148_) == 6)
{
lean_dec_ref_known(v_val_6148_, 1);
return v___x_6145_;
}
else
{
lean_dec(v_val_6148_);
return v___x_6146_;
}
}
else
{
lean_dec(v___x_6147_);
return v___x_6146_;
}
}
}
else
{
uint8_t v___x_6149_; 
lean_dec(v_n_6141_);
lean_dec_ref(v_env_6140_);
v___x_6149_ = 0;
return v___x_6149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6150_, lean_object* v_n_6151_){
_start:
{
uint8_t v_res_6152_; lean_object* v_r_6153_; 
v_res_6152_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6150_, v_n_6151_);
v_r_6153_ = lean_box(v_res_6152_);
return v_r_6153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6156_; lean_object* v___x_6157_; 
v___f_6156_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6157_ = l_Lean_registerReservedNamePredicate(v___f_6156_);
return v___x_6157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6158_){
_start:
{
lean_object* v_res_6159_; 
v_res_6159_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6159_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6160_, lean_object* v___y_6161_){
_start:
{
lean_object* v___x_6163_; lean_object* v_env_6164_; lean_object* v_toConstantVal_6165_; lean_object* v_value_6166_; lean_object* v_all_6167_; uint8_t v___y_6169_; lean_object* v_type_6177_; uint8_t v___x_6178_; 
v___x_6163_ = lean_st_ref_get(v___y_6161_);
v_env_6164_ = lean_ctor_get(v___x_6163_, 0);
lean_inc_ref_n(v_env_6164_, 2);
lean_dec(v___x_6163_);
v_toConstantVal_6165_ = lean_ctor_get(v_thm_6160_, 0);
v_value_6166_ = lean_ctor_get(v_thm_6160_, 1);
v_all_6167_ = lean_ctor_get(v_thm_6160_, 2);
v_type_6177_ = lean_ctor_get(v_toConstantVal_6165_, 2);
v___x_6178_ = l_Lean_Environment_hasUnsafe(v_env_6164_, v_type_6177_);
if (v___x_6178_ == 0)
{
uint8_t v___x_6179_; 
v___x_6179_ = l_Lean_Environment_hasUnsafe(v_env_6164_, v_value_6166_);
v___y_6169_ = v___x_6179_;
goto v___jp_6168_;
}
else
{
lean_dec_ref(v_env_6164_);
v___y_6169_ = v___x_6178_;
goto v___jp_6168_;
}
v___jp_6168_:
{
if (v___y_6169_ == 0)
{
lean_object* v___x_6170_; lean_object* v___x_6171_; 
v___x_6170_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6170_, 0, v_thm_6160_);
v___x_6171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6170_);
return v___x_6171_;
}
else
{
lean_object* v___x_6172_; uint8_t v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; 
lean_inc(v_all_6167_);
lean_inc_ref(v_value_6166_);
lean_inc_ref(v_toConstantVal_6165_);
lean_dec_ref(v_thm_6160_);
v___x_6172_ = lean_box(0);
v___x_6173_ = 0;
v___x_6174_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6174_, 0, v_toConstantVal_6165_);
lean_ctor_set(v___x_6174_, 1, v_value_6166_);
lean_ctor_set(v___x_6174_, 2, v___x_6172_);
lean_ctor_set(v___x_6174_, 3, v_all_6167_);
lean_ctor_set_uint8(v___x_6174_, sizeof(void*)*4, v___x_6173_);
v___x_6175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6174_);
v___x_6176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6175_);
return v___x_6176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_){
_start:
{
lean_object* v_res_6183_; 
v_res_6183_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6180_, v___y_6181_);
lean_dec(v___y_6181_);
return v_res_6183_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_){
_start:
{
lean_object* v___x_6190_; 
v___x_6190_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6184_, v___y_6188_);
return v___x_6190_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_){
_start:
{
lean_object* v_res_6197_; 
v_res_6197_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_);
lean_dec(v___y_6195_);
lean_dec_ref(v___y_6194_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
return v_res_6197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6198_, uint8_t v___x_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_){
_start:
{
lean_object* v___x_6205_; lean_object* v_a_6206_; lean_object* v___x_6207_; 
v___x_6205_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6198_, v___y_6203_);
v_a_6206_ = lean_ctor_get(v___x_6205_, 0);
lean_inc(v_a_6206_);
lean_dec_ref(v___x_6205_);
v___x_6207_ = l_Lean_addDecl(v_a_6206_, v___x_6199_, v___y_6202_, v___y_6203_);
return v___x_6207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6208_, lean_object* v___x_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_){
_start:
{
uint8_t v___x_2122__boxed_6215_; lean_object* v_res_6216_; 
v___x_2122__boxed_6215_ = lean_unbox(v___x_6209_);
v_res_6216_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6208_, v___x_2122__boxed_6215_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
lean_dec(v___y_6213_);
lean_dec_ref(v___y_6212_);
lean_dec(v___y_6211_);
lean_dec_ref(v___y_6210_);
return v_res_6216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; 
v___x_6219_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6220_ = lean_unsigned_to_nat(0u);
v___x_6221_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6220_);
lean_ctor_set(v___x_6221_, 1, v___x_6220_);
lean_ctor_set(v___x_6221_, 2, v___x_6220_);
lean_ctor_set(v___x_6221_, 3, v___x_6220_);
lean_ctor_set(v___x_6221_, 4, v___x_6219_);
lean_ctor_set(v___x_6221_, 5, v___x_6219_);
lean_ctor_set(v___x_6221_, 6, v___x_6219_);
lean_ctor_set(v___x_6221_, 7, v___x_6219_);
lean_ctor_set(v___x_6221_, 8, v___x_6219_);
lean_ctor_set(v___x_6221_, 9, v___x_6219_);
return v___x_6221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6222_; lean_object* v___x_6223_; 
v___x_6222_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6223_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6223_, 0, v___x_6222_);
lean_ctor_set(v___x_6223_, 1, v___x_6222_);
lean_ctor_set(v___x_6223_, 2, v___x_6222_);
lean_ctor_set(v___x_6223_, 3, v___x_6222_);
lean_ctor_set(v___x_6223_, 4, v___x_6222_);
lean_ctor_set(v___x_6223_, 5, v___x_6222_);
return v___x_6223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6224_; lean_object* v___x_6225_; 
v___x_6224_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6225_, 0, v___x_6224_);
lean_ctor_set(v___x_6225_, 1, v___x_6224_);
lean_ctor_set(v___x_6225_, 2, v___x_6224_);
lean_ctor_set(v___x_6225_, 3, v___x_6224_);
lean_ctor_set(v___x_6225_, 4, v___x_6224_);
return v___x_6225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6226_, lean_object* v_name_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_){
_start:
{
if (lean_obj_tag(v_name_6227_) == 1)
{
lean_object* v_pre_6239_; lean_object* v_str_6240_; lean_object* v___x_6241_; uint8_t v___x_6242_; 
v_pre_6239_ = lean_ctor_get(v_name_6227_, 0);
lean_inc(v_pre_6239_);
v_str_6240_ = lean_ctor_get(v_name_6227_, 1);
v___x_6241_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6242_ = lean_string_dec_eq(v_str_6240_, v___x_6241_);
if (v___x_6242_ == 0)
{
lean_dec(v_pre_6239_);
lean_dec_ref_known(v_name_6227_, 2);
lean_dec(v___x_6226_);
goto v___jp_6235_;
}
else
{
lean_object* v___x_6243_; lean_object* v_env_6244_; uint8_t v___x_6245_; lean_object* v___x_6246_; 
v___x_6243_ = lean_st_ref_get(v___y_6229_);
v_env_6244_ = lean_ctor_get(v___x_6243_, 0);
lean_inc_ref(v_env_6244_);
lean_dec(v___x_6243_);
v___x_6245_ = 0;
lean_inc(v_pre_6239_);
v___x_6246_ = l_Lean_Environment_find_x3f(v_env_6244_, v_pre_6239_, v___x_6245_);
if (lean_obj_tag(v___x_6246_) == 1)
{
lean_object* v_val_6247_; 
v_val_6247_ = lean_ctor_get(v___x_6246_, 0);
lean_inc(v_val_6247_);
lean_dec_ref_known(v___x_6246_, 1);
if (lean_obj_tag(v_val_6247_) == 6)
{
lean_object* v_val_6248_; lean_object* v___x_6250_; uint8_t v_isShared_6251_; uint8_t v_isSharedCheck_6298_; 
v_val_6248_ = lean_ctor_get(v_val_6247_, 0);
v_isSharedCheck_6298_ = !lean_is_exclusive(v_val_6247_);
if (v_isSharedCheck_6298_ == 0)
{
v___x_6250_ = v_val_6247_;
v_isShared_6251_ = v_isSharedCheck_6298_;
goto v_resetjp_6249_;
}
else
{
lean_inc(v_val_6248_);
lean_dec(v_val_6247_);
v___x_6250_ = lean_box(0);
v_isShared_6251_ = v_isSharedCheck_6298_;
goto v_resetjp_6249_;
}
v_resetjp_6249_:
{
uint8_t v___x_6252_; uint8_t v___x_6253_; uint8_t v___x_6254_; lean_object* v___x_6255_; uint64_t v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; uint8_t v_a_6270_; lean_object* v___x_6276_; 
v___x_6252_ = 1;
v___x_6253_ = 0;
v___x_6254_ = 2;
v___x_6255_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6255_, 0, v___x_6245_);
lean_ctor_set_uint8(v___x_6255_, 1, v___x_6245_);
lean_ctor_set_uint8(v___x_6255_, 2, v___x_6245_);
lean_ctor_set_uint8(v___x_6255_, 3, v___x_6245_);
lean_ctor_set_uint8(v___x_6255_, 4, v___x_6245_);
lean_ctor_set_uint8(v___x_6255_, 5, v___x_6242_);
lean_ctor_set_uint8(v___x_6255_, 6, v___x_6242_);
lean_ctor_set_uint8(v___x_6255_, 7, v___x_6245_);
lean_ctor_set_uint8(v___x_6255_, 8, v___x_6242_);
lean_ctor_set_uint8(v___x_6255_, 9, v___x_6252_);
lean_ctor_set_uint8(v___x_6255_, 10, v___x_6253_);
lean_ctor_set_uint8(v___x_6255_, 11, v___x_6242_);
lean_ctor_set_uint8(v___x_6255_, 12, v___x_6242_);
lean_ctor_set_uint8(v___x_6255_, 13, v___x_6242_);
lean_ctor_set_uint8(v___x_6255_, 14, v___x_6254_);
lean_ctor_set_uint8(v___x_6255_, 15, v___x_6242_);
lean_ctor_set_uint8(v___x_6255_, 16, v___x_6242_);
lean_ctor_set_uint8(v___x_6255_, 17, v___x_6242_);
lean_ctor_set_uint8(v___x_6255_, 18, v___x_6242_);
v___x_6256_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6255_);
v___x_6257_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6257_, 0, v___x_6255_);
lean_ctor_set_uint64(v___x_6257_, sizeof(void*)*1, v___x_6256_);
v___x_6258_ = lean_unsigned_to_nat(0u);
v___x_6259_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6260_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6261_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6262_ = lean_box(0);
lean_inc(v___x_6226_);
v___x_6263_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6263_, 0, v___x_6257_);
lean_ctor_set(v___x_6263_, 1, v___x_6226_);
lean_ctor_set(v___x_6263_, 2, v___x_6260_);
lean_ctor_set(v___x_6263_, 3, v___x_6261_);
lean_ctor_set(v___x_6263_, 4, v___x_6262_);
lean_ctor_set(v___x_6263_, 5, v___x_6258_);
lean_ctor_set(v___x_6263_, 6, v___x_6262_);
lean_ctor_set_uint8(v___x_6263_, sizeof(void*)*7, v___x_6245_);
lean_ctor_set_uint8(v___x_6263_, sizeof(void*)*7 + 1, v___x_6245_);
lean_ctor_set_uint8(v___x_6263_, sizeof(void*)*7 + 2, v___x_6245_);
lean_ctor_set_uint8(v___x_6263_, sizeof(void*)*7 + 3, v___x_6242_);
v___x_6264_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6265_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6266_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6267_, 0, v___x_6264_);
lean_ctor_set(v___x_6267_, 1, v___x_6265_);
lean_ctor_set(v___x_6267_, 2, v___x_6226_);
lean_ctor_set(v___x_6267_, 3, v___x_6259_);
lean_ctor_set(v___x_6267_, 4, v___x_6266_);
v___x_6268_ = lean_st_mk_ref(v___x_6267_);
lean_inc_ref(v_name_6227_);
v___x_6276_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6227_, v_val_6248_, v___x_6263_, v___x_6268_, v___y_6228_, v___y_6229_);
if (lean_obj_tag(v___x_6276_) == 0)
{
lean_object* v_a_6277_; 
v_a_6277_ = lean_ctor_get(v___x_6276_, 0);
lean_inc(v_a_6277_);
lean_dec_ref_known(v___x_6276_, 1);
if (lean_obj_tag(v_a_6277_) == 1)
{
lean_object* v_val_6278_; lean_object* v___x_6279_; lean_object* v___f_6280_; lean_object* v___x_6281_; 
v_val_6278_ = lean_ctor_get(v_a_6277_, 0);
lean_inc(v_val_6278_);
lean_dec_ref_known(v_a_6277_, 1);
v___x_6279_ = lean_box(v___x_6245_);
v___f_6280_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6280_, 0, v_val_6278_);
lean_closure_set(v___f_6280_, 1, v___x_6279_);
v___x_6281_ = l_Lean_Meta_realizeConst(v_pre_6239_, v_name_6227_, v___f_6280_, v___x_6263_, v___x_6268_, v___y_6228_, v___y_6229_);
lean_dec_ref_known(v___x_6263_, 7);
if (lean_obj_tag(v___x_6281_) == 0)
{
lean_dec_ref_known(v___x_6281_, 1);
v_a_6270_ = v___x_6242_;
goto v___jp_6269_;
}
else
{
lean_object* v_a_6282_; lean_object* v___x_6284_; uint8_t v_isShared_6285_; uint8_t v_isSharedCheck_6289_; 
lean_dec(v___x_6268_);
lean_del_object(v___x_6250_);
v_a_6282_ = lean_ctor_get(v___x_6281_, 0);
v_isSharedCheck_6289_ = !lean_is_exclusive(v___x_6281_);
if (v_isSharedCheck_6289_ == 0)
{
v___x_6284_ = v___x_6281_;
v_isShared_6285_ = v_isSharedCheck_6289_;
goto v_resetjp_6283_;
}
else
{
lean_inc(v_a_6282_);
lean_dec(v___x_6281_);
v___x_6284_ = lean_box(0);
v_isShared_6285_ = v_isSharedCheck_6289_;
goto v_resetjp_6283_;
}
v_resetjp_6283_:
{
lean_object* v___x_6287_; 
if (v_isShared_6285_ == 0)
{
v___x_6287_ = v___x_6284_;
goto v_reusejp_6286_;
}
else
{
lean_object* v_reuseFailAlloc_6288_; 
v_reuseFailAlloc_6288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6288_, 0, v_a_6282_);
v___x_6287_ = v_reuseFailAlloc_6288_;
goto v_reusejp_6286_;
}
v_reusejp_6286_:
{
return v___x_6287_;
}
}
}
}
else
{
lean_dec(v_a_6277_);
lean_dec_ref_known(v___x_6263_, 7);
lean_dec_ref_known(v_name_6227_, 2);
lean_dec(v_pre_6239_);
v_a_6270_ = v___x_6245_;
goto v___jp_6269_;
}
}
else
{
lean_object* v_a_6290_; lean_object* v___x_6292_; uint8_t v_isShared_6293_; uint8_t v_isSharedCheck_6297_; 
lean_dec(v___x_6268_);
lean_dec_ref_known(v___x_6263_, 7);
lean_del_object(v___x_6250_);
lean_dec_ref_known(v_name_6227_, 2);
lean_dec(v_pre_6239_);
v_a_6290_ = lean_ctor_get(v___x_6276_, 0);
v_isSharedCheck_6297_ = !lean_is_exclusive(v___x_6276_);
if (v_isSharedCheck_6297_ == 0)
{
v___x_6292_ = v___x_6276_;
v_isShared_6293_ = v_isSharedCheck_6297_;
goto v_resetjp_6291_;
}
else
{
lean_inc(v_a_6290_);
lean_dec(v___x_6276_);
v___x_6292_ = lean_box(0);
v_isShared_6293_ = v_isSharedCheck_6297_;
goto v_resetjp_6291_;
}
v_resetjp_6291_:
{
lean_object* v___x_6295_; 
if (v_isShared_6293_ == 0)
{
v___x_6295_ = v___x_6292_;
goto v_reusejp_6294_;
}
else
{
lean_object* v_reuseFailAlloc_6296_; 
v_reuseFailAlloc_6296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6296_, 0, v_a_6290_);
v___x_6295_ = v_reuseFailAlloc_6296_;
goto v_reusejp_6294_;
}
v_reusejp_6294_:
{
return v___x_6295_;
}
}
}
v___jp_6269_:
{
lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6274_; 
v___x_6271_ = lean_st_ref_get(v___x_6268_);
lean_dec(v___x_6268_);
lean_dec(v___x_6271_);
v___x_6272_ = lean_box(v_a_6270_);
if (v_isShared_6251_ == 0)
{
lean_ctor_set_tag(v___x_6250_, 0);
lean_ctor_set(v___x_6250_, 0, v___x_6272_);
v___x_6274_ = v___x_6250_;
goto v_reusejp_6273_;
}
else
{
lean_object* v_reuseFailAlloc_6275_; 
v_reuseFailAlloc_6275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6275_, 0, v___x_6272_);
v___x_6274_ = v_reuseFailAlloc_6275_;
goto v_reusejp_6273_;
}
v_reusejp_6273_:
{
return v___x_6274_;
}
}
}
}
else
{
lean_dec(v_val_6247_);
lean_dec(v_pre_6239_);
lean_dec_ref_known(v_name_6227_, 2);
lean_dec(v___x_6226_);
goto v___jp_6231_;
}
}
else
{
lean_dec(v___x_6246_);
lean_dec(v_pre_6239_);
lean_dec_ref_known(v_name_6227_, 2);
lean_dec(v___x_6226_);
goto v___jp_6231_;
}
}
}
else
{
lean_dec(v_name_6227_);
lean_dec(v___x_6226_);
goto v___jp_6235_;
}
v___jp_6231_:
{
uint8_t v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; 
v___x_6232_ = 0;
v___x_6233_ = lean_box(v___x_6232_);
v___x_6234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6234_, 0, v___x_6233_);
return v___x_6234_;
}
v___jp_6235_:
{
uint8_t v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; 
v___x_6236_ = 0;
v___x_6237_ = lean_box(v___x_6236_);
v___x_6238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6238_, 0, v___x_6237_);
return v___x_6238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6299_, lean_object* v_name_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_){
_start:
{
lean_object* v_res_6304_; 
v_res_6304_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6299_, v_name_6300_, v___y_6301_, v___y_6302_);
lean_dec(v___y_6302_);
lean_dec_ref(v___y_6301_);
return v_res_6304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6308_; lean_object* v___x_6309_; 
v___f_6308_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6309_ = l_Lean_registerReservedNameAction(v___f_6308_);
return v___x_6309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6310_){
_start:
{
lean_object* v_res_6311_; 
v_res_6311_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6311_;
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
