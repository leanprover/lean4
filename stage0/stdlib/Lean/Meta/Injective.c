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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "solving injectivity goal for "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " with hypothesis "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at\n"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12;
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
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "genInjectivity"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(56, 68, 112, 222, 169, 79, 62, 37)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "generate injectivity theorems for inductive datatype constructors. Temporarily (for bootstrapping reasons) also controls the generation of the\n    `ctorIdx` definition."};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 17, 232, 138, 187, 170, 36, 13)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_82_, lean_object* v_b_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_dec(v_b_83_);
lean_dec_ref(v_a_82_);
return v_x_84_;
}
else
{
lean_object* v_key_85_; lean_object* v_value_86_; lean_object* v_tail_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_99_; 
v_key_85_ = lean_ctor_get(v_x_84_, 0);
v_value_86_ = lean_ctor_get(v_x_84_, 1);
v_tail_87_ = lean_ctor_get(v_x_84_, 2);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_99_ == 0)
{
v___x_89_ = v_x_84_;
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_tail_87_);
lean_inc(v_value_86_);
lean_inc(v_key_85_);
lean_dec(v_x_84_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint8_t v___x_91_; 
v___x_91_ = l_Lean_ExprStructEq_beq(v_key_85_, v_a_82_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_a_82_, v_b_83_, v_tail_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 2, v___x_92_);
v___x_94_ = v___x_89_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_key_85_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_value_86_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec(v_value_86_);
lean_dec(v_key_85_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_b_83_);
lean_ctor_set(v___x_89_, 0, v_a_82_);
v___x_97_ = v___x_89_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_82_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_b_83_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v_tail_87_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_100_, lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
uint8_t v___x_102_; 
v___x_102_ = 0;
return v___x_102_;
}
else
{
lean_object* v_key_103_; lean_object* v_tail_104_; uint8_t v___x_105_; 
v_key_103_ = lean_ctor_get(v_x_101_, 0);
v_tail_104_ = lean_ctor_get(v_x_101_, 2);
v___x_105_ = l_Lean_ExprStructEq_beq(v_key_103_, v_a_100_);
if (v___x_105_ == 0)
{
v_x_101_ = v_tail_104_;
goto _start;
}
else
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(v_a_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec_ref(v_a_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
return v_x_111_;
}
else
{
lean_object* v_key_113_; lean_object* v_value_114_; lean_object* v_tail_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_138_; 
v_key_113_ = lean_ctor_get(v_x_112_, 0);
v_value_114_ = lean_ctor_get(v_x_112_, 1);
v_tail_115_ = lean_ctor_get(v_x_112_, 2);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_138_ == 0)
{
v___x_117_ = v_x_112_;
v_isShared_118_ = v_isSharedCheck_138_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_tail_115_);
lean_inc(v_value_114_);
lean_inc(v_key_113_);
lean_dec(v_x_112_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_138_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v_fold_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_119_ = lean_array_get_size(v_x_111_);
v___x_120_ = l_Lean_ExprStructEq_hash(v_key_113_);
v___x_121_ = 32ULL;
v___x_122_ = lean_uint64_shift_right(v___x_120_, v___x_121_);
v_fold_123_ = lean_uint64_xor(v___x_120_, v___x_122_);
v___x_124_ = 16ULL;
v___x_125_ = lean_uint64_shift_right(v_fold_123_, v___x_124_);
v___x_126_ = lean_uint64_xor(v_fold_123_, v___x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = lean_usize_of_nat(v___x_119_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v___x_128_, v___x_129_);
v___x_131_ = lean_usize_land(v___x_127_, v___x_130_);
v___x_132_ = lean_array_uget_borrowed(v_x_111_, v___x_131_);
lean_inc(v___x_132_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 2, v___x_132_);
v___x_134_ = v___x_117_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_key_113_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_value_114_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v___x_132_);
v___x_134_ = v_reuseFailAlloc_137_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; 
v___x_135_ = lean_array_uset(v_x_111_, v___x_131_, v___x_134_);
v_x_111_ = v___x_135_;
v_x_112_ = v_tail_115_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_139_, lean_object* v_source_140_, lean_object* v_target_141_){
_start:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_array_get_size(v_source_140_);
v___x_143_ = lean_nat_dec_lt(v_i_139_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec_ref(v_source_140_);
lean_dec(v_i_139_);
return v_target_141_;
}
else
{
lean_object* v_es_144_; lean_object* v___x_145_; lean_object* v_source_146_; lean_object* v_target_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_es_144_ = lean_array_fget(v_source_140_, v_i_139_);
v___x_145_ = lean_box(0);
v_source_146_ = lean_array_fset(v_source_140_, v_i_139_, v___x_145_);
v_target_147_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_141_, v_es_144_);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_i_139_, v___x_148_);
lean_dec(v_i_139_);
v_i_139_ = v___x_149_;
v_source_140_ = v_source_146_;
v_target_141_ = v_target_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_nbuckets_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_152_ = lean_array_get_size(v_data_151_);
v___x_153_ = lean_unsigned_to_nat(2u);
v_nbuckets_154_ = lean_nat_mul(v___x_152_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_box(0);
v___x_157_ = lean_mk_array(v_nbuckets_154_, v___x_156_);
v___x_158_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_155_, v_data_151_, v___x_157_);
return v___x_158_;
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
v___x_181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(v_a_160_, v_bkt_180_);
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
v_val_192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_185_);
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
v___x_201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_a_160_, v_b_161_, v_bkt_180_);
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = l_Lean_maxRecDepthErrorMessage;
v___x_226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_228_ = l_Lean_MessageData_ofFormat(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_230_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_231_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_ref_232_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(lean_object* v_x_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___y_246_; lean_object* v_fileName_255_; lean_object* v_fileMap_256_; lean_object* v_options_257_; lean_object* v_currRecDepth_258_; lean_object* v_maxRecDepth_259_; lean_object* v_ref_260_; lean_object* v_currNamespace_261_; lean_object* v_openDecls_262_; lean_object* v_initHeartbeats_263_; lean_object* v_maxHeartbeats_264_; lean_object* v_quotContext_265_; lean_object* v_currMacroScope_266_; uint8_t v_diag_267_; lean_object* v_cancelTk_x3f_268_; uint8_t v_suppressElabErrors_269_; lean_object* v_inheritedTraceOptions_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_282_; 
v_fileName_255_ = lean_ctor_get(v___y_242_, 0);
v_fileMap_256_ = lean_ctor_get(v___y_242_, 1);
v_options_257_ = lean_ctor_get(v___y_242_, 2);
v_currRecDepth_258_ = lean_ctor_get(v___y_242_, 3);
v_maxRecDepth_259_ = lean_ctor_get(v___y_242_, 4);
v_ref_260_ = lean_ctor_get(v___y_242_, 5);
v_currNamespace_261_ = lean_ctor_get(v___y_242_, 6);
v_openDecls_262_ = lean_ctor_get(v___y_242_, 7);
v_initHeartbeats_263_ = lean_ctor_get(v___y_242_, 8);
v_maxHeartbeats_264_ = lean_ctor_get(v___y_242_, 9);
v_quotContext_265_ = lean_ctor_get(v___y_242_, 10);
v_currMacroScope_266_ = lean_ctor_get(v___y_242_, 11);
v_diag_267_ = lean_ctor_get_uint8(v___y_242_, sizeof(void*)*14);
v_cancelTk_x3f_268_ = lean_ctor_get(v___y_242_, 12);
v_suppressElabErrors_269_ = lean_ctor_get_uint8(v___y_242_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_270_ = lean_ctor_get(v___y_242_, 13);
v_isSharedCheck_282_ = !lean_is_exclusive(v___y_242_);
if (v_isSharedCheck_282_ == 0)
{
v___x_272_ = v___y_242_;
v_isShared_273_ = v_isSharedCheck_282_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_inheritedTraceOptions_270_);
lean_inc(v_cancelTk_x3f_268_);
lean_inc(v_currMacroScope_266_);
lean_inc(v_quotContext_265_);
lean_inc(v_maxHeartbeats_264_);
lean_inc(v_initHeartbeats_263_);
lean_inc(v_openDecls_262_);
lean_inc(v_currNamespace_261_);
lean_inc(v_ref_260_);
lean_inc(v_maxRecDepth_259_);
lean_inc(v_currRecDepth_258_);
lean_inc(v_options_257_);
lean_inc(v_fileMap_256_);
lean_inc(v_fileName_255_);
lean_dec(v___y_242_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_282_;
goto v_resetjp_271_;
}
v___jp_245_:
{
if (lean_obj_tag(v___y_246_) == 0)
{
return v___y_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___y_246_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___y_246_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___y_246_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___y_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
v_resetjp_271_:
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_eq(v_currRecDepth_258_, v_maxRecDepth_259_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_currRecDepth_258_, v___x_275_);
lean_dec(v_currRecDepth_258_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 3, v___x_276_);
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_fileName_255_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_fileMap_256_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_options_257_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_280_, 4, v_maxRecDepth_259_);
lean_ctor_set(v_reuseFailAlloc_280_, 5, v_ref_260_);
lean_ctor_set(v_reuseFailAlloc_280_, 6, v_currNamespace_261_);
lean_ctor_set(v_reuseFailAlloc_280_, 7, v_openDecls_262_);
lean_ctor_set(v_reuseFailAlloc_280_, 8, v_initHeartbeats_263_);
lean_ctor_set(v_reuseFailAlloc_280_, 9, v_maxHeartbeats_264_);
lean_ctor_set(v_reuseFailAlloc_280_, 10, v_quotContext_265_);
lean_ctor_set(v_reuseFailAlloc_280_, 11, v_currMacroScope_266_);
lean_ctor_set(v_reuseFailAlloc_280_, 12, v_cancelTk_x3f_268_);
lean_ctor_set(v_reuseFailAlloc_280_, 13, v_inheritedTraceOptions_270_);
lean_ctor_set_uint8(v_reuseFailAlloc_280_, sizeof(void*)*14, v_diag_267_);
lean_ctor_set_uint8(v_reuseFailAlloc_280_, sizeof(void*)*14 + 1, v_suppressElabErrors_269_);
v___x_278_ = v_reuseFailAlloc_280_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; 
v___x_279_ = lean_apply_4(v_x_240_, v___y_241_, v___x_278_, v___y_243_, lean_box(0));
v___y_246_ = v___x_279_;
goto v___jp_245_;
}
}
else
{
lean_object* v___x_281_; 
lean_del_object(v___x_272_);
lean_dec_ref(v_inheritedTraceOptions_270_);
lean_dec(v_cancelTk_x3f_268_);
lean_dec(v_currMacroScope_266_);
lean_dec(v_quotContext_265_);
lean_dec(v_maxHeartbeats_264_);
lean_dec(v_initHeartbeats_263_);
lean_dec(v_openDecls_262_);
lean_dec(v_currNamespace_261_);
lean_dec(v_maxRecDepth_259_);
lean_dec(v_currRecDepth_258_);
lean_dec_ref(v_options_257_);
lean_dec_ref(v_fileMap_256_);
lean_dec_ref(v_fileName_255_);
lean_dec(v___y_243_);
lean_dec(v___y_241_);
lean_dec_ref(v_x_240_);
v___x_281_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_260_);
v___y_246_ = v___x_281_;
goto v___jp_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_283_, v___y_284_, v___y_285_, v___y_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_289_, lean_object* v_x_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_apply_1(v_x_290_, lean_box(0));
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_296_, lean_object* v_x_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_296_, v_x_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v_key_305_; lean_object* v_value_306_; lean_object* v_tail_307_; uint8_t v___x_308_; 
v_key_305_ = lean_ctor_get(v_x_303_, 0);
v_value_306_ = lean_ctor_get(v_x_303_, 1);
v_tail_307_ = lean_ctor_get(v_x_303_, 2);
v___x_308_ = l_Lean_ExprStructEq_beq(v_key_305_, v_a_302_);
if (v___x_308_ == 0)
{
v_x_303_ = v_tail_307_;
goto _start;
}
else
{
lean_object* v___x_310_; 
lean_inc(v_value_306_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_value_306_);
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_311_, v_x_312_);
lean_dec(v_x_312_);
lean_dec_ref(v_a_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_buckets_316_; lean_object* v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v_fold_321_; uint64_t v___x_322_; uint64_t v___x_323_; uint64_t v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_buckets_316_ = lean_ctor_get(v_m_314_, 1);
v___x_317_ = lean_array_get_size(v_buckets_316_);
v___x_318_ = l_Lean_ExprStructEq_hash(v_a_315_);
v___x_319_ = 32ULL;
v___x_320_ = lean_uint64_shift_right(v___x_318_, v___x_319_);
v_fold_321_ = lean_uint64_xor(v___x_318_, v___x_320_);
v___x_322_ = 16ULL;
v___x_323_ = lean_uint64_shift_right(v_fold_321_, v___x_322_);
v___x_324_ = lean_uint64_xor(v_fold_321_, v___x_323_);
v___x_325_ = lean_uint64_to_usize(v___x_324_);
v___x_326_ = lean_usize_of_nat(v___x_317_);
v___x_327_ = ((size_t)1ULL);
v___x_328_ = lean_usize_sub(v___x_326_, v___x_327_);
v___x_329_ = lean_usize_land(v___x_325_, v___x_328_);
v___x_330_ = lean_array_uget_borrowed(v_buckets_316_, v___x_329_);
v___x_331_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_315_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_332_, v_a_333_);
lean_dec_ref(v_a_333_);
lean_dec_ref(v_m_332_);
return v_res_334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v_dummy_336_; 
v___x_335_ = lean_box(0);
v_dummy_336_ = l_Lean_Expr_sort___override(v___x_335_);
return v_dummy_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_337_, lean_object* v_post_338_, size_t v_sz_339_, size_t v_i_340_, lean_object* v_bs_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_usize_dec_lt(v_i_340_, v_sz_339_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v_post_338_);
lean_dec_ref(v_pre_337_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_bs_341_);
return v___x_347_;
}
else
{
lean_object* v_v_348_; lean_object* v___x_349_; 
v_v_348_ = lean_array_uget_borrowed(v_bs_341_, v_i_340_);
lean_inc(v___y_344_);
lean_inc_ref(v___y_343_);
lean_inc(v___y_342_);
lean_inc(v_v_348_);
lean_inc_ref(v_post_338_);
lean_inc_ref(v_pre_337_);
v___x_349_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_337_, v_post_338_, v_v_348_, v___y_342_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_351_; lean_object* v_bs_x27_352_; size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref(v___x_349_);
v___x_351_ = lean_unsigned_to_nat(0u);
v_bs_x27_352_ = lean_array_uset(v_bs_341_, v_i_340_, v___x_351_);
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_add(v_i_340_, v___x_353_);
v___x_355_ = lean_array_uset(v_bs_x27_352_, v_i_340_, v_a_350_);
v_i_340_ = v___x_354_;
v_bs_341_ = v___x_355_;
goto _start;
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v_bs_341_);
lean_dec_ref(v_post_338_);
lean_dec_ref(v_pre_337_);
v_a_357_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_349_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_349_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_365_, lean_object* v_post_366_, lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_x_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
if (lean_obj_tag(v_x_367_) == 5)
{
lean_object* v_fn_374_; lean_object* v_arg_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_fn_374_ = lean_ctor_get(v_x_367_, 0);
lean_inc_ref(v_fn_374_);
v_arg_375_ = lean_ctor_get(v_x_367_, 1);
lean_inc_ref(v_arg_375_);
lean_dec_ref(v_x_367_);
v___x_376_ = lean_array_set(v_x_368_, v_x_369_, v_arg_375_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_sub(v_x_369_, v___x_377_);
lean_dec(v_x_369_);
v_x_367_ = v_fn_374_;
v_x_368_ = v___x_376_;
v_x_369_ = v___x_378_;
goto _start;
}
else
{
lean_object* v___x_380_; 
lean_dec(v_x_369_);
lean_inc(v___y_372_);
lean_inc_ref(v___y_371_);
lean_inc(v___y_370_);
lean_inc_ref(v_post_366_);
lean_inc_ref(v_pre_365_);
v___x_380_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_365_, v_post_366_, v_x_367_, v___y_370_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; size_t v_sz_382_; size_t v___x_383_; lean_object* v___x_384_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref(v___x_380_);
v_sz_382_ = lean_array_size(v_x_368_);
v___x_383_ = ((size_t)0ULL);
lean_inc(v___y_372_);
lean_inc_ref(v___y_371_);
lean_inc(v___y_370_);
lean_inc_ref(v_post_366_);
lean_inc_ref(v_pre_365_);
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_365_, v_post_366_, v_sz_382_, v___x_383_, v_x_368_, v___y_370_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref(v___x_384_);
v___x_386_ = l_Lean_mkAppN(v_a_381_, v_a_385_);
lean_dec(v_a_385_);
v___x_387_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_365_, v_post_366_, v___x_386_, v___y_370_, v___y_371_, v___y_372_);
return v___x_387_;
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_a_381_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v_post_366_);
lean_dec_ref(v_pre_365_);
v_a_388_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_384_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_384_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v_x_368_);
lean_dec_ref(v_post_366_);
lean_dec_ref(v_pre_365_);
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v_pre_396_, lean_object* v_e_397_, lean_object* v_post_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
uint8_t v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; uint8_t v___y_411_; lean_object* v___y_421_; uint8_t v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; uint8_t v___y_426_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; uint8_t v___y_437_; lean_object* v___y_438_; uint8_t v___y_439_; lean_object* v___x_446_; 
lean_inc_ref(v_pre_396_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc_ref(v_e_397_);
v___x_446_ = lean_apply_4(v_pre_396_, v_e_397_, v___y_400_, v___y_401_, lean_box(0));
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_536_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_536_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_536_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_536_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___y_452_; 
switch(lean_obj_tag(v_a_447_))
{
case 0:
{
lean_object* v_e_526_; lean_object* v___x_528_; 
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_e_397_);
lean_dec_ref(v_pre_396_);
v_e_526_ = lean_ctor_get(v_a_447_, 0);
lean_inc_ref(v_e_526_);
lean_dec_ref(v_a_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v_e_526_);
v___x_528_ = v___x_449_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_e_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
case 1:
{
lean_object* v_e_530_; lean_object* v___x_531_; 
lean_del_object(v___x_449_);
lean_dec_ref(v_e_397_);
v_e_530_ = lean_ctor_get(v_a_447_, 0);
lean_inc_ref(v_e_530_);
lean_dec_ref(v_a_447_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_e_530_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_533_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref(v___x_531_);
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v_a_532_, v___y_399_, v___y_400_, v___y_401_);
return v___x_533_;
}
else
{
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_531_;
}
}
default: 
{
lean_object* v_e_x3f_534_; 
lean_del_object(v___x_449_);
v_e_x3f_534_ = lean_ctor_get(v_a_447_, 0);
lean_inc(v_e_x3f_534_);
lean_dec_ref(v_a_447_);
if (lean_obj_tag(v_e_x3f_534_) == 0)
{
v___y_452_ = v_e_397_;
goto v___jp_451_;
}
else
{
lean_object* v_val_535_; 
lean_dec_ref(v_e_397_);
v_val_535_ = lean_ctor_get(v_e_x3f_534_, 0);
lean_inc(v_val_535_);
lean_dec_ref(v_e_x3f_534_);
v___y_452_ = v_val_535_;
goto v___jp_451_;
}
}
}
v___jp_451_:
{
switch(lean_obj_tag(v___y_452_))
{
case 7:
{
lean_object* v_binderName_453_; lean_object* v_binderType_454_; lean_object* v_body_455_; uint8_t v_binderInfo_456_; lean_object* v___x_457_; 
v_binderName_453_ = lean_ctor_get(v___y_452_, 0);
lean_inc(v_binderName_453_);
v_binderType_454_ = lean_ctor_get(v___y_452_, 1);
v_body_455_ = lean_ctor_get(v___y_452_, 2);
v_binderInfo_456_ = lean_ctor_get_uint8(v___y_452_, sizeof(void*)*3 + 8);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_binderType_454_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_binderType_454_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_body_455_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_body_455_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; size_t v___x_461_; size_t v___x_462_; uint8_t v___x_463_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref(v___x_459_);
v___x_461_ = lean_ptr_addr(v_binderType_454_);
v___x_462_ = lean_ptr_addr(v_a_458_);
v___x_463_ = lean_usize_dec_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
v___y_434_ = v_a_460_;
v___y_435_ = v_binderName_453_;
v___y_436_ = v_a_458_;
v___y_437_ = v_binderInfo_456_;
v___y_438_ = v___y_452_;
v___y_439_ = v___x_463_;
goto v___jp_433_;
}
else
{
size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_ptr_addr(v_body_455_);
v___x_465_ = lean_ptr_addr(v_a_460_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
v___y_434_ = v_a_460_;
v___y_435_ = v_binderName_453_;
v___y_436_ = v_a_458_;
v___y_437_ = v_binderInfo_456_;
v___y_438_ = v___y_452_;
v___y_439_ = v___x_466_;
goto v___jp_433_;
}
}
else
{
lean_dec(v_a_458_);
lean_dec_ref(v___y_452_);
lean_dec(v_binderName_453_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_459_;
}
}
else
{
lean_dec_ref(v___y_452_);
lean_dec(v_binderName_453_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_457_;
}
}
case 6:
{
lean_object* v_binderName_467_; lean_object* v_binderType_468_; lean_object* v_body_469_; uint8_t v_binderInfo_470_; lean_object* v___x_471_; 
v_binderName_467_ = lean_ctor_get(v___y_452_, 0);
lean_inc(v_binderName_467_);
v_binderType_468_ = lean_ctor_get(v___y_452_, 1);
v_body_469_ = lean_ctor_get(v___y_452_, 2);
v_binderInfo_470_ = lean_ctor_get_uint8(v___y_452_, sizeof(void*)*3 + 8);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_binderType_468_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_binderType_468_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_body_469_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_body_469_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; size_t v___x_475_; size_t v___x_476_; uint8_t v___x_477_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___x_473_);
v___x_475_ = lean_ptr_addr(v_binderType_468_);
v___x_476_ = lean_ptr_addr(v_a_472_);
v___x_477_ = lean_usize_dec_eq(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
v___y_421_ = v_binderName_467_;
v___y_422_ = v_binderInfo_470_;
v___y_423_ = v_a_474_;
v___y_424_ = v_a_472_;
v___y_425_ = v___y_452_;
v___y_426_ = v___x_477_;
goto v___jp_420_;
}
else
{
size_t v___x_478_; size_t v___x_479_; uint8_t v___x_480_; 
v___x_478_ = lean_ptr_addr(v_body_469_);
v___x_479_ = lean_ptr_addr(v_a_474_);
v___x_480_ = lean_usize_dec_eq(v___x_478_, v___x_479_);
v___y_421_ = v_binderName_467_;
v___y_422_ = v_binderInfo_470_;
v___y_423_ = v_a_474_;
v___y_424_ = v_a_472_;
v___y_425_ = v___y_452_;
v___y_426_ = v___x_480_;
goto v___jp_420_;
}
}
else
{
lean_dec(v_a_472_);
lean_dec_ref(v___y_452_);
lean_dec(v_binderName_467_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_473_;
}
}
else
{
lean_dec_ref(v___y_452_);
lean_dec(v_binderName_467_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_471_;
}
}
case 8:
{
lean_object* v_declName_481_; lean_object* v_type_482_; lean_object* v_value_483_; lean_object* v_body_484_; uint8_t v_nondep_485_; lean_object* v___x_486_; 
v_declName_481_ = lean_ctor_get(v___y_452_, 0);
lean_inc(v_declName_481_);
v_type_482_ = lean_ctor_get(v___y_452_, 1);
v_value_483_ = lean_ctor_get(v___y_452_, 2);
v_body_484_ = lean_ctor_get(v___y_452_, 3);
lean_inc_ref(v_body_484_);
v_nondep_485_ = lean_ctor_get_uint8(v___y_452_, sizeof(void*)*4 + 8);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_type_482_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_type_482_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_value_483_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_value_483_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_body_484_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_body_484_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
v___x_492_ = lean_ptr_addr(v_type_482_);
v___x_493_ = lean_ptr_addr(v_a_487_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
v___y_404_ = v_nondep_485_;
v___y_405_ = v_a_491_;
v___y_406_ = v_declName_481_;
v___y_407_ = v_body_484_;
v___y_408_ = v_a_489_;
v___y_409_ = v_a_487_;
v___y_410_ = v___y_452_;
v___y_411_ = v___x_494_;
goto v___jp_403_;
}
else
{
size_t v___x_495_; size_t v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_ptr_addr(v_value_483_);
v___x_496_ = lean_ptr_addr(v_a_489_);
v___x_497_ = lean_usize_dec_eq(v___x_495_, v___x_496_);
v___y_404_ = v_nondep_485_;
v___y_405_ = v_a_491_;
v___y_406_ = v_declName_481_;
v___y_407_ = v_body_484_;
v___y_408_ = v_a_489_;
v___y_409_ = v_a_487_;
v___y_410_ = v___y_452_;
v___y_411_ = v___x_497_;
goto v___jp_403_;
}
}
else
{
lean_dec(v_a_489_);
lean_dec(v_a_487_);
lean_dec_ref(v_body_484_);
lean_dec_ref(v___y_452_);
lean_dec(v_declName_481_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_490_;
}
}
else
{
lean_dec(v_a_487_);
lean_dec_ref(v_body_484_);
lean_dec(v_declName_481_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_488_;
}
}
else
{
lean_dec_ref(v_body_484_);
lean_dec_ref(v___y_452_);
lean_dec(v_declName_481_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_486_;
}
}
case 5:
{
lean_object* v_dummy_498_; lean_object* v_nargs_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_dummy_498_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_499_ = l_Lean_Expr_getAppNumArgs(v___y_452_);
lean_inc(v_nargs_499_);
v___x_500_ = lean_mk_array(v_nargs_499_, v_dummy_498_);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_sub(v_nargs_499_, v___x_501_);
lean_dec(v_nargs_499_);
v___x_503_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_396_, v_post_398_, v___y_452_, v___x_500_, v___x_502_, v___y_399_, v___y_400_, v___y_401_);
return v___x_503_;
}
case 10:
{
lean_object* v_data_504_; lean_object* v_expr_505_; lean_object* v___x_506_; 
v_data_504_ = lean_ctor_get(v___y_452_, 0);
v_expr_505_ = lean_ctor_get(v___y_452_, 1);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_expr_505_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_expr_505_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = lean_ptr_addr(v_expr_505_);
v___x_509_ = lean_ptr_addr(v_a_507_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_inc(v_data_504_);
lean_dec_ref(v___y_452_);
v___x_511_ = l_Lean_Expr_mdata___override(v_data_504_, v_a_507_);
v___x_512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___x_511_, v___y_399_, v___y_400_, v___y_401_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; 
lean_dec(v_a_507_);
v___x_513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___y_452_, v___y_399_, v___y_400_, v___y_401_);
return v___x_513_;
}
}
else
{
lean_dec_ref(v___y_452_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_506_;
}
}
case 11:
{
lean_object* v_typeName_514_; lean_object* v_idx_515_; lean_object* v_struct_516_; lean_object* v___x_517_; 
v_typeName_514_ = lean_ctor_get(v___y_452_, 0);
v_idx_515_ = lean_ctor_get(v___y_452_, 1);
v_struct_516_ = lean_ctor_get(v___y_452_, 2);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v_struct_516_);
lean_inc_ref(v_post_398_);
lean_inc_ref(v_pre_396_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_396_, v_post_398_, v_struct_516_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; size_t v___x_519_; size_t v___x_520_; uint8_t v___x_521_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref(v___x_517_);
v___x_519_ = lean_ptr_addr(v_struct_516_);
v___x_520_ = lean_ptr_addr(v_a_518_);
v___x_521_ = lean_usize_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_inc(v_idx_515_);
lean_inc(v_typeName_514_);
lean_dec_ref(v___y_452_);
v___x_522_ = l_Lean_Expr_proj___override(v_typeName_514_, v_idx_515_, v_a_518_);
v___x_523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___x_522_, v___y_399_, v___y_400_, v___y_401_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; 
lean_dec(v_a_518_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___y_452_, v___y_399_, v___y_400_, v___y_401_);
return v___x_524_;
}
}
else
{
lean_dec_ref(v___y_452_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_pre_396_);
return v___x_517_;
}
}
default: 
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___y_452_, v___y_399_, v___y_400_, v___y_401_);
return v___x_525_;
}
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v_post_398_);
lean_dec_ref(v_e_397_);
lean_dec_ref(v_pre_396_);
v_a_537_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_446_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_446_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
v___jp_403_:
{
if (v___y_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec_ref(v___y_410_);
lean_dec_ref(v___y_407_);
v___x_412_ = l_Lean_Expr_letE___override(v___y_406_, v___y_409_, v___y_408_, v___y_405_, v___y_404_);
v___x_413_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___x_412_, v___y_399_, v___y_400_, v___y_401_);
return v___x_413_;
}
else
{
size_t v___x_414_; size_t v___x_415_; uint8_t v___x_416_; 
v___x_414_ = lean_ptr_addr(v___y_407_);
lean_dec_ref(v___y_407_);
v___x_415_ = lean_ptr_addr(v___y_405_);
v___x_416_ = lean_usize_dec_eq(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v___y_410_);
v___x_417_ = l_Lean_Expr_letE___override(v___y_406_, v___y_409_, v___y_408_, v___y_405_, v___y_404_);
v___x_418_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___x_417_, v___y_399_, v___y_400_, v___y_401_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; 
lean_dec_ref(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
v___x_419_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___y_410_, v___y_399_, v___y_400_, v___y_401_);
return v___x_419_;
}
}
}
v___jp_420_:
{
if (v___y_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec_ref(v___y_425_);
v___x_427_ = l_Lean_Expr_lam___override(v___y_421_, v___y_424_, v___y_423_, v___y_422_);
v___x_428_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___x_427_, v___y_399_, v___y_400_, v___y_401_);
return v___x_428_;
}
else
{
uint8_t v___x_429_; 
v___x_429_ = l_Lean_instBEqBinderInfo_beq(v___y_422_, v___y_422_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v___y_425_);
v___x_430_ = l_Lean_Expr_lam___override(v___y_421_, v___y_424_, v___y_423_, v___y_422_);
v___x_431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___x_430_, v___y_399_, v___y_400_, v___y_401_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; 
lean_dec_ref(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_421_);
v___x_432_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___y_425_, v___y_399_, v___y_400_, v___y_401_);
return v___x_432_;
}
}
}
v___jp_433_:
{
if (v___y_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec_ref(v___y_438_);
v___x_440_ = l_Lean_Expr_forallE___override(v___y_435_, v___y_436_, v___y_434_, v___y_437_);
v___x_441_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___x_440_, v___y_399_, v___y_400_, v___y_401_);
return v___x_441_;
}
else
{
uint8_t v___x_442_; 
v___x_442_ = l_Lean_instBEqBinderInfo_beq(v___y_437_, v___y_437_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec_ref(v___y_438_);
v___x_443_ = l_Lean_Expr_forallE___override(v___y_435_, v___y_436_, v___y_434_, v___y_437_);
v___x_444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___x_443_, v___y_399_, v___y_400_, v___y_401_);
return v___x_444_;
}
else
{
lean_object* v___x_445_; 
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
v___x_445_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_396_, v_post_398_, v___y_438_, v___y_399_, v___y_400_, v___y_401_);
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_545_, lean_object* v_e_546_, lean_object* v_post_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v_pre_545_, v_e_546_, v_post_547_, v___y_548_, v___y_549_, v___y_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_553_, lean_object* v_post_554_, lean_object* v_e_555_, lean_object* v_a_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_inc(v_a_556_);
v___x_560_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_560_, 0, lean_box(0));
lean_closure_set(v___x_560_, 1, lean_box(0));
lean_closure_set(v___x_560_, 2, v_a_556_);
v___x_561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_560_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_592_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_592_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_592_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_592_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_562_, v_e_555_);
lean_dec(v_a_562_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___f_567_; lean_object* v___x_568_; 
lean_del_object(v___x_564_);
lean_inc_ref(v_e_555_);
v___f_567_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 7, 3);
lean_closure_set(v___f_567_, 0, v_pre_553_);
lean_closure_set(v___f_567_, 1, v_e_555_);
lean_closure_set(v___f_567_, 2, v_post_554_);
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
lean_inc(v_a_556_);
v___x_568_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_567_, v_a_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___f_570_; lean_object* v___x_571_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref(v___x_568_);
lean_inc(v_a_569_);
v___f_570_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_570_, 0, v_a_556_);
lean_closure_set(v___f_570_, 1, v_e_555_);
lean_closure_set(v___f_570_, 2, v_a_569_);
v___x_571_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_570_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v___x_571_, 0);
lean_dec(v_unused_579_);
v___x_573_ = v___x_571_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_dec(v___x_571_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_a_569_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_569_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_a_569_);
v_a_580_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_571_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_571_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_e_555_);
return v___x_568_;
}
}
else
{
lean_object* v_val_588_; lean_object* v___x_590_; 
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_e_555_);
lean_dec_ref(v_post_554_);
lean_dec_ref(v_pre_553_);
v_val_588_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_val_588_);
lean_dec_ref(v___x_566_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v_val_588_);
v___x_590_ = v___x_564_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_val_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_e_555_);
lean_dec_ref(v_post_554_);
lean_dec_ref(v_pre_553_);
v_a_593_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_561_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_561_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_601_, lean_object* v_post_602_, lean_object* v_e_603_, lean_object* v_a_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
lean_inc_ref(v_post_602_);
lean_inc(v___y_606_);
lean_inc_ref(v___y_605_);
lean_inc_ref(v_e_603_);
v___x_608_ = lean_apply_4(v_post_602_, v_e_603_, v___y_605_, v___y_606_, lean_box(0));
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_627_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_627_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_627_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_627_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
switch(lean_obj_tag(v_a_609_))
{
case 0:
{
lean_object* v_e_613_; lean_object* v___x_615_; 
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_e_603_);
lean_dec_ref(v_post_602_);
lean_dec_ref(v_pre_601_);
v_e_613_ = lean_ctor_get(v_a_609_, 0);
lean_inc_ref(v_e_613_);
lean_dec_ref(v_a_609_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v_e_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_e_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
case 1:
{
lean_object* v_e_617_; lean_object* v___x_618_; 
lean_del_object(v___x_611_);
lean_dec_ref(v_e_603_);
v_e_617_ = lean_ctor_get(v_a_609_, 0);
lean_inc_ref(v_e_617_);
lean_dec_ref(v_a_609_);
v___x_618_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_601_, v_post_602_, v_e_617_, v_a_604_, v___y_605_, v___y_606_);
return v___x_618_;
}
default: 
{
lean_object* v_e_x3f_619_; 
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_post_602_);
lean_dec_ref(v_pre_601_);
v_e_x3f_619_ = lean_ctor_get(v_a_609_, 0);
lean_inc(v_e_x3f_619_);
lean_dec_ref(v_a_609_);
if (lean_obj_tag(v_e_x3f_619_) == 0)
{
lean_object* v___x_621_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v_e_603_);
v___x_621_ = v___x_611_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_e_603_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v_val_623_; lean_object* v___x_625_; 
lean_dec_ref(v_e_603_);
v_val_623_ = lean_ctor_get(v_e_x3f_619_, 0);
lean_inc(v_val_623_);
lean_dec_ref(v_e_x3f_619_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v_val_623_);
v___x_625_ = v___x_611_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_val_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_e_603_);
lean_dec_ref(v_post_602_);
lean_dec_ref(v_pre_601_);
v_a_628_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_608_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_608_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_636_, lean_object* v_post_637_, lean_object* v_e_638_, lean_object* v_a_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_636_, v_post_637_, v_e_638_, v_a_639_, v___y_640_, v___y_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_644_, lean_object* v_post_645_, lean_object* v_sz_646_, lean_object* v_i_647_, lean_object* v_bs_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
size_t v_sz_boxed_653_; size_t v_i_boxed_654_; lean_object* v_res_655_; 
v_sz_boxed_653_ = lean_unbox_usize(v_sz_646_);
lean_dec(v_sz_646_);
v_i_boxed_654_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_644_, v_post_645_, v_sz_boxed_653_, v_i_boxed_654_, v_bs_648_, v___y_649_, v___y_650_, v___y_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_656_, lean_object* v_post_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_656_, v_post_657_, v_x_658_, v_x_659_, v_x_660_, v___y_661_, v___y_662_, v___y_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_666_, lean_object* v_post_667_, lean_object* v_e_668_, lean_object* v_a_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_666_, v_post_667_, v_e_668_, v_a_669_, v___y_670_, v___y_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_apply_1(v_x_675_, lean_box(0));
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_681_, lean_object* v_x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_681_, v_x_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
return v_res_686_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_box(0);
v___x_688_ = lean_unsigned_to_nat(16u);
v___x_689_ = lean_mk_array(v___x_688_, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_694_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_694_, 0, lean_box(0));
lean_closure_set(v___x_694_, 1, lean_box(0));
lean_closure_set(v___x_694_, 2, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_695_, lean_object* v_pre_696_, lean_object* v_post_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_a_703_; lean_object* v___x_704_; 
v___x_701_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_702_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_701_, v___y_698_, v___y_699_);
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v_a_703_);
v___x_704_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_696_, v_post_697_, v_input_695_, v_a_703_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_704_);
v___x_706_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_706_, 0, lean_box(0));
lean_closure_set(v___x_706_, 1, lean_box(0));
lean_closure_set(v___x_706_, 2, v_a_703_);
v___x_707_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_706_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v___x_707_, 0);
lean_dec(v_unused_715_);
v___x_709_ = v___x_707_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_dec(v___x_707_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v_a_705_);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_705_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_dec(v_a_703_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_716_, lean_object* v_pre_717_, lean_object* v_post_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_716_, v_pre_717_, v_post_718_, v___y_719_, v___y_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___f_729_; lean_object* v___f_730_; lean_object* v___x_731_; 
v___f_729_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_730_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_731_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_725_, v___f_729_, v___f_730_, v_a_726_, v_a_727_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Meta_elimOptParam(v_type_732_, v_a_733_, v_a_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_737_, lean_object* v_m_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_738_, v_a_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_741_, lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_741_, v_m_742_, v_a_743_);
lean_dec_ref(v_a_743_);
lean_dec_ref(v_m_742_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_745_, lean_object* v_ref_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_746_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_751_, lean_object* v_ref_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_751_, v_ref_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_757_, lean_object* v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_758_, v___y_759_, v___y_760_, v___y_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_764_, lean_object* v_x_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_764_, v_x_765_, v___y_766_, v___y_767_, v___y_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_771_, lean_object* v_m_772_, lean_object* v_a_773_, lean_object* v_b_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_772_, v_a_773_, v_b_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_776_, lean_object* v_a_777_, lean_object* v_x_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_777_, v_x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_780_, lean_object* v_a_781_, lean_object* v_x_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_780_, v_a_781_, v_x_782_);
lean_dec(v_x_782_);
lean_dec_ref(v_a_781_);
return v_res_783_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_784_, lean_object* v_a_785_, lean_object* v_x_786_){
_start:
{
uint8_t v___x_787_; 
v___x_787_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(v_a_785_, v_x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_788_, lean_object* v_a_789_, lean_object* v_x_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_788_, v_a_789_, v_x_790_);
lean_dec(v_x_790_);
lean_dec_ref(v_a_789_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_793_, lean_object* v_data_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_data_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_796_, lean_object* v_a_797_, lean_object* v_b_798_, lean_object* v_x_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_a_797_, v_b_798_, v_x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_801_, lean_object* v_i_802_, lean_object* v_source_803_, lean_object* v_target_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_802_, v_source_803_, v_target_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_807_, v_x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_810_, lean_object* v_as_811_, size_t v_sz_812_, size_t v_i_813_, lean_object* v_b_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_a_821_; uint8_t v___x_825_; 
v___x_825_ = lean_usize_dec_lt(v_i_813_, v_sz_812_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v_b_814_);
return v___x_826_;
}
else
{
lean_object* v_snd_827_; lean_object* v_fst_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_906_; 
v_snd_827_ = lean_ctor_get(v_b_814_, 1);
v_fst_828_ = lean_ctor_get(v_b_814_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_b_814_);
if (v_isSharedCheck_906_ == 0)
{
v___x_830_ = v_b_814_;
v_isShared_831_ = v_isSharedCheck_906_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_snd_827_);
lean_inc(v_fst_828_);
lean_dec(v_b_814_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_906_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_array_832_; lean_object* v_start_833_; lean_object* v_stop_834_; uint8_t v___x_835_; 
v_array_832_ = lean_ctor_get(v_snd_827_, 0);
v_start_833_ = lean_ctor_get(v_snd_827_, 1);
v_stop_834_ = lean_ctor_get(v_snd_827_, 2);
v___x_835_ = lean_nat_dec_lt(v_start_833_, v_stop_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_837_; 
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
if (v_isShared_831_ == 0)
{
v___x_837_ = v___x_830_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_fst_828_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_snd_827_);
v___x_837_ = v_reuseFailAlloc_839_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; 
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
else
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_902_; 
lean_inc(v_stop_834_);
lean_inc(v_start_833_);
lean_inc_ref(v_array_832_);
v_isSharedCheck_902_ = !lean_is_exclusive(v_snd_827_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; lean_object* v_unused_904_; lean_object* v_unused_905_; 
v_unused_903_ = lean_ctor_get(v_snd_827_, 2);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_snd_827_, 1);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_snd_827_, 0);
lean_dec(v_unused_905_);
v___x_841_ = v_snd_827_;
v_isShared_842_ = v_isSharedCheck_902_;
goto v_resetjp_840_;
}
else
{
lean_dec(v_snd_827_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_902_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_a_843_; lean_object* v___x_844_; 
v_a_843_ = lean_array_uget_borrowed(v_as_811_, v_i_813_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v_a_843_);
v___x_844_ = lean_infer_type(v_a_843_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref(v___x_844_);
v___x_846_ = lean_array_fget(v_array_832_, v_start_833_);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_add(v_start_833_, v___x_847_);
lean_dec(v_start_833_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v___x_848_);
v___x_850_ = v___x_841_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_array_832_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_stop_834_);
v___x_850_ = v_reuseFailAlloc_893_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
if (v_skipIfPropOrEq_810_ == 0)
{
lean_object* v___x_851_; 
lean_dec(v_a_845_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v_a_843_);
v___x_851_ = l_Lean_Meta_mkEqHEq(v_a_843_, v___x_846_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref(v___x_851_);
v___x_853_ = lean_array_push(v_fst_828_, v_a_852_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___x_850_);
lean_ctor_set(v___x_830_, 0, v___x_853_);
v___x_855_ = v___x_830_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
v_a_821_ = v___x_855_;
goto v___jp_820_;
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v___x_850_);
lean_del_object(v___x_830_);
lean_dec(v_fst_828_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
v_a_857_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_851_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_851_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
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
else
{
lean_object* v___x_865_; 
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
v___x_865_ = l_Lean_Meta_isProp(v_a_845_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; uint8_t v___x_871_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref(v___x_865_);
v___x_871_ = lean_unbox(v_a_866_);
lean_dec(v_a_866_);
if (v___x_871_ == 0)
{
uint8_t v___x_872_; 
v___x_872_ = lean_expr_eqv(v_a_843_, v___x_846_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
lean_del_object(v___x_830_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
lean_inc(v_a_843_);
v___x_873_ = l_Lean_Meta_mkEqHEq(v_a_843_, v___x_846_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = lean_array_push(v_fst_828_, v_a_874_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_850_);
v_a_821_ = v___x_876_;
goto v___jp_820_;
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v___x_850_);
lean_dec(v_fst_828_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
v_a_877_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_873_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_873_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_dec(v___x_846_);
goto v___jp_867_;
}
}
else
{
lean_dec(v___x_846_);
goto v___jp_867_;
}
v___jp_867_:
{
lean_object* v___x_869_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___x_850_);
v___x_869_ = v___x_830_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_fst_828_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_850_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
v_a_821_ = v___x_869_;
goto v___jp_820_;
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref(v___x_850_);
lean_dec(v___x_846_);
lean_del_object(v___x_830_);
lean_dec(v_fst_828_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
v_a_885_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_865_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_865_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_del_object(v___x_841_);
lean_dec(v_stop_834_);
lean_dec(v_start_833_);
lean_dec_ref(v_array_832_);
lean_del_object(v___x_830_);
lean_dec(v_fst_828_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
v_a_894_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_844_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_844_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
}
v___jp_820_:
{
size_t v___x_822_; size_t v___x_823_; 
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_add(v_i_813_, v___x_822_);
v_i_813_ = v___x_823_;
v_b_814_ = v_a_821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_907_, lean_object* v_as_908_, lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_917_; size_t v_sz_boxed_918_; size_t v_i_boxed_919_; lean_object* v_res_920_; 
v_skipIfPropOrEq_boxed_917_ = lean_unbox(v_skipIfPropOrEq_907_);
v_sz_boxed_918_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_919_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_917_, v_as_908_, v_sz_boxed_918_, v_i_boxed_919_, v_b_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec_ref(v_as_908_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_923_, lean_object* v_args2_924_, uint8_t v_skipIfPropOrEq_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; lean_object* v_eqs_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; size_t v_sz_936_; size_t v___x_937_; lean_object* v___x_938_; 
v___x_931_ = lean_unsigned_to_nat(0u);
v_eqs_932_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_933_ = lean_array_get_size(v_args2_924_);
v___x_934_ = l_Array_toSubarray___redArg(v_args2_924_, v___x_931_, v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v_eqs_932_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v_sz_936_ = lean_array_size(v_args1_923_);
v___x_937_ = ((size_t)0ULL);
v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_925_, v_args1_923_, v_sz_936_, v___x_937_, v___x_935_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_fst_943_; lean_object* v___x_945_; 
v_fst_943_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_fst_943_);
lean_dec(v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_fst_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_fst_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_938_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_938_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_956_, lean_object* v_args2_957_, lean_object* v_skipIfPropOrEq_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_964_; lean_object* v_res_965_; 
v_skipIfPropOrEq_boxed_964_ = lean_unbox(v_skipIfPropOrEq_958_);
v_res_965_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_956_, v_args2_957_, v_skipIfPropOrEq_boxed_964_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec_ref(v_args1_956_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_apply_6(v_k_966_, v_b_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, lean_box(0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_974_, v_b_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_982_, uint8_t v_bi_983_, lean_object* v_type_984_, lean_object* v_k_985_, uint8_t v_kind_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___f_992_; lean_object* v___x_993_; 
v___f_992_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_992_, 0, v_k_985_);
v___x_993_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_982_, v_bi_983_, v_type_984_, v___f_992_, v_kind_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_993_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_993_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1010_, lean_object* v_bi_1011_, lean_object* v_type_1012_, lean_object* v_k_1013_, lean_object* v_kind_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
uint8_t v_bi_boxed_1020_; uint8_t v_kind_boxed_1021_; lean_object* v_res_1022_; 
v_bi_boxed_1020_ = lean_unbox(v_bi_1011_);
v_kind_boxed_1021_ = lean_unbox(v_kind_1014_);
v_res_1022_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1010_, v_bi_boxed_1020_, v_type_1012_, v_k_1013_, v_kind_boxed_1021_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1023_, lean_object* v_name_1024_, uint8_t v_bi_1025_, lean_object* v_type_1026_, lean_object* v_k_1027_, uint8_t v_kind_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1024_, v_bi_1025_, v_type_1026_, v_k_1027_, v_kind_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_name_1036_, lean_object* v_bi_1037_, lean_object* v_type_1038_, lean_object* v_k_1039_, lean_object* v_kind_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v_bi_boxed_1046_; uint8_t v_kind_boxed_1047_; lean_object* v_res_1048_; 
v_bi_boxed_1046_ = lean_unbox(v_bi_1037_);
v_kind_boxed_1047_ = lean_unbox(v_kind_1040_);
v_res_1048_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1035_, v_name_1036_, v_bi_boxed_1046_, v_type_1038_, v_k_1039_, v_kind_boxed_1047_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; lean_object* v_env_1056_; lean_object* v___x_1057_; lean_object* v_mctx_1058_; lean_object* v_lctx_1059_; lean_object* v_options_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1055_ = lean_st_ref_get(v___y_1053_);
v_env_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_ref(v_env_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = lean_st_ref_get(v___y_1051_);
v_mctx_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc_ref(v_mctx_1058_);
lean_dec(v___x_1057_);
v_lctx_1059_ = lean_ctor_get(v___y_1050_, 2);
v_options_1060_ = lean_ctor_get(v___y_1052_, 2);
lean_inc_ref(v_options_1060_);
lean_inc_ref(v_lctx_1059_);
v___x_1061_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1061_, 0, v_env_1056_);
lean_ctor_set(v___x_1061_, 1, v_mctx_1058_);
lean_ctor_set(v___x_1061_, 2, v_lctx_1059_);
lean_ctor_set(v___x_1061_, 3, v_options_1060_);
v___x_1062_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_msgData_1049_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_ref_1077_; lean_object* v___x_1078_; lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1087_; 
v_ref_1077_ = lean_ctor_get(v___y_1074_, 5);
v___x_1078_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_inc(v_ref_1077_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v_ref_1077_);
lean_ctor_set(v___x_1083_, 1, v_a_1079_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 1);
lean_ctor_set(v___x_1081_, 0, v___x_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1095_, lean_object* v_body_1096_, lean_object* v_args2_1097_, lean_object* v_args2New_1098_, lean_object* v_ctorVal_1099_, lean_object* v_useEq_1100_, lean_object* v_args1_1101_, lean_object* v_resultType_1102_, lean_object* v_k_1103_, lean_object* v_arg2_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v_useEq_boxed_1110_; lean_object* v_res_1111_; 
v_useEq_boxed_1110_ = lean_unbox(v_useEq_1100_);
v_res_1111_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1095_, v_body_1096_, v_args2_1097_, v_args2New_1098_, v_ctorVal_1099_, v_useEq_boxed_1110_, v_args1_1101_, v_resultType_1102_, v_k_1103_, v_arg2_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec_ref(v_body_1096_);
lean_dec(v_i_1095_);
return v_res_1111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1118_, uint8_t v_useEq_1119_, lean_object* v_args1_1120_, lean_object* v_resultType_1121_, lean_object* v_k_1122_, lean_object* v_i_1123_, lean_object* v_type_1124_, lean_object* v_args2_1125_, lean_object* v_args2New_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_array_get_size(v_args1_1120_);
v___x_1133_ = lean_nat_dec_lt(v_i_1123_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref(v_type_1124_);
lean_dec(v_i_1123_);
lean_dec_ref(v_resultType_1121_);
lean_dec_ref(v_args1_1120_);
lean_dec_ref(v_ctorVal_1118_);
v___x_1134_ = lean_apply_7(v_k_1122_, v_args2_1125_, v_args2New_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, lean_box(0));
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; 
lean_inc(v_a_1130_);
lean_inc_ref(v_a_1129_);
lean_inc(v_a_1128_);
lean_inc_ref(v_a_1127_);
v___x_1135_ = lean_whnf(v_type_1124_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v___x_1135_);
if (lean_obj_tag(v_a_1136_) == 7)
{
lean_object* v_binderName_1137_; lean_object* v_binderType_1138_; lean_object* v_body_1139_; lean_object* v_lctx_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v_binderName_1137_ = lean_ctor_get(v_a_1136_, 0);
lean_inc(v_binderName_1137_);
v_binderType_1138_ = lean_ctor_get(v_a_1136_, 1);
lean_inc_ref(v_binderType_1138_);
v_body_1139_ = lean_ctor_get(v_a_1136_, 2);
lean_inc_ref(v_body_1139_);
lean_dec_ref(v_a_1136_);
v_lctx_1140_ = lean_ctor_get(v_a_1127_, 2);
v___x_1141_ = lean_array_fget_borrowed(v_args1_1120_, v_i_1123_);
lean_inc(v___x_1141_);
lean_inc_ref(v_lctx_1140_);
v___x_1142_ = l_Lean_Meta_occursOrInType(v_lctx_1140_, v___x_1141_, v_resultType_1121_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___f_1144_; uint8_t v___y_1146_; 
v___x_1143_ = lean_box(v_useEq_1119_);
v___f_1144_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1144_, 0, v_i_1123_);
lean_closure_set(v___f_1144_, 1, v_body_1139_);
lean_closure_set(v___f_1144_, 2, v_args2_1125_);
lean_closure_set(v___f_1144_, 3, v_args2New_1126_);
lean_closure_set(v___f_1144_, 4, v_ctorVal_1118_);
lean_closure_set(v___f_1144_, 5, v___x_1143_);
lean_closure_set(v___f_1144_, 6, v_args1_1120_);
lean_closure_set(v___f_1144_, 7, v_resultType_1121_);
lean_closure_set(v___f_1144_, 8, v_k_1122_);
if (v_useEq_1119_ == 0)
{
uint8_t v___x_1149_; 
v___x_1149_ = 1;
v___y_1146_ = v___x_1149_;
goto v___jp_1145_;
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = 0;
v___y_1146_ = v___x_1150_;
goto v___jp_1145_;
}
v___jp_1145_:
{
uint8_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = 0;
v___x_1148_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1137_, v___y_1146_, v_binderType_1138_, v___f_1144_, v___x_1147_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1148_;
}
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref(v_binderType_1138_);
lean_dec(v_binderName_1137_);
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_add(v_i_1123_, v___x_1151_);
lean_dec(v_i_1123_);
v___x_1153_ = lean_expr_instantiate1(v_body_1139_, v___x_1141_);
lean_dec_ref(v_body_1139_);
lean_inc(v___x_1141_);
v___x_1154_ = lean_array_push(v_args2_1125_, v___x_1141_);
v_i_1123_ = v___x_1152_;
v_type_1124_ = v___x_1153_;
v_args2_1125_ = v___x_1154_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1156_; lean_object* v_name_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec(v_a_1136_);
lean_dec_ref(v_args2New_1126_);
lean_dec_ref(v_args2_1125_);
lean_dec(v_i_1123_);
lean_dec_ref(v_k_1122_);
lean_dec_ref(v_resultType_1121_);
lean_dec_ref(v_args1_1120_);
v_toConstantVal_1156_ = lean_ctor_get(v_ctorVal_1118_, 0);
lean_inc_ref(v_toConstantVal_1156_);
lean_dec_ref(v_ctorVal_1118_);
v_name_1157_ = lean_ctor_get(v_toConstantVal_1156_, 0);
lean_inc(v_name_1157_);
lean_dec_ref(v_toConstantVal_1156_);
v___x_1158_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1159_ = l_Lean_MessageData_ofName(v_name_1157_);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1162_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
return v___x_1163_;
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec_ref(v_args2New_1126_);
lean_dec_ref(v_args2_1125_);
lean_dec(v_i_1123_);
lean_dec_ref(v_k_1122_);
lean_dec_ref(v_resultType_1121_);
lean_dec_ref(v_args1_1120_);
lean_dec_ref(v_ctorVal_1118_);
v_a_1164_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1135_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1135_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1172_, lean_object* v_body_1173_, lean_object* v_args2_1174_, lean_object* v_args2New_1175_, lean_object* v_ctorVal_1176_, uint8_t v_useEq_1177_, lean_object* v_args1_1178_, lean_object* v_resultType_1179_, lean_object* v_k_1180_, lean_object* v_arg2_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_add(v_i_1172_, v___x_1187_);
v___x_1189_ = lean_expr_instantiate1(v_body_1173_, v_arg2_1181_);
lean_inc_ref(v_arg2_1181_);
v___x_1190_ = lean_array_push(v_args2_1174_, v_arg2_1181_);
v___x_1191_ = lean_array_push(v_args2New_1175_, v_arg2_1181_);
v___x_1192_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1176_, v_useEq_1177_, v_args1_1178_, v_resultType_1179_, v_k_1180_, v___x_1188_, v___x_1189_, v___x_1190_, v___x_1191_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1193_, lean_object* v_useEq_1194_, lean_object* v_args1_1195_, lean_object* v_resultType_1196_, lean_object* v_k_1197_, lean_object* v_i_1198_, lean_object* v_type_1199_, lean_object* v_args2_1200_, lean_object* v_args2New_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
uint8_t v_useEq_boxed_1207_; lean_object* v_res_1208_; 
v_useEq_boxed_1207_ = lean_unbox(v_useEq_1194_);
v_res_1208_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1193_, v_useEq_boxed_1207_, v_args1_1195_, v_resultType_1196_, v_k_1197_, v_i_1198_, v_type_1199_, v_args2_1200_, v_args2New_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1209_, lean_object* v_msg_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1217_, lean_object* v_msg_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1217_, v_msg_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1225_, lean_object* v_h__1_1226_, lean_object* v_h__2_1227_){
_start:
{
if (lean_obj_tag(v_____x_1225_) == 7)
{
lean_object* v_binderName_1228_; lean_object* v_binderType_1229_; lean_object* v_body_1230_; uint8_t v_binderInfo_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec(v_h__2_1227_);
v_binderName_1228_ = lean_ctor_get(v_____x_1225_, 0);
lean_inc(v_binderName_1228_);
v_binderType_1229_ = lean_ctor_get(v_____x_1225_, 1);
lean_inc_ref(v_binderType_1229_);
v_body_1230_ = lean_ctor_get(v_____x_1225_, 2);
lean_inc_ref(v_body_1230_);
v_binderInfo_1231_ = lean_ctor_get_uint8(v_____x_1225_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1225_);
v___x_1232_ = lean_box(v_binderInfo_1231_);
v___x_1233_ = lean_apply_4(v_h__1_1226_, v_binderName_1228_, v_binderType_1229_, v_body_1230_, v___x_1232_);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; 
lean_dec(v_h__1_1226_);
v___x_1234_ = lean_apply_2(v_h__2_1227_, v_____x_1225_, lean_box(0));
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1235_, lean_object* v_____x_1236_, lean_object* v_h__1_1237_, lean_object* v_h__2_1238_){
_start:
{
if (lean_obj_tag(v_____x_1236_) == 7)
{
lean_object* v_binderName_1239_; lean_object* v_binderType_1240_; lean_object* v_body_1241_; uint8_t v_binderInfo_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_h__2_1238_);
v_binderName_1239_ = lean_ctor_get(v_____x_1236_, 0);
lean_inc(v_binderName_1239_);
v_binderType_1240_ = lean_ctor_get(v_____x_1236_, 1);
lean_inc_ref(v_binderType_1240_);
v_body_1241_ = lean_ctor_get(v_____x_1236_, 2);
lean_inc_ref(v_body_1241_);
v_binderInfo_1242_ = lean_ctor_get_uint8(v_____x_1236_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1236_);
v___x_1243_ = lean_box(v_binderInfo_1242_);
v___x_1244_ = lean_apply_4(v_h__1_1237_, v_binderName_1239_, v_binderType_1240_, v_body_1241_, v___x_1243_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; 
lean_dec(v_h__1_1237_);
v___x_1245_ = lean_apply_2(v_h__2_1238_, v_____x_1236_, lean_box(0));
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1246_, lean_object* v_b_1247_, lean_object* v_c_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_apply_7(v_k_1246_, v_b_1247_, v_c_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, lean_box(0));
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1255_, lean_object* v_b_1256_, lean_object* v_c_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1255_, v_b_1256_, v_c_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1264_, lean_object* v_k_1265_, uint8_t v_cleanupAnnotations_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___f_1272_; uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1272_, 0, v_k_1265_);
v___x_1273_ = 0;
v___x_1274_ = lean_box(0);
v___x_1275_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1273_, v___x_1274_, v_type_1264_, v___f_1272_, v_cleanupAnnotations_1266_, v___x_1273_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1275_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1275_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1292_, lean_object* v_k_1293_, lean_object* v_cleanupAnnotations_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1300_; lean_object* v_res_1301_; 
v_cleanupAnnotations_boxed_1300_ = lean_unbox(v_cleanupAnnotations_1294_);
v_res_1301_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1292_, v_k_1293_, v_cleanupAnnotations_boxed_1300_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1302_, lean_object* v_type_1303_, lean_object* v_k_1304_, uint8_t v_cleanupAnnotations_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1303_, v_k_1304_, v_cleanupAnnotations_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1312_, lean_object* v_type_1313_, lean_object* v_k_1314_, lean_object* v_cleanupAnnotations_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1321_; lean_object* v_res_1322_; 
v_cleanupAnnotations_boxed_1321_ = lean_unbox(v_cleanupAnnotations_1315_);
v_res_1322_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1312_, v_type_1313_, v_k_1314_, v_cleanupAnnotations_boxed_1321_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1323_, lean_object* v_maxFVars_x3f_1324_, lean_object* v_k_1325_, uint8_t v_cleanupAnnotations_1326_, uint8_t v_whnfType_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___f_1333_; lean_object* v___x_1334_; 
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1333_, 0, v_k_1325_);
v___x_1334_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1323_, v_maxFVars_x3f_1324_, v___f_1333_, v_cleanupAnnotations_1326_, v_whnfType_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1334_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1334_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1351_, lean_object* v_maxFVars_x3f_1352_, lean_object* v_k_1353_, lean_object* v_cleanupAnnotations_1354_, lean_object* v_whnfType_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1361_; uint8_t v_whnfType_boxed_1362_; lean_object* v_res_1363_; 
v_cleanupAnnotations_boxed_1361_ = lean_unbox(v_cleanupAnnotations_1354_);
v_whnfType_boxed_1362_ = lean_unbox(v_whnfType_1355_);
v_res_1363_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1351_, v_maxFVars_x3f_1352_, v_k_1353_, v_cleanupAnnotations_boxed_1361_, v_whnfType_boxed_1362_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1364_, lean_object* v_type_1365_, lean_object* v_maxFVars_x3f_1366_, lean_object* v_k_1367_, uint8_t v_cleanupAnnotations_1368_, uint8_t v_whnfType_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1365_, v_maxFVars_x3f_1366_, v_k_1367_, v_cleanupAnnotations_1368_, v_whnfType_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_type_1377_, lean_object* v_maxFVars_x3f_1378_, lean_object* v_k_1379_, lean_object* v_cleanupAnnotations_1380_, lean_object* v_whnfType_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1387_; uint8_t v_whnfType_boxed_1388_; lean_object* v_res_1389_; 
v_cleanupAnnotations_boxed_1387_ = lean_unbox(v_cleanupAnnotations_1380_);
v_whnfType_boxed_1388_ = lean_unbox(v_whnfType_1381_);
v_res_1389_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1376_, v_type_1377_, v_maxFVars_x3f_1378_, v_k_1379_, v_cleanupAnnotations_boxed_1387_, v_whnfType_boxed_1388_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1390_, lean_object* v_us_1391_, lean_object* v_params_1392_, lean_object* v_args1_1393_, uint8_t v_useEq_1394_, lean_object* v_args2_1395_, lean_object* v_args2New_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1402_ = l_Lean_mkConst(v_name_1390_, v_us_1391_);
v___x_1403_ = l_Lean_mkAppN(v___x_1402_, v_params_1392_);
lean_inc_ref(v___x_1403_);
v___x_1404_ = l_Lean_mkAppN(v___x_1403_, v_args1_1393_);
v___x_1405_ = l_Lean_mkAppN(v___x_1403_, v_args2_1395_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
v___x_1406_ = l_Lean_Meta_mkEq(v___x_1404_, v___x_1405_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; uint8_t v___x_1408_; lean_object* v_result_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___x_1455_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = 1;
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
v___x_1455_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1393_, v_args2_1395_, v___x_1408_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1487_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1487_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1487_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; 
v___x_1460_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1456_);
if (lean_obj_tag(v___x_1460_) == 1)
{
lean_del_object(v___x_1458_);
if (v_useEq_1394_ == 0)
{
lean_object* v_val_1461_; lean_object* v___x_1462_; 
v_val_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_val_1461_);
lean_dec_ref(v___x_1460_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
v___x_1462_ = l_Lean_mkArrow(v_a_1407_, v_val_1461_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
v_result_1410_ = v_a_1463_;
v___y_1411_ = v___y_1397_;
v___y_1412_ = v___y_1398_;
v___y_1413_ = v___y_1399_;
v___y_1414_ = v___y_1400_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
v_a_1464_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1462_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1462_);
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
lean_object* v_val_1472_; lean_object* v___x_1473_; 
v_val_1472_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_val_1472_);
lean_dec_ref(v___x_1460_);
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
v___x_1473_ = l_Lean_Meta_mkEq(v_a_1407_, v_val_1472_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1473_);
v_result_1410_ = v_a_1474_;
v___y_1411_ = v___y_1397_;
v___y_1412_ = v___y_1398_;
v___y_1413_ = v___y_1399_;
v___y_1414_ = v___y_1400_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
v_a_1475_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1473_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1473_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
lean_dec(v___x_1460_);
lean_dec(v_a_1407_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
v___x_1483_ = lean_box(0);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1483_);
v___x_1485_ = v___x_1458_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_a_1407_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
v_a_1488_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1455_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1455_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
v___jp_1409_:
{
uint8_t v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = 0;
v___x_1416_ = 1;
v___x_1417_ = l_Lean_Meta_mkForallFVars(v_args2New_1396_, v_result_1410_, v___x_1415_, v___x_1408_, v___x_1408_, v___x_1416_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v___x_1419_ = l_Lean_Meta_mkForallFVars(v_args1_1393_, v_a_1418_, v___x_1415_, v___x_1408_, v___x_1408_, v___x_1416_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1421_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = l_Lean_Meta_mkForallFVars(v_params_1392_, v_a_1420_, v___x_1415_, v___x_1408_, v___x_1408_, v___x_1416_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1430_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1430_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1430_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_a_1422_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1426_);
v___x_1428_ = v___x_1424_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1421_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1421_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
v_a_1439_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1419_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1419_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
v_a_1447_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1417_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1417_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec_ref(v_args2_1395_);
v_a_1496_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1406_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1406_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1504_, lean_object* v_us_1505_, lean_object* v_params_1506_, lean_object* v_args1_1507_, lean_object* v_useEq_1508_, lean_object* v_args2_1509_, lean_object* v_args2New_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
uint8_t v_useEq_boxed_1516_; lean_object* v_res_1517_; 
v_useEq_boxed_1516_ = lean_unbox(v_useEq_1508_);
v_res_1517_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1504_, v_us_1505_, v_params_1506_, v_args1_1507_, v_useEq_boxed_1516_, v_args2_1509_, v_args2New_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec_ref(v_args2New_1510_);
lean_dec_ref(v_args1_1507_);
lean_dec_ref(v_params_1506_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1518_, size_t v_i_1519_, lean_object* v_bs_1520_){
_start:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_usize_dec_lt(v_i_1519_, v_sz_1518_);
if (v___x_1521_ == 0)
{
return v_bs_1520_;
}
else
{
lean_object* v_v_1522_; lean_object* v___x_1523_; lean_object* v_bs_x27_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; lean_object* v___x_1531_; 
v_v_1522_ = lean_array_uget(v_bs_1520_, v_i_1519_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v_bs_x27_1524_ = lean_array_uset(v_bs_1520_, v_i_1519_, v___x_1523_);
v___x_1525_ = l_Lean_Expr_fvarId_x21(v_v_1522_);
lean_dec(v_v_1522_);
v___x_1526_ = 1;
v___x_1527_ = lean_box(v___x_1526_);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1525_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = ((size_t)1ULL);
v___x_1530_ = lean_usize_add(v_i_1519_, v___x_1529_);
v___x_1531_ = lean_array_uset(v_bs_x27_1524_, v_i_1519_, v___x_1528_);
v_i_1519_ = v___x_1530_;
v_bs_1520_ = v___x_1531_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1533_, lean_object* v_i_1534_, lean_object* v_bs_1535_){
_start:
{
size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1533_);
lean_dec(v_sz_1533_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1534_);
lean_dec(v_i_1534_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1536_, v_i_boxed_1537_, v_bs_1535_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1539_, lean_object* v_k_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1539_, v_k_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
v_a_1555_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1546_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1546_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1563_, lean_object* v_k_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1563_, v_k_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec_ref(v_bs_1563_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1571_, lean_object* v_k_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
size_t v_sz_1578_; size_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_sz_1578_ = lean_array_size(v_bs_1571_);
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1578_, v___x_1579_, v_bs_1571_);
v___x_1581_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1580_, v_k_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec_ref(v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1582_, lean_object* v_k_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1582_, v_k_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1590_, lean_object* v_us_1591_, lean_object* v_params_1592_, uint8_t v_useEq_1593_, lean_object* v_ctorVal_1594_, lean_object* v_type_1595_, lean_object* v_args1_1596_, lean_object* v_resultType_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v___f_1604_; 
v___x_1603_ = lean_box(v_useEq_1593_);
lean_inc_ref(v_args1_1596_);
lean_inc_ref(v_params_1592_);
v___f_1604_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1604_, 0, v_name_1590_);
lean_closure_set(v___f_1604_, 1, v_us_1591_);
lean_closure_set(v___f_1604_, 2, v_params_1592_);
lean_closure_set(v___f_1604_, 3, v_args1_1596_);
lean_closure_set(v___f_1604_, 4, v___x_1603_);
if (v_useEq_1593_ == 0)
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1605_ = l_Array_append___redArg(v_params_1592_, v_args1_1596_);
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1608_ = lean_box(v_useEq_1593_);
v___x_1609_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1609_, 0, v_ctorVal_1594_);
lean_closure_set(v___x_1609_, 1, v___x_1608_);
lean_closure_set(v___x_1609_, 2, v_args1_1596_);
lean_closure_set(v___x_1609_, 3, v_resultType_1597_);
lean_closure_set(v___x_1609_, 4, v___f_1604_);
lean_closure_set(v___x_1609_, 5, v___x_1606_);
lean_closure_set(v___x_1609_, 6, v_type_1595_);
lean_closure_set(v___x_1609_, 7, v___x_1607_);
lean_closure_set(v___x_1609_, 8, v___x_1607_);
v___x_1610_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1605_, v___x_1609_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
lean_dec_ref(v_params_1592_);
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1613_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1594_, v_useEq_1593_, v_args1_1596_, v_resultType_1597_, v___f_1604_, v___x_1611_, v_type_1595_, v___x_1612_, v___x_1612_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1614_, lean_object* v_us_1615_, lean_object* v_params_1616_, lean_object* v_useEq_1617_, lean_object* v_ctorVal_1618_, lean_object* v_type_1619_, lean_object* v_args1_1620_, lean_object* v_resultType_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v_useEq_boxed_1627_; lean_object* v_res_1628_; 
v_useEq_boxed_1627_ = lean_unbox(v_useEq_1617_);
v_res_1628_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1614_, v_us_1615_, v_params_1616_, v_useEq_boxed_1627_, v_ctorVal_1618_, v_type_1619_, v_args1_1620_, v_resultType_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1629_, lean_object* v_us_1630_, uint8_t v_useEq_1631_, lean_object* v_ctorVal_1632_, lean_object* v_params_1633_, lean_object* v_type_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___f_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = lean_box(v_useEq_1631_);
lean_inc_ref(v_type_1634_);
v___f_1641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1641_, 0, v_name_1629_);
lean_closure_set(v___f_1641_, 1, v_us_1630_);
lean_closure_set(v___f_1641_, 2, v_params_1633_);
lean_closure_set(v___f_1641_, 3, v___x_1640_);
lean_closure_set(v___f_1641_, 4, v_ctorVal_1632_);
lean_closure_set(v___f_1641_, 5, v_type_1634_);
v___x_1642_ = 0;
v___x_1643_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1634_, v___f_1641_, v___x_1642_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1644_, lean_object* v_us_1645_, lean_object* v_useEq_1646_, lean_object* v_ctorVal_1647_, lean_object* v_params_1648_, lean_object* v_type_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
uint8_t v_useEq_boxed_1655_; lean_object* v_res_1656_; 
v_useEq_boxed_1655_ = lean_unbox(v_useEq_1646_);
v_res_1656_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1644_, v_us_1645_, v_useEq_boxed_1655_, v_ctorVal_1647_, v_params_1648_, v_type_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
if (lean_obj_tag(v_a_1657_) == 0)
{
lean_object* v___x_1659_; 
v___x_1659_ = l_List_reverse___redArg(v_a_1658_);
return v___x_1659_;
}
else
{
lean_object* v_head_1660_; lean_object* v_tail_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1670_; 
v_head_1660_ = lean_ctor_get(v_a_1657_, 0);
v_tail_1661_ = lean_ctor_get(v_a_1657_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_a_1657_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1663_ = v_a_1657_;
v_isShared_1664_ = v_isSharedCheck_1670_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_tail_1661_);
lean_inc(v_head_1660_);
lean_dec(v_a_1657_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1670_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = l_Lean_mkLevelParam(v_head_1660_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v_a_1658_);
lean_ctor_set(v___x_1663_, 0, v___x_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_a_1658_);
v___x_1667_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
v_a_1657_ = v_tail_1661_;
v_a_1658_ = v___x_1667_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1671_, uint8_t v_useEq_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_toConstantVal_1678_; lean_object* v_numParams_1679_; lean_object* v_name_1680_; lean_object* v_levelParams_1681_; lean_object* v_type_1682_; lean_object* v___x_1683_; 
v_toConstantVal_1678_ = lean_ctor_get(v_ctorVal_1671_, 0);
v_numParams_1679_ = lean_ctor_get(v_ctorVal_1671_, 3);
lean_inc(v_numParams_1679_);
v_name_1680_ = lean_ctor_get(v_toConstantVal_1678_, 0);
lean_inc(v_name_1680_);
v_levelParams_1681_ = lean_ctor_get(v_toConstantVal_1678_, 1);
v_type_1682_ = lean_ctor_get(v_toConstantVal_1678_, 2);
lean_inc(v_a_1676_);
lean_inc_ref(v_a_1675_);
lean_inc_ref(v_type_1682_);
v___x_1683_ = l_Lean_Meta_elimOptParam(v_type_1682_, v_a_1675_, v_a_1676_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; lean_object* v_us_1686_; lean_object* v___x_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; lean_object* v___x_1691_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = lean_box(0);
lean_inc(v_levelParams_1681_);
v_us_1686_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1681_, v___x_1685_);
v___x_1687_ = lean_box(v_useEq_1672_);
v___f_1688_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1688_, 0, v_name_1680_);
lean_closure_set(v___f_1688_, 1, v_us_1686_);
lean_closure_set(v___f_1688_, 2, v___x_1687_);
lean_closure_set(v___f_1688_, 3, v_ctorVal_1671_);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_numParams_1679_);
v___x_1690_ = 0;
v___x_1691_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1684_, v___x_1689_, v___f_1688_, v___x_1690_, v___x_1690_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v___x_1691_;
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_name_1680_);
lean_dec(v_numParams_1679_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec_ref(v_ctorVal_1671_);
v_a_1692_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1683_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1683_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1700_, lean_object* v_useEq_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
uint8_t v_useEq_boxed_1707_; lean_object* v_res_1708_; 
v_useEq_boxed_1707_ = lean_unbox(v_useEq_1701_);
v_res_1708_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1700_, v_useEq_boxed_1707_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1709_, lean_object* v_bs_1710_, lean_object* v_k_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1710_, v_k_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1718_, lean_object* v_bs_1719_, lean_object* v_k_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1718_, v_bs_1719_, v_k_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v_bs_1719_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1727_, lean_object* v_bs_1728_, lean_object* v_k_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1728_, v_k_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1736_, lean_object* v_bs_1737_, lean_object* v_k_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1736_, v_bs_1737_, v_k_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
uint8_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = 0;
v___x_1752_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1745_, v___x_1751_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
return v_res_1759_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1765_ = l_Lean_stringToMessageData(v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1766_){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1767_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1768_ = l_Lean_MessageData_ofName(v_ctorName_1766_);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1772_, lean_object* v_mvarId_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1779_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1772_);
v___x_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_mvarId_1773_);
v___x_1781_ = l_Lean_indentD(v___x_1780_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1779_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1782_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1784_, lean_object* v_mvarId_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1784_, v_mvarId_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1792_, lean_object* v_ctorName_1793_, lean_object* v_mvarId_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1793_, v_mvarId_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_ctorName_1802_, lean_object* v_mvarId_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1801_, v_ctorName_1802_, v_mvarId_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1810_, lean_object* v_as_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
if (lean_obj_tag(v_as_1811_) == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v_ctorName_1810_);
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
else
{
lean_object* v_head_1819_; lean_object* v_tail_1820_; lean_object* v___x_1821_; 
v_head_1819_ = lean_ctor_get(v_as_1811_, 0);
lean_inc(v_head_1819_);
v_tail_1820_ = lean_ctor_get(v_as_1811_, 1);
lean_inc(v_tail_1820_);
lean_dec_ref(v_as_1811_);
lean_inc(v___y_1815_);
lean_inc_ref(v___y_1814_);
lean_inc(v___y_1813_);
lean_inc_ref(v___y_1812_);
lean_inc(v_head_1819_);
v___x_1821_ = l_Lean_MVarId_assumptionCore(v_head_1819_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; uint8_t v___x_1823_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1821_);
v___x_1823_ = lean_unbox(v_a_1822_);
lean_dec(v_a_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_dec(v_tail_1820_);
v___x_1824_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1810_, v_head_1819_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v___x_1824_;
}
else
{
lean_dec(v_head_1819_);
v_as_1811_ = v_tail_1820_;
goto _start;
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_tail_1820_);
lean_dec(v_head_1819_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v_ctorName_1810_);
v_a_1826_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1821_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1821_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1834_, lean_object* v_as_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1834_, v_as_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1842_, lean_object* v_ctorName_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v___x_1849_; 
lean_inc(v_a_1847_);
lean_inc_ref(v_a_1846_);
lean_inc(v_a_1845_);
lean_inc_ref(v_a_1844_);
v___x_1849_ = l_Lean_MVarId_splitAndCore(v_mvarId_1842_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref(v___x_1849_);
v___x_1851_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1843_, v_a_1850_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
return v___x_1851_;
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_ctorName_1843_);
v_a_1852_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1849_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1849_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1860_, lean_object* v_ctorName_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1860_, v_ctorName_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___f_1875_; lean_object* v___x_563__overap_1876_; lean_object* v___x_1877_; 
v___f_1875_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_563__overap_1876_ = lean_panic_fn(v___f_1875_, v_msg_1869_);
v___x_1877_ = lean_apply_5(v___x_563__overap_1876_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, lean_box(0));
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(lean_object* v_cls_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_options_1891_; uint8_t v_hasTrace_1892_; 
v_options_1891_ = lean_ctor_get(v___y_1889_, 2);
v_hasTrace_1892_ = lean_ctor_get_uint8(v_options_1891_, sizeof(void*)*1);
if (v_hasTrace_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec(v_cls_1888_);
v___x_1893_ = lean_box(v_hasTrace_1892_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
else
{
lean_object* v_inheritedTraceOptions_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_inheritedTraceOptions_1895_ = lean_ctor_get(v___y_1889_, 13);
v___x_1896_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___closed__1));
v___x_1897_ = l_Lean_Name_append(v___x_1896_, v_cls_1888_);
v___x_1898_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1895_, v_options_1891_, v___x_1897_);
lean_dec(v___x_1897_);
v___x_1899_ = lean_box(v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___boxed(lean_object* v_cls_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_1901_, v___y_1902_);
lean_dec_ref(v___y_1902_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_1905_, v___y_1908_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
return v_res_1918_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1919_; double v___x_1920_; 
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = lean_float_of_nat(v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(lean_object* v_cls_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_ref_1931_; lean_object* v___x_1932_; lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1977_; 
v_ref_1931_ = lean_ctor_get(v___y_1928_, 5);
v___x_1932_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1977_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1977_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v_traceState_1938_; lean_object* v_env_1939_; lean_object* v_nextMacroScope_1940_; lean_object* v_ngen_1941_; lean_object* v_auxDeclNGen_1942_; lean_object* v_cache_1943_; lean_object* v_messages_1944_; lean_object* v_infoState_1945_; lean_object* v_snapshotTasks_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1976_; 
v___x_1937_ = lean_st_ref_take(v___y_1929_);
v_traceState_1938_ = lean_ctor_get(v___x_1937_, 4);
v_env_1939_ = lean_ctor_get(v___x_1937_, 0);
v_nextMacroScope_1940_ = lean_ctor_get(v___x_1937_, 1);
v_ngen_1941_ = lean_ctor_get(v___x_1937_, 2);
v_auxDeclNGen_1942_ = lean_ctor_get(v___x_1937_, 3);
v_cache_1943_ = lean_ctor_get(v___x_1937_, 5);
v_messages_1944_ = lean_ctor_get(v___x_1937_, 6);
v_infoState_1945_ = lean_ctor_get(v___x_1937_, 7);
v_snapshotTasks_1946_ = lean_ctor_get(v___x_1937_, 8);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1948_ = v___x_1937_;
v_isShared_1949_ = v_isSharedCheck_1976_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_snapshotTasks_1946_);
lean_inc(v_infoState_1945_);
lean_inc(v_messages_1944_);
lean_inc(v_cache_1943_);
lean_inc(v_traceState_1938_);
lean_inc(v_auxDeclNGen_1942_);
lean_inc(v_ngen_1941_);
lean_inc(v_nextMacroScope_1940_);
lean_inc(v_env_1939_);
lean_dec(v___x_1937_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1976_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
uint64_t v_tid_1950_; lean_object* v_traces_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1975_; 
v_tid_1950_ = lean_ctor_get_uint64(v_traceState_1938_, sizeof(void*)*1);
v_traces_1951_ = lean_ctor_get(v_traceState_1938_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_traceState_1938_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1953_ = v_traceState_1938_;
v_isShared_1954_ = v_isSharedCheck_1975_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_traces_1951_);
lean_dec(v_traceState_1938_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1975_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; double v___x_1956_; uint8_t v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0);
v___x_1957_ = 0;
v___x_1958_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1));
v___x_1959_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1959_, 0, v_cls_1924_);
lean_ctor_set(v___x_1959_, 1, v___x_1955_);
lean_ctor_set(v___x_1959_, 2, v___x_1958_);
lean_ctor_set_float(v___x_1959_, sizeof(void*)*3, v___x_1956_);
lean_ctor_set_float(v___x_1959_, sizeof(void*)*3 + 8, v___x_1956_);
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*3 + 16, v___x_1957_);
v___x_1960_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__2));
v___x_1961_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set(v___x_1961_, 1, v_a_1933_);
lean_ctor_set(v___x_1961_, 2, v___x_1960_);
lean_inc(v_ref_1931_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_ref_1931_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = l_Lean_PersistentArray_push___redArg(v_traces_1951_, v___x_1962_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1963_);
v___x_1965_ = v___x_1953_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1963_);
lean_ctor_set_uint64(v_reuseFailAlloc_1974_, sizeof(void*)*1, v_tid_1950_);
v___x_1965_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1967_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 4, v___x_1965_);
v___x_1967_ = v___x_1948_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_env_1939_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_nextMacroScope_1940_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_ngen_1941_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_auxDeclNGen_1942_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1973_, 5, v_cache_1943_);
lean_ctor_set(v_reuseFailAlloc_1973_, 6, v_messages_1944_);
lean_ctor_set(v_reuseFailAlloc_1973_, 7, v_infoState_1945_);
lean_ctor_set(v_reuseFailAlloc_1973_, 8, v_snapshotTasks_1946_);
v___x_1967_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1968_ = lean_st_ref_set(v___y_1929_, v___x_1967_);
v___x_1969_ = lean_box(0);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1969_);
v___x_1971_ = v___x_1935_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___boxed(lean_object* v_cls_1978_, lean_object* v_msg_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_1978_, v_msg_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1985_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1990_ = lean_unsigned_to_nat(30u);
v___x_1991_ = lean_unsigned_to_nat(96u);
v___x_1992_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1993_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1994_ = l_mkPanicMessageWithDecl(v___x_1993_, v___x_1992_, v___x_1991_, v___x_1990_, v___x_1989_);
return v___x_1994_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7));
v___x_2002_ = l_Lean_stringToMessageData(v___x_2001_);
return v___x_2002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9));
v___x_2005_ = l_Lean_stringToMessageData(v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11));
v___x_2008_ = l_Lean_stringToMessageData(v___x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2009_, lean_object* v_mvarId_2010_, lean_object* v_h_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v_cls_2037_; lean_object* v___x_2038_; lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2059_; 
v_cls_2037_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2038_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2037_, v_a_2014_);
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2059_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2059_;
goto v_resetjp_2040_;
}
v___jp_2017_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_box(0);
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
v___x_2023_ = l_Lean_Meta_injection(v_mvarId_2010_, v_h_2011_, v___x_2022_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref(v___x_2023_);
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
lean_dec_ref(v_a_2024_);
v___x_2028_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2027_, v_ctorName_2009_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2028_;
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
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
v_resetjp_2040_:
{
uint8_t v___x_2043_; 
v___x_2043_ = lean_unbox(v_a_2039_);
lean_dec(v_a_2039_);
if (v___x_2043_ == 0)
{
lean_del_object(v___x_2041_);
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
v___y_2020_ = v_a_2014_;
v___y_2021_ = v_a_2015_;
goto v___jp_2017_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2044_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8);
lean_inc(v_ctorName_2009_);
v___x_2045_ = l_Lean_MessageData_ofName(v_ctorName_2009_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_inc(v_h_2011_);
v___x_2049_ = l_Lean_mkFVar(v_h_2011_);
v___x_2050_ = l_Lean_MessageData_ofExpr(v___x_2049_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2048_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
lean_inc(v_mvarId_2010_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 1);
lean_ctor_set(v___x_2041_, 0, v_mvarId_2010_);
v___x_2055_ = v___x_2041_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_mvarId_2010_);
v___x_2055_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2053_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2037_, v___x_2056_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref(v___x_2057_);
v___y_2018_ = v_a_2012_;
v___y_2019_ = v_a_2013_;
v___y_2020_ = v_a_2014_;
v___y_2021_ = v_a_2015_;
goto v___jp_2017_;
}
else
{
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_h_2011_);
lean_dec(v_mvarId_2010_);
lean_dec(v_ctorName_2009_);
return v___x_2057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2060_, lean_object* v_mvarId_2061_, lean_object* v_h_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2060_, v_mvarId_2061_, v_h_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2069_, lean_object* v_k_2070_, uint8_t v_cleanupAnnotations_2071_, uint8_t v_whnfType_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___f_2078_; lean_object* v___x_2079_; 
v___f_2078_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2078_, 0, v_k_2070_);
v___x_2079_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2069_, v___f_2078_, v_cleanupAnnotations_2071_, v_whnfType_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v_a_2088_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2079_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2079_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2096_, lean_object* v_k_2097_, lean_object* v_cleanupAnnotations_2098_, lean_object* v_whnfType_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2105_; uint8_t v_whnfType_boxed_2106_; lean_object* v_res_2107_; 
v_cleanupAnnotations_boxed_2105_ = lean_unbox(v_cleanupAnnotations_2098_);
v_whnfType_boxed_2106_ = lean_unbox(v_whnfType_2099_);
v_res_2107_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2096_, v_k_2097_, v_cleanupAnnotations_boxed_2105_, v_whnfType_boxed_2106_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2108_, lean_object* v_type_2109_, lean_object* v_k_2110_, uint8_t v_cleanupAnnotations_2111_, uint8_t v_whnfType_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2109_, v_k_2110_, v_cleanupAnnotations_2111_, v_whnfType_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2119_, lean_object* v_type_2120_, lean_object* v_k_2121_, lean_object* v_cleanupAnnotations_2122_, lean_object* v_whnfType_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2129_; uint8_t v_whnfType_boxed_2130_; lean_object* v_res_2131_; 
v_cleanupAnnotations_boxed_2129_ = lean_unbox(v_cleanupAnnotations_2122_);
v_whnfType_boxed_2130_ = lean_unbox(v_whnfType_2123_);
v_res_2131_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2119_, v_type_2120_, v_k_2121_, v_cleanupAnnotations_boxed_2129_, v_whnfType_boxed_2130_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2132_, lean_object* v_ctorName_2133_, lean_object* v_xs_2134_, lean_object* v_type_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_box(0);
lean_inc_ref(v___y_2136_);
v___x_2142_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2135_, v___x_2141_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref(v___x_2142_);
v___x_2144_ = l_Lean_Expr_mvarId_x21(v_a_2143_);
v___x_2145_ = lean_array_get_size(v_xs_2134_);
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_sub(v___x_2145_, v___x_2146_);
v___x_2148_ = lean_array_get_borrowed(v___x_2132_, v_xs_2134_, v___x_2147_);
lean_dec(v___x_2147_);
v___x_2149_ = l_Lean_Expr_fvarId_x21(v___x_2148_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2137_);
lean_inc_ref(v___y_2136_);
v___x_2150_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2133_, v___x_2144_, v___x_2149_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
if (lean_obj_tag(v___x_2150_) == 0)
{
uint8_t v___x_2151_; uint8_t v___x_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v___x_2150_);
v___x_2151_ = 0;
v___x_2152_ = 1;
v___x_2153_ = 1;
v___x_2154_ = l_Lean_Meta_mkLambdaFVars(v_xs_2134_, v_a_2143_, v___x_2151_, v___x_2152_, v___x_2151_, v___x_2152_, v___x_2153_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v___x_2154_;
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_a_2143_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
v_a_2155_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2150_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2150_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v_ctorName_2133_);
lean_dec_ref(v___x_2132_);
return v___x_2142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2163_, lean_object* v_ctorName_2164_, lean_object* v_xs_2165_, lean_object* v_type_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2163_, v_ctorName_2164_, v_xs_2165_, v_type_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec_ref(v_xs_2165_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2173_, lean_object* v_targetType_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v___x_2180_; lean_object* v___f_2181_; uint8_t v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = l_Lean_instInhabitedExpr;
v___f_2181_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2181_, 0, v___x_2180_);
lean_closure_set(v___f_2181_, 1, v_ctorName_2173_);
v___x_2182_ = 0;
v___x_2183_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2174_, v___f_2181_, v___x_2182_, v___x_2182_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2184_, lean_object* v_targetType_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2184_, v_targetType_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2195_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2197_ = l_Lean_Name_append(v_ctorName_2195_, v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lean_Expr_hasMVar(v_e_2198_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v_e_2198_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v_mctx_2204_; lean_object* v___x_2205_; lean_object* v_fst_2206_; lean_object* v_snd_2207_; lean_object* v___x_2208_; lean_object* v_cache_2209_; lean_object* v_zetaDeltaFVarIds_2210_; lean_object* v_postponed_2211_; lean_object* v_diag_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2221_; 
v___x_2203_ = lean_st_ref_get(v___y_2199_);
v_mctx_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc_ref(v_mctx_2204_);
lean_dec(v___x_2203_);
v___x_2205_ = l_Lean_instantiateMVarsCore(v_mctx_2204_, v_e_2198_);
v_fst_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_fst_2206_);
v_snd_2207_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_snd_2207_);
lean_dec_ref(v___x_2205_);
v___x_2208_ = lean_st_ref_take(v___y_2199_);
v_cache_2209_ = lean_ctor_get(v___x_2208_, 1);
v_zetaDeltaFVarIds_2210_ = lean_ctor_get(v___x_2208_, 2);
v_postponed_2211_ = lean_ctor_get(v___x_2208_, 3);
v_diag_2212_ = lean_ctor_get(v___x_2208_, 4);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; 
v_unused_2222_ = lean_ctor_get(v___x_2208_, 0);
lean_dec(v_unused_2222_);
v___x_2214_ = v___x_2208_;
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_diag_2212_);
lean_inc(v_postponed_2211_);
lean_inc(v_zetaDeltaFVarIds_2210_);
lean_inc(v_cache_2209_);
lean_dec(v___x_2208_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v_snd_2207_);
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_snd_2207_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_cache_2209_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_zetaDeltaFVarIds_2210_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v_postponed_2211_);
lean_ctor_set(v_reuseFailAlloc_2220_, 4, v_diag_2212_);
v___x_2217_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_st_ref_set(v___y_2199_, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_fst_2206_);
return v___x_2219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2223_, v___y_2224_);
lean_dec(v___y_2224_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2227_, v___y_2229_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2240_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_unsigned_to_nat(32u);
v___x_2242_ = lean_mk_empty_array_with_capacity(v___x_2241_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
return v___x_2243_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2244_ = ((size_t)5ULL);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_unsigned_to_nat(32u);
v___x_2247_ = lean_mk_empty_array_with_capacity(v___x_2246_);
v___x_2248_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2249_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___x_2247_);
lean_ctor_set(v___x_2249_, 2, v___x_2245_);
lean_ctor_set(v___x_2249_, 3, v___x_2245_);
lean_ctor_set_usize(v___x_2249_, 4, v___x_2244_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v_traceState_2253_; lean_object* v_traces_2254_; lean_object* v___x_2255_; lean_object* v_traceState_2256_; lean_object* v_env_2257_; lean_object* v_nextMacroScope_2258_; lean_object* v_ngen_2259_; lean_object* v_auxDeclNGen_2260_; lean_object* v_cache_2261_; lean_object* v_messages_2262_; lean_object* v_infoState_2263_; lean_object* v_snapshotTasks_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2283_; 
v___x_2252_ = lean_st_ref_get(v___y_2250_);
v_traceState_2253_ = lean_ctor_get(v___x_2252_, 4);
lean_inc_ref(v_traceState_2253_);
lean_dec(v___x_2252_);
v_traces_2254_ = lean_ctor_get(v_traceState_2253_, 0);
lean_inc_ref(v_traces_2254_);
lean_dec_ref(v_traceState_2253_);
v___x_2255_ = lean_st_ref_take(v___y_2250_);
v_traceState_2256_ = lean_ctor_get(v___x_2255_, 4);
v_env_2257_ = lean_ctor_get(v___x_2255_, 0);
v_nextMacroScope_2258_ = lean_ctor_get(v___x_2255_, 1);
v_ngen_2259_ = lean_ctor_get(v___x_2255_, 2);
v_auxDeclNGen_2260_ = lean_ctor_get(v___x_2255_, 3);
v_cache_2261_ = lean_ctor_get(v___x_2255_, 5);
v_messages_2262_ = lean_ctor_get(v___x_2255_, 6);
v_infoState_2263_ = lean_ctor_get(v___x_2255_, 7);
v_snapshotTasks_2264_ = lean_ctor_get(v___x_2255_, 8);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2266_ = v___x_2255_;
v_isShared_2267_ = v_isSharedCheck_2283_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_snapshotTasks_2264_);
lean_inc(v_infoState_2263_);
lean_inc(v_messages_2262_);
lean_inc(v_cache_2261_);
lean_inc(v_traceState_2256_);
lean_inc(v_auxDeclNGen_2260_);
lean_inc(v_ngen_2259_);
lean_inc(v_nextMacroScope_2258_);
lean_inc(v_env_2257_);
lean_dec(v___x_2255_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2283_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
uint64_t v_tid_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2281_; 
v_tid_2268_ = lean_ctor_get_uint64(v_traceState_2256_, sizeof(void*)*1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_traceState_2256_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; 
v_unused_2282_ = lean_ctor_get(v_traceState_2256_, 0);
lean_dec(v_unused_2282_);
v___x_2270_ = v_traceState_2256_;
v_isShared_2271_ = v_isSharedCheck_2281_;
goto v_resetjp_2269_;
}
else
{
lean_dec(v_traceState_2256_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2281_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2272_);
v___x_2274_ = v___x_2270_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2272_);
lean_ctor_set_uint64(v_reuseFailAlloc_2280_, sizeof(void*)*1, v_tid_2268_);
v___x_2274_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2276_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v___x_2274_);
v___x_2276_ = v___x_2266_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_env_2257_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_nextMacroScope_2258_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_ngen_2259_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_auxDeclNGen_2260_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2279_, 5, v_cache_2261_);
lean_ctor_set(v_reuseFailAlloc_2279_, 6, v_messages_2262_);
lean_ctor_set(v_reuseFailAlloc_2279_, 7, v_infoState_2263_);
lean_ctor_set(v_reuseFailAlloc_2279_, 8, v_snapshotTasks_2264_);
v___x_2276_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_st_ref_set(v___y_2250_, v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v_traces_2254_);
return v___x_2278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2284_);
lean_dec(v___y_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2298_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2299_, lean_object* v_opt_2300_){
_start:
{
lean_object* v_name_2301_; lean_object* v_defValue_2302_; lean_object* v_map_2303_; lean_object* v___x_2304_; 
v_name_2301_ = lean_ctor_get(v_opt_2300_, 0);
v_defValue_2302_ = lean_ctor_get(v_opt_2300_, 1);
v_map_2303_ = lean_ctor_get(v_opts_2299_, 0);
v___x_2304_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2303_, v_name_2301_);
if (lean_obj_tag(v___x_2304_) == 0)
{
uint8_t v___x_2305_; 
v___x_2305_ = lean_unbox(v_defValue_2302_);
return v___x_2305_;
}
else
{
lean_object* v_val_2306_; 
v_val_2306_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_val_2306_);
lean_dec_ref(v___x_2304_);
if (lean_obj_tag(v_val_2306_) == 1)
{
uint8_t v_v_2307_; 
v_v_2307_ = lean_ctor_get_uint8(v_val_2306_, 0);
lean_dec_ref(v_val_2306_);
return v_v_2307_;
}
else
{
uint8_t v___x_2308_; 
lean_dec(v_val_2306_);
v___x_2308_ = lean_unbox(v_defValue_2302_);
return v___x_2308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2309_, lean_object* v_opt_2310_){
_start:
{
uint8_t v_res_2311_; lean_object* v_r_2312_; 
v_res_2311_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2309_, v_opt_2310_);
lean_dec_ref(v_opt_2310_);
lean_dec_ref(v_opts_2309_);
v_r_2312_ = lean_box(v_res_2311_);
return v_r_2312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2315_ = l_Lean_stringToMessageData(v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2316_, lean_object* v_x_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2323_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2324_ = l_Lean_MessageData_ofName(v_name_2316_);
v___x_2325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2323_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2329_, lean_object* v_x_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2329_, v_x_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v_x_2330_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2337_, lean_object* v_val_2338_, lean_object* v_name_2339_, lean_object* v_levelParams_2340_, uint8_t v___x_2341_, lean_object* v_____r_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; 
lean_inc(v___y_2346_);
lean_inc_ref(v___y_2345_);
lean_inc(v___y_2344_);
lean_inc_ref(v_val_2338_);
v___x_2348_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2337_, v_val_2338_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; lean_object* v_a_2351_; lean_object* v___x_2352_; lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2365_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref(v___x_2348_);
v___x_2350_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2338_, v___y_2344_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
v___x_2352_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2349_, v___y_2344_);
lean_dec(v___y_2344_);
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_inc(v_name_2339_);
v___x_2357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2357_, 0, v_name_2339_);
lean_ctor_set(v___x_2357_, 1, v_levelParams_2340_);
lean_ctor_set(v___x_2357_, 2, v_a_2351_);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2359_, 0, v_name_2339_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2357_);
lean_ctor_set(v___x_2360_, 1, v_a_2353_);
lean_ctor_set(v___x_2360_, 2, v___x_2359_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 2);
lean_ctor_set(v___x_2355_, 0, v___x_2360_);
v___x_2362_ = v___x_2355_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_addDecl(v___x_2362_, v___x_2341_, v___y_2345_, v___y_2346_);
return v___x_2363_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec(v_levelParams_2340_);
lean_dec(v_name_2339_);
lean_dec_ref(v_val_2338_);
v_a_2366_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2348_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2348_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2374_, lean_object* v_val_2375_, lean_object* v_name_2376_, lean_object* v_levelParams_2377_, lean_object* v___x_2378_, lean_object* v_____r_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
uint8_t v___x_10731__boxed_2385_; lean_object* v_res_2386_; 
v___x_10731__boxed_2385_ = lean_unbox(v___x_2378_);
v_res_2386_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2374_, v_val_2375_, v_name_2376_, v_levelParams_2377_, v___x_10731__boxed_2385_, v_____r_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2387_, lean_object* v_val_2388_, lean_object* v_name_2389_, lean_object* v_levelParams_2390_, lean_object* v_____r_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; 
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
lean_inc(v___y_2393_);
lean_inc_ref(v_val_2388_);
v___x_2397_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2387_, v_val_2388_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2399_; lean_object* v_a_2400_; lean_object* v___x_2401_; lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2415_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref(v___x_2397_);
v___x_2399_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2388_, v___y_2393_);
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref(v___x_2399_);
v___x_2401_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2398_, v___y_2393_);
lean_dec(v___y_2393_);
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2415_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2415_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
lean_inc(v_name_2389_);
v___x_2406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2406_, 0, v_name_2389_);
lean_ctor_set(v___x_2406_, 1, v_levelParams_2390_);
lean_ctor_set(v___x_2406_, 2, v_a_2400_);
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2408_, 0, v_name_2389_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2406_);
lean_ctor_set(v___x_2409_, 1, v_a_2402_);
lean_ctor_set(v___x_2409_, 2, v___x_2408_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 2);
lean_ctor_set(v___x_2404_, 0, v___x_2409_);
v___x_2411_ = v___x_2404_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
uint8_t v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = 0;
v___x_2413_ = l_Lean_addDecl(v___x_2411_, v___x_2412_, v___y_2394_, v___y_2395_);
return v___x_2413_;
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec(v_levelParams_2390_);
lean_dec(v_name_2389_);
lean_dec_ref(v_val_2388_);
v_a_2416_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2397_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2397_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2424_, lean_object* v_val_2425_, lean_object* v_name_2426_, lean_object* v_levelParams_2427_, lean_object* v_____r_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2424_, v_val_2425_, v_name_2426_, v_levelParams_2427_, v_____r_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
return v_res_2434_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_e_2435_){
_start:
{
if (lean_obj_tag(v_e_2435_) == 0)
{
uint8_t v___x_2436_; 
v___x_2436_ = 2;
return v___x_2436_;
}
else
{
uint8_t v___x_2437_; 
v___x_2437_ = 0;
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_e_2438_){
_start:
{
uint8_t v_res_2439_; lean_object* v_r_2440_; 
v_res_2439_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_e_2438_);
lean_dec_ref(v_e_2438_);
v_r_2440_ = lean_box(v_res_2439_);
return v_r_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2441_, lean_object* v_opt_2442_){
_start:
{
lean_object* v_name_2443_; lean_object* v_defValue_2444_; lean_object* v_map_2445_; lean_object* v___x_2446_; 
v_name_2443_ = lean_ctor_get(v_opt_2442_, 0);
v_defValue_2444_ = lean_ctor_get(v_opt_2442_, 1);
v_map_2445_ = lean_ctor_get(v_opts_2441_, 0);
v___x_2446_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2445_, v_name_2443_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_inc(v_defValue_2444_);
return v_defValue_2444_;
}
else
{
lean_object* v_val_2447_; 
v_val_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_val_2447_);
lean_dec_ref(v___x_2446_);
if (lean_obj_tag(v_val_2447_) == 3)
{
lean_object* v_v_2448_; 
v_v_2448_ = lean_ctor_get(v_val_2447_, 0);
lean_inc(v_v_2448_);
lean_dec_ref(v_val_2447_);
return v_v_2448_;
}
else
{
lean_dec(v_val_2447_);
lean_inc(v_defValue_2444_);
return v_defValue_2444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2449_, lean_object* v_opt_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2449_, v_opt_2450_);
lean_dec_ref(v_opt_2450_);
lean_dec_ref(v_opts_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(lean_object* v_x_2452_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
v_a_2454_ = lean_ctor_get(v_x_2452_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_x_2452_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v_x_2452_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v_x_2452_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
lean_ctor_set_tag(v___x_2456_, 1);
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v_a_2462_ = lean_ctor_get(v_x_2452_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_x_2452_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v_x_2452_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v_x_2452_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 0);
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg___boxed(lean_object* v_x_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2470_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(size_t v_sz_2473_, size_t v_i_2474_, lean_object* v_bs_2475_){
_start:
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_usize_dec_lt(v_i_2474_, v_sz_2473_);
if (v___x_2476_ == 0)
{
return v_bs_2475_;
}
else
{
lean_object* v_v_2477_; lean_object* v_msg_2478_; lean_object* v___x_2479_; lean_object* v_bs_x27_2480_; size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v_v_2477_ = lean_array_uget_borrowed(v_bs_2475_, v_i_2474_);
v_msg_2478_ = lean_ctor_get(v_v_2477_, 1);
lean_inc_ref(v_msg_2478_);
v___x_2479_ = lean_unsigned_to_nat(0u);
v_bs_x27_2480_ = lean_array_uset(v_bs_2475_, v_i_2474_, v___x_2479_);
v___x_2481_ = ((size_t)1ULL);
v___x_2482_ = lean_usize_add(v_i_2474_, v___x_2481_);
v___x_2483_ = lean_array_uset(v_bs_x27_2480_, v_i_2474_, v_msg_2478_);
v_i_2474_ = v___x_2482_;
v_bs_2475_ = v___x_2483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2485_, lean_object* v_i_2486_, lean_object* v_bs_2487_){
_start:
{
size_t v_sz_boxed_2488_; size_t v_i_boxed_2489_; lean_object* v_res_2490_; 
v_sz_boxed_2488_ = lean_unbox_usize(v_sz_2485_);
lean_dec(v_sz_2485_);
v_i_boxed_2489_ = lean_unbox_usize(v_i_2486_);
lean_dec(v_i_2486_);
v_res_2490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_boxed_2488_, v_i_boxed_2489_, v_bs_2487_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_oldTraces_2491_, lean_object* v_data_2492_, lean_object* v_ref_2493_, lean_object* v_msg_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_fileName_2500_; lean_object* v_fileMap_2501_; lean_object* v_options_2502_; lean_object* v_currRecDepth_2503_; lean_object* v_maxRecDepth_2504_; lean_object* v_ref_2505_; lean_object* v_currNamespace_2506_; lean_object* v_openDecls_2507_; lean_object* v_initHeartbeats_2508_; lean_object* v_maxHeartbeats_2509_; lean_object* v_quotContext_2510_; lean_object* v_currMacroScope_2511_; uint8_t v_diag_2512_; lean_object* v_cancelTk_x3f_2513_; uint8_t v_suppressElabErrors_2514_; lean_object* v_inheritedTraceOptions_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2570_; 
v_fileName_2500_ = lean_ctor_get(v___y_2497_, 0);
v_fileMap_2501_ = lean_ctor_get(v___y_2497_, 1);
v_options_2502_ = lean_ctor_get(v___y_2497_, 2);
v_currRecDepth_2503_ = lean_ctor_get(v___y_2497_, 3);
v_maxRecDepth_2504_ = lean_ctor_get(v___y_2497_, 4);
v_ref_2505_ = lean_ctor_get(v___y_2497_, 5);
v_currNamespace_2506_ = lean_ctor_get(v___y_2497_, 6);
v_openDecls_2507_ = lean_ctor_get(v___y_2497_, 7);
v_initHeartbeats_2508_ = lean_ctor_get(v___y_2497_, 8);
v_maxHeartbeats_2509_ = lean_ctor_get(v___y_2497_, 9);
v_quotContext_2510_ = lean_ctor_get(v___y_2497_, 10);
v_currMacroScope_2511_ = lean_ctor_get(v___y_2497_, 11);
v_diag_2512_ = lean_ctor_get_uint8(v___y_2497_, sizeof(void*)*14);
v_cancelTk_x3f_2513_ = lean_ctor_get(v___y_2497_, 12);
v_suppressElabErrors_2514_ = lean_ctor_get_uint8(v___y_2497_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2515_ = lean_ctor_get(v___y_2497_, 13);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___y_2497_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2517_ = v___y_2497_;
v_isShared_2518_ = v_isSharedCheck_2570_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_inheritedTraceOptions_2515_);
lean_inc(v_cancelTk_x3f_2513_);
lean_inc(v_currMacroScope_2511_);
lean_inc(v_quotContext_2510_);
lean_inc(v_maxHeartbeats_2509_);
lean_inc(v_initHeartbeats_2508_);
lean_inc(v_openDecls_2507_);
lean_inc(v_currNamespace_2506_);
lean_inc(v_ref_2505_);
lean_inc(v_maxRecDepth_2504_);
lean_inc(v_currRecDepth_2503_);
lean_inc(v_options_2502_);
lean_inc(v_fileMap_2501_);
lean_inc(v_fileName_2500_);
lean_dec(v___y_2497_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2570_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v_traceState_2520_; lean_object* v_traces_2521_; lean_object* v_ref_2522_; lean_object* v___x_2524_; 
v___x_2519_ = lean_st_ref_get(v___y_2498_);
v_traceState_2520_ = lean_ctor_get(v___x_2519_, 4);
lean_inc_ref(v_traceState_2520_);
lean_dec(v___x_2519_);
v_traces_2521_ = lean_ctor_get(v_traceState_2520_, 0);
lean_inc_ref(v_traces_2521_);
lean_dec_ref(v_traceState_2520_);
v_ref_2522_ = l_Lean_replaceRef(v_ref_2493_, v_ref_2505_);
lean_dec(v_ref_2505_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 5, v_ref_2522_);
v___x_2524_ = v___x_2517_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_fileName_2500_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_fileMap_2501_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_options_2502_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v_currRecDepth_2503_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v_maxRecDepth_2504_);
lean_ctor_set(v_reuseFailAlloc_2569_, 5, v_ref_2522_);
lean_ctor_set(v_reuseFailAlloc_2569_, 6, v_currNamespace_2506_);
lean_ctor_set(v_reuseFailAlloc_2569_, 7, v_openDecls_2507_);
lean_ctor_set(v_reuseFailAlloc_2569_, 8, v_initHeartbeats_2508_);
lean_ctor_set(v_reuseFailAlloc_2569_, 9, v_maxHeartbeats_2509_);
lean_ctor_set(v_reuseFailAlloc_2569_, 10, v_quotContext_2510_);
lean_ctor_set(v_reuseFailAlloc_2569_, 11, v_currMacroScope_2511_);
lean_ctor_set(v_reuseFailAlloc_2569_, 12, v_cancelTk_x3f_2513_);
lean_ctor_set(v_reuseFailAlloc_2569_, 13, v_inheritedTraceOptions_2515_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*14, v_diag_2512_);
lean_ctor_set_uint8(v_reuseFailAlloc_2569_, sizeof(void*)*14 + 1, v_suppressElabErrors_2514_);
v___x_2524_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; size_t v_sz_2526_; size_t v___x_2527_; lean_object* v___x_2528_; lean_object* v_msg_2529_; lean_object* v___x_2530_; lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2568_; 
v___x_2525_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2521_);
lean_dec_ref(v_traces_2521_);
v_sz_2526_ = lean_array_size(v___x_2525_);
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_2526_, v___x_2527_, v___x_2525_);
v_msg_2529_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2529_, 0, v_data_2492_);
lean_ctor_set(v_msg_2529_, 1, v_msg_2494_);
lean_ctor_set(v_msg_2529_, 2, v___x_2528_);
v___x_2530_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2529_, v___y_2495_, v___y_2496_, v___x_2524_, v___y_2498_);
lean_dec_ref(v___x_2524_);
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2568_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2568_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v_traceState_2536_; lean_object* v_env_2537_; lean_object* v_nextMacroScope_2538_; lean_object* v_ngen_2539_; lean_object* v_auxDeclNGen_2540_; lean_object* v_cache_2541_; lean_object* v_messages_2542_; lean_object* v_infoState_2543_; lean_object* v_snapshotTasks_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2567_; 
v___x_2535_ = lean_st_ref_take(v___y_2498_);
v_traceState_2536_ = lean_ctor_get(v___x_2535_, 4);
v_env_2537_ = lean_ctor_get(v___x_2535_, 0);
v_nextMacroScope_2538_ = lean_ctor_get(v___x_2535_, 1);
v_ngen_2539_ = lean_ctor_get(v___x_2535_, 2);
v_auxDeclNGen_2540_ = lean_ctor_get(v___x_2535_, 3);
v_cache_2541_ = lean_ctor_get(v___x_2535_, 5);
v_messages_2542_ = lean_ctor_get(v___x_2535_, 6);
v_infoState_2543_ = lean_ctor_get(v___x_2535_, 7);
v_snapshotTasks_2544_ = lean_ctor_get(v___x_2535_, 8);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2546_ = v___x_2535_;
v_isShared_2547_ = v_isSharedCheck_2567_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_snapshotTasks_2544_);
lean_inc(v_infoState_2543_);
lean_inc(v_messages_2542_);
lean_inc(v_cache_2541_);
lean_inc(v_traceState_2536_);
lean_inc(v_auxDeclNGen_2540_);
lean_inc(v_ngen_2539_);
lean_inc(v_nextMacroScope_2538_);
lean_inc(v_env_2537_);
lean_dec(v___x_2535_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2567_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
uint64_t v_tid_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2565_; 
v_tid_2548_ = lean_ctor_get_uint64(v_traceState_2536_, sizeof(void*)*1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_traceState_2536_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v_traceState_2536_, 0);
lean_dec(v_unused_2566_);
v___x_2550_ = v_traceState_2536_;
v_isShared_2551_ = v_isSharedCheck_2565_;
goto v_resetjp_2549_;
}
else
{
lean_dec(v_traceState_2536_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2565_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v_ref_2493_);
lean_ctor_set(v___x_2552_, 1, v_a_2531_);
v___x_2553_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2491_, v___x_2552_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2553_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2553_);
lean_ctor_set_uint64(v_reuseFailAlloc_2564_, sizeof(void*)*1, v_tid_2548_);
v___x_2555_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 4, v___x_2555_);
v___x_2557_ = v___x_2546_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_env_2537_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_nextMacroScope_2538_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_ngen_2539_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_auxDeclNGen_2540_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2563_, 5, v_cache_2541_);
lean_ctor_set(v_reuseFailAlloc_2563_, 6, v_messages_2542_);
lean_ctor_set(v_reuseFailAlloc_2563_, 7, v_infoState_2543_);
lean_ctor_set(v_reuseFailAlloc_2563_, 8, v_snapshotTasks_2544_);
v___x_2557_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2558_ = lean_st_ref_set(v___y_2498_, v___x_2557_);
v___x_2559_ = lean_box(0);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2559_);
v___x_2561_ = v___x_2533_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_oldTraces_2571_, lean_object* v_data_2572_, lean_object* v_ref_2573_, lean_object* v_msg_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2571_, v_data_2572_, v_ref_2573_, v_msg_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
return v_res_2580_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2583_ = l_Lean_stringToMessageData(v___x_2582_);
return v___x_2583_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2));
v___x_2586_ = l_Lean_stringToMessageData(v___x_2585_);
return v___x_2586_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2587_; double v___x_2588_; 
v___x_2587_ = lean_unsigned_to_nat(1000u);
v___x_2588_ = lean_float_of_nat(v___x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2589_, uint8_t v_collapsed_2590_, lean_object* v_tag_2591_, lean_object* v_opts_2592_, uint8_t v_clsEnabled_2593_, lean_object* v_oldTraces_2594_, lean_object* v_msg_2595_, lean_object* v_resStartStop_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_fst_2602_; lean_object* v_snd_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2693_; 
v_fst_2602_ = lean_ctor_get(v_resStartStop_2596_, 0);
v_snd_2603_ = lean_ctor_get(v_resStartStop_2596_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_resStartStop_2596_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2605_ = v_resStartStop_2596_;
v_isShared_2606_ = v_isSharedCheck_2693_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_snd_2603_);
lean_inc(v_fst_2602_);
lean_dec(v_resStartStop_2596_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2693_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v_data_2610_; lean_object* v_fst_2613_; lean_object* v_snd_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2692_; 
v_fst_2613_ = lean_ctor_get(v_snd_2603_, 0);
v_snd_2614_ = lean_ctor_get(v_snd_2603_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_snd_2603_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2616_ = v_snd_2603_;
v_isShared_2617_ = v_isSharedCheck_2692_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_snd_2614_);
lean_inc(v_fst_2613_);
lean_dec(v_snd_2603_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2692_;
goto v_resetjp_2615_;
}
v___jp_2607_:
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2594_, v_data_2610_, v___y_2608_, v___y_2609_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v___x_2612_; 
lean_dec_ref(v___x_2611_);
v___x_2612_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2602_);
return v___x_2612_;
}
else
{
lean_dec(v_fst_2602_);
return v___x_2611_;
}
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; uint8_t v___x_2619_; lean_object* v___y_2621_; lean_object* v_a_2622_; uint8_t v___y_2646_; double v___y_2677_; 
v___x_2618_ = l_Lean_trace_profiler;
v___x_2619_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2592_, v___x_2618_);
if (v___x_2619_ == 0)
{
v___y_2646_ = v___x_2619_;
goto v___jp_2645_;
}
else
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2683_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2592_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; double v___x_2686_; double v___x_2687_; double v___x_2688_; 
v___x_2684_ = l_Lean_trace_profiler_threshold;
v___x_2685_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2592_, v___x_2684_);
v___x_2686_ = lean_float_of_nat(v___x_2685_);
v___x_2687_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4);
v___x_2688_ = lean_float_div(v___x_2686_, v___x_2687_);
v___y_2677_ = v___x_2688_;
goto v___jp_2676_;
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; double v___x_2691_; 
v___x_2689_ = l_Lean_trace_profiler_threshold;
v___x_2690_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2592_, v___x_2689_);
v___x_2691_ = lean_float_of_nat(v___x_2690_);
v___y_2677_ = v___x_2691_;
goto v___jp_2676_;
}
}
v___jp_2620_:
{
uint8_t v_result_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v_result_2623_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_fst_2602_);
v___x_2624_ = l_Lean_TraceResult_toEmoji(v_result_2623_);
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
v___x_2626_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
if (v_isShared_2617_ == 0)
{
lean_ctor_set_tag(v___x_2616_, 7);
lean_ctor_set(v___x_2616_, 1, v___x_2626_);
lean_ctor_set(v___x_2616_, 0, v___x_2625_);
v___x_2628_ = v___x_2616_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v_m_2630_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 7);
lean_ctor_set(v___x_2605_, 1, v_a_2622_);
lean_ctor_set(v___x_2605_, 0, v___x_2628_);
v_m_2630_ = v___x_2605_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_a_2622_);
v_m_2630_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; double v___x_2633_; lean_object* v_data_2634_; 
v___x_2631_ = lean_box(v_result_2623_);
v___x_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
v___x_2633_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0);
lean_inc_ref(v_tag_2591_);
lean_inc_ref(v___x_2632_);
lean_inc(v_cls_2589_);
v_data_2634_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2634_, 0, v_cls_2589_);
lean_ctor_set(v_data_2634_, 1, v___x_2632_);
lean_ctor_set(v_data_2634_, 2, v_tag_2591_);
lean_ctor_set_float(v_data_2634_, sizeof(void*)*3, v___x_2633_);
lean_ctor_set_float(v_data_2634_, sizeof(void*)*3 + 8, v___x_2633_);
lean_ctor_set_uint8(v_data_2634_, sizeof(void*)*3 + 16, v_collapsed_2590_);
if (v___x_2619_ == 0)
{
lean_dec_ref(v___x_2632_);
lean_dec(v_snd_2614_);
lean_dec(v_fst_2613_);
lean_dec_ref(v_tag_2591_);
lean_dec(v_cls_2589_);
v___y_2608_ = v___y_2621_;
v___y_2609_ = v_m_2630_;
v_data_2610_ = v_data_2634_;
goto v___jp_2607_;
}
else
{
lean_object* v_data_2635_; double v___x_2636_; double v___x_2637_; 
lean_dec_ref(v_data_2634_);
v_data_2635_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2635_, 0, v_cls_2589_);
lean_ctor_set(v_data_2635_, 1, v___x_2632_);
lean_ctor_set(v_data_2635_, 2, v_tag_2591_);
v___x_2636_ = lean_unbox_float(v_fst_2613_);
lean_dec(v_fst_2613_);
lean_ctor_set_float(v_data_2635_, sizeof(void*)*3, v___x_2636_);
v___x_2637_ = lean_unbox_float(v_snd_2614_);
lean_dec(v_snd_2614_);
lean_ctor_set_float(v_data_2635_, sizeof(void*)*3 + 8, v___x_2637_);
lean_ctor_set_uint8(v_data_2635_, sizeof(void*)*3 + 16, v_collapsed_2590_);
v___y_2608_ = v___y_2621_;
v___y_2609_ = v_m_2630_;
v_data_2610_ = v_data_2635_;
goto v___jp_2607_;
}
}
}
}
v___jp_2640_:
{
lean_object* v_ref_2641_; lean_object* v___x_2642_; 
v_ref_2641_ = lean_ctor_get(v___y_2599_, 5);
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
lean_inc(v_fst_2602_);
v___x_2642_ = lean_apply_6(v_msg_2595_, v_fst_2602_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, lean_box(0));
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref(v___x_2642_);
lean_inc(v_ref_2641_);
v___y_2621_ = v_ref_2641_;
v_a_2622_ = v_a_2643_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2644_; 
lean_dec_ref(v___x_2642_);
v___x_2644_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3);
lean_inc(v_ref_2641_);
v___y_2621_ = v_ref_2641_;
v_a_2622_ = v___x_2644_;
goto v___jp_2620_;
}
}
v___jp_2645_:
{
if (v_clsEnabled_2593_ == 0)
{
if (v___y_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v_traceState_2648_; lean_object* v_env_2649_; lean_object* v_nextMacroScope_2650_; lean_object* v_ngen_2651_; lean_object* v_auxDeclNGen_2652_; lean_object* v_cache_2653_; lean_object* v_messages_2654_; lean_object* v_infoState_2655_; lean_object* v_snapshotTasks_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2675_; 
lean_del_object(v___x_2616_);
lean_dec(v_snd_2614_);
lean_dec(v_fst_2613_);
lean_del_object(v___x_2605_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_msg_2595_);
lean_dec_ref(v_tag_2591_);
lean_dec(v_cls_2589_);
v___x_2647_ = lean_st_ref_take(v___y_2600_);
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
v___x_2665_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2594_, v_traces_2661_);
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
v___x_2670_ = lean_st_ref_set(v___y_2600_, v___x_2669_);
lean_dec(v___y_2600_);
v___x_2671_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2602_);
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
v___x_2678_ = lean_unbox_float(v_snd_2614_);
v___x_2679_ = lean_unbox_float(v_fst_2613_);
v___x_2680_ = lean_float_sub(v___x_2678_, v___x_2679_);
v___x_2681_ = lean_float_decLt(v___y_2677_, v___x_2680_);
v___y_2646_ = v___x_2681_;
goto v___jp_2645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2694_, lean_object* v_collapsed_2695_, lean_object* v_tag_2696_, lean_object* v_opts_2697_, lean_object* v_clsEnabled_2698_, lean_object* v_oldTraces_2699_, lean_object* v_msg_2700_, lean_object* v_resStartStop_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
uint8_t v_collapsed_boxed_2707_; uint8_t v_clsEnabled_boxed_2708_; lean_object* v_res_2709_; 
v_collapsed_boxed_2707_ = lean_unbox(v_collapsed_2695_);
v_clsEnabled_boxed_2708_ = lean_unbox(v_clsEnabled_2698_);
v_res_2709_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2694_, v_collapsed_boxed_2707_, v_tag_2696_, v_opts_2697_, v_clsEnabled_boxed_2708_, v_oldTraces_2699_, v_msg_2700_, v_resStartStop_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec_ref(v_opts_2697_);
return v_res_2709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0));
v___x_2712_ = l_Lean_stringToMessageData(v___x_2711_);
return v___x_2712_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2713_; double v___x_2714_; 
v___x_2713_ = lean_unsigned_to_nat(1000000000u);
v___x_2714_ = lean_float_of_nat(v___x_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_toConstantVal_2721_; lean_object* v_options_2722_; lean_object* v_name_2723_; lean_object* v_levelParams_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2962_; 
v_toConstantVal_2721_ = lean_ctor_get(v_ctorVal_2715_, 0);
lean_inc_ref(v_toConstantVal_2721_);
v_options_2722_ = lean_ctor_get(v_a_2718_, 2);
v_name_2723_ = lean_ctor_get(v_toConstantVal_2721_, 0);
v_levelParams_2724_ = lean_ctor_get(v_toConstantVal_2721_, 1);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_toConstantVal_2721_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v_toConstantVal_2721_, 2);
lean_dec(v_unused_2963_);
v___x_2726_ = v_toConstantVal_2721_;
v_isShared_2727_ = v_isSharedCheck_2962_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_levelParams_2724_);
lean_inc(v_name_2723_);
lean_dec(v_toConstantVal_2721_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2962_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
uint8_t v_hasTrace_2728_; lean_object* v_name_2729_; lean_object* v_cls_2730_; 
v_hasTrace_2728_ = lean_ctor_get_uint8(v_options_2722_, sizeof(void*)*1);
lean_inc(v_name_2723_);
v_name_2729_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2723_);
v_cls_2730_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
if (v_hasTrace_2728_ == 0)
{
lean_object* v___x_2731_; 
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
v___x_2731_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2781_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2781_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2781_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
if (lean_obj_tag(v_a_2732_) == 1)
{
lean_object* v_val_2736_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___x_2770_; lean_object* v_a_2771_; uint8_t v___x_2772_; 
lean_del_object(v___x_2734_);
v_val_2736_ = lean_ctor_get(v_a_2732_, 0);
lean_inc(v_val_2736_);
lean_dec_ref(v_a_2732_);
v___x_2770_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2730_, v_a_2718_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref(v___x_2770_);
v___x_2772_ = lean_unbox(v_a_2771_);
lean_dec(v_a_2771_);
if (v___x_2772_ == 0)
{
v___y_2738_ = v_a_2716_;
v___y_2739_ = v_a_2717_;
v___y_2740_ = v_a_2718_;
v___y_2741_ = v_a_2719_;
goto v___jp_2737_;
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2773_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_2736_);
v___x_2774_ = l_Lean_MessageData_ofExpr(v_val_2736_);
v___x_2775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2730_, v___x_2775_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_dec_ref(v___x_2776_);
v___y_2738_ = v_a_2716_;
v___y_2739_ = v_a_2717_;
v___y_2740_ = v_a_2718_;
v___y_2741_ = v_a_2719_;
goto v___jp_2737_;
}
else
{
lean_dec(v_val_2736_);
lean_dec(v_name_2729_);
lean_del_object(v___x_2726_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
return v___x_2776_;
}
}
v___jp_2737_:
{
lean_object* v___x_2742_; 
lean_inc(v___y_2741_);
lean_inc_ref(v___y_2740_);
lean_inc(v___y_2739_);
lean_inc(v_val_2736_);
v___x_2742_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2723_, v_val_2736_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2761_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v___x_2742_);
v___x_2744_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2736_, v___y_2739_);
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
v___x_2746_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2743_, v___y_2739_);
lean_dec(v___y_2739_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2761_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2761_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
lean_inc(v_name_2729_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 2, v_a_2745_);
lean_ctor_set(v___x_2726_, 0, v_name_2729_);
v___x_2752_ = v___x_2726_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_name_2729_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_levelParams_2724_);
lean_ctor_set(v_reuseFailAlloc_2760_, 2, v_a_2745_);
v___x_2752_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2753_ = lean_box(0);
v___x_2754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_name_2729_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2752_);
lean_ctor_set(v___x_2755_, 1, v_a_2747_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 2);
lean_ctor_set(v___x_2749_, 0, v___x_2755_);
v___x_2757_ = v___x_2749_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_addDecl(v___x_2757_, v_hasTrace_2728_, v___y_2740_, v___y_2741_);
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec(v_val_2736_);
lean_dec(v_name_2729_);
lean_del_object(v___x_2726_);
lean_dec(v_levelParams_2724_);
v_a_2762_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2742_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2742_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
lean_dec(v_a_2732_);
lean_dec(v_name_2729_);
lean_del_object(v___x_2726_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
v___x_2777_ = lean_box(0);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2777_);
v___x_2779_ = v___x_2734_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_name_2729_);
lean_del_object(v___x_2726_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
v_a_2782_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2731_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2731_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
else
{
lean_object* v___x_2790_; lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2961_; 
v___x_2790_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2730_, v_a_2718_);
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2961_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2961_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___f_2795_; lean_object* v___x_2796_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v_a_2800_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v_a_2813_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v_a_2820_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v_a_2831_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v_a_2847_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v_a_2852_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; uint8_t v___x_2899_; 
lean_inc(v_name_2729_);
v___f_2795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2795_, 0, v_name_2729_);
v___x_2796_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1));
v___x_2899_ = lean_unbox(v_a_2791_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; uint8_t v___x_2901_; 
v___x_2900_ = l_Lean_trace_profiler;
v___x_2901_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2722_, v___x_2900_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; 
lean_dec_ref(v___f_2795_);
lean_del_object(v___x_2793_);
lean_dec(v_a_2791_);
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
v___x_2902_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2952_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2952_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2952_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
if (lean_obj_tag(v_a_2903_) == 1)
{
lean_object* v_val_2907_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___x_2941_; lean_object* v_a_2942_; uint8_t v___x_2943_; 
lean_del_object(v___x_2905_);
v_val_2907_ = lean_ctor_get(v_a_2903_, 0);
lean_inc(v_val_2907_);
lean_dec_ref(v_a_2903_);
v___x_2941_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2730_, v_a_2718_);
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
v___x_2943_ = lean_unbox(v_a_2942_);
lean_dec(v_a_2942_);
if (v___x_2943_ == 0)
{
v___y_2909_ = v_a_2716_;
v___y_2910_ = v_a_2717_;
v___y_2911_ = v_a_2718_;
v___y_2912_ = v_a_2719_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2944_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_2907_);
v___x_2945_ = l_Lean_MessageData_ofExpr(v_val_2907_);
v___x_2946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2944_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2730_, v___x_2946_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_dec_ref(v___x_2947_);
v___y_2909_ = v_a_2716_;
v___y_2910_ = v_a_2717_;
v___y_2911_ = v_a_2718_;
v___y_2912_ = v_a_2719_;
goto v___jp_2908_;
}
else
{
lean_dec(v_val_2907_);
lean_dec(v_name_2729_);
lean_del_object(v___x_2726_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
return v___x_2947_;
}
}
v___jp_2908_:
{
lean_object* v___x_2913_; 
lean_inc(v___y_2912_);
lean_inc_ref(v___y_2911_);
lean_inc(v___y_2910_);
lean_inc(v_val_2907_);
v___x_2913_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2723_, v_val_2907_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2915_; lean_object* v_a_2916_; lean_object* v___x_2917_; lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2932_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref(v___x_2913_);
v___x_2915_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2907_, v___y_2910_);
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref(v___x_2915_);
v___x_2917_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2914_, v___y_2910_);
lean_dec(v___y_2910_);
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2920_ = v___x_2917_;
v_isShared_2921_ = v_isSharedCheck_2932_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2932_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
lean_inc(v_name_2729_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 2, v_a_2916_);
lean_ctor_set(v___x_2726_, 0, v_name_2729_);
v___x_2923_ = v___x_2726_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_name_2729_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_levelParams_2724_);
lean_ctor_set(v_reuseFailAlloc_2931_, 2, v_a_2916_);
v___x_2923_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2924_ = lean_box(0);
v___x_2925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2925_, 0, v_name_2729_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2923_);
lean_ctor_set(v___x_2926_, 1, v_a_2918_);
lean_ctor_set(v___x_2926_, 2, v___x_2925_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set_tag(v___x_2920_, 2);
lean_ctor_set(v___x_2920_, 0, v___x_2926_);
v___x_2928_ = v___x_2920_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_addDecl(v___x_2928_, v___x_2901_, v___y_2911_, v___y_2912_);
return v___x_2929_;
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v_val_2907_);
lean_dec(v_name_2729_);
lean_del_object(v___x_2726_);
lean_dec(v_levelParams_2724_);
v_a_2933_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2913_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2913_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
else
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
lean_dec(v_a_2903_);
lean_dec(v_name_2729_);
lean_del_object(v___x_2726_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
v___x_2948_ = lean_box(0);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2948_);
v___x_2950_ = v___x_2905_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
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
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec(v_name_2729_);
lean_del_object(v___x_2726_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
v_a_2953_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2902_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2902_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
else
{
lean_inc_ref(v_options_2722_);
lean_del_object(v___x_2726_);
goto v___jp_2860_;
}
}
else
{
lean_inc_ref(v_options_2722_);
lean_del_object(v___x_2726_);
goto v___jp_2860_;
}
v___jp_2797_:
{
lean_object* v___x_2801_; double v___x_2802_; double v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; lean_object* v___x_2809_; 
v___x_2801_ = lean_io_get_num_heartbeats();
v___x_2802_ = lean_float_of_nat(v___y_2798_);
v___x_2803_ = lean_float_of_nat(v___x_2801_);
v___x_2804_ = lean_box_float(v___x_2802_);
v___x_2805_ = lean_box_float(v___x_2803_);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2807_, 0, v_a_2800_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = lean_unbox(v_a_2791_);
lean_dec(v_a_2791_);
v___x_2809_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2730_, v_hasTrace_2728_, v___x_2796_, v_options_2722_, v___x_2808_, v___y_2799_, v___f_2795_, v___x_2807_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec_ref(v_options_2722_);
return v___x_2809_;
}
v___jp_2810_:
{
lean_object* v___x_2815_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v_a_2813_);
v___x_2815_ = v___x_2793_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
v___y_2798_ = v___y_2811_;
v___y_2799_ = v___y_2812_;
v_a_2800_ = v___x_2815_;
goto v___jp_2797_;
}
}
v___jp_2817_:
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2820_);
v___y_2798_ = v___y_2818_;
v___y_2799_ = v___y_2819_;
v_a_2800_ = v___x_2821_;
goto v___jp_2797_;
}
v___jp_2822_:
{
if (lean_obj_tag(v___y_2825_) == 0)
{
lean_object* v_a_2826_; 
lean_del_object(v___x_2793_);
v_a_2826_ = lean_ctor_get(v___y_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref(v___y_2825_);
v___y_2818_ = v___y_2823_;
v___y_2819_ = v___y_2824_;
v_a_2820_ = v_a_2826_;
goto v___jp_2817_;
}
else
{
lean_object* v_a_2827_; 
v_a_2827_ = lean_ctor_get(v___y_2825_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___y_2825_);
v___y_2811_ = v___y_2823_;
v___y_2812_ = v___y_2824_;
v_a_2813_ = v_a_2827_;
goto v___jp_2810_;
}
}
v___jp_2828_:
{
lean_object* v___x_2832_; double v___x_2833_; double v___x_2834_; double v___x_2835_; double v___x_2836_; double v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; lean_object* v___x_2843_; 
v___x_2832_ = lean_io_mono_nanos_now();
v___x_2833_ = lean_float_of_nat(v___y_2830_);
v___x_2834_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2835_ = lean_float_div(v___x_2833_, v___x_2834_);
v___x_2836_ = lean_float_of_nat(v___x_2832_);
v___x_2837_ = lean_float_div(v___x_2836_, v___x_2834_);
v___x_2838_ = lean_box_float(v___x_2835_);
v___x_2839_ = lean_box_float(v___x_2837_);
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v_a_2831_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = lean_unbox(v_a_2791_);
lean_dec(v_a_2791_);
v___x_2843_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2730_, v_hasTrace_2728_, v___x_2796_, v_options_2722_, v___x_2842_, v___y_2829_, v___f_2795_, v___x_2841_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec_ref(v_options_2722_);
return v___x_2843_;
}
v___jp_2844_:
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_a_2847_);
v___y_2829_ = v___y_2846_;
v___y_2830_ = v___y_2845_;
v_a_2831_ = v___x_2848_;
goto v___jp_2828_;
}
v___jp_2849_:
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_a_2852_);
v___y_2829_ = v___y_2851_;
v___y_2830_ = v___y_2850_;
v_a_2831_ = v___x_2853_;
goto v___jp_2828_;
}
v___jp_2854_:
{
if (lean_obj_tag(v___y_2857_) == 0)
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___y_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___y_2857_);
v___y_2845_ = v___y_2856_;
v___y_2846_ = v___y_2855_;
v_a_2847_ = v_a_2858_;
goto v___jp_2844_;
}
else
{
lean_object* v_a_2859_; 
v_a_2859_ = lean_ctor_get(v___y_2857_, 0);
lean_inc(v_a_2859_);
lean_dec_ref(v___y_2857_);
v___y_2850_ = v___y_2856_;
v___y_2851_ = v___y_2855_;
v_a_2852_ = v_a_2859_;
goto v___jp_2849_;
}
}
v___jp_2860_:
{
lean_object* v___x_2861_; lean_object* v_a_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2861_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2719_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2864_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2722_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
lean_del_object(v___x_2793_);
v___x_2865_ = lean_io_mono_nanos_now();
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
v___x_2866_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
if (lean_obj_tag(v_a_2867_) == 1)
{
lean_object* v_val_2868_; lean_object* v___x_2869_; lean_object* v_a_2870_; uint8_t v___x_2871_; 
v_val_2868_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_val_2868_);
lean_dec_ref(v_a_2867_);
v___x_2869_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2730_, v_a_2718_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = lean_unbox(v_a_2870_);
lean_dec(v_a_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_box(0);
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
v___x_2873_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2723_, v_val_2868_, v_name_2729_, v_levelParams_2724_, v___x_2864_, v___x_2872_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
v___y_2855_ = v_a_2862_;
v___y_2856_ = v___x_2865_;
v___y_2857_ = v___x_2873_;
goto v___jp_2854_;
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2874_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_2868_);
v___x_2875_ = l_Lean_MessageData_ofExpr(v_val_2868_);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2730_, v___x_2876_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref(v___x_2877_);
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
v___x_2879_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2723_, v_val_2868_, v_name_2729_, v_levelParams_2724_, v___x_2864_, v_a_2878_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
v___y_2855_ = v_a_2862_;
v___y_2856_ = v___x_2865_;
v___y_2857_ = v___x_2879_;
goto v___jp_2854_;
}
else
{
lean_dec(v_val_2868_);
lean_dec(v_name_2729_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
v___y_2855_ = v_a_2862_;
v___y_2856_ = v___x_2865_;
v___y_2857_ = v___x_2877_;
goto v___jp_2854_;
}
}
}
else
{
lean_object* v___x_2880_; 
lean_dec(v_a_2867_);
lean_dec(v_name_2729_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
v___x_2880_ = lean_box(0);
v___y_2845_ = v___x_2865_;
v___y_2846_ = v_a_2862_;
v_a_2847_ = v___x_2880_;
goto v___jp_2844_;
}
}
else
{
lean_object* v_a_2881_; 
lean_dec(v_name_2729_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
v_a_2881_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2881_);
lean_dec_ref(v___x_2866_);
v___y_2850_ = v___x_2865_;
v___y_2851_ = v_a_2862_;
v_a_2852_ = v_a_2881_;
goto v___jp_2849_;
}
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
v___x_2883_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref(v___x_2883_);
if (lean_obj_tag(v_a_2884_) == 1)
{
lean_object* v_val_2885_; lean_object* v___x_2886_; lean_object* v_a_2887_; uint8_t v___x_2888_; 
v_val_2885_ = lean_ctor_get(v_a_2884_, 0);
lean_inc(v_val_2885_);
lean_dec_ref(v_a_2884_);
v___x_2886_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2730_, v_a_2718_);
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref(v___x_2886_);
v___x_2888_ = lean_unbox(v_a_2887_);
lean_dec(v_a_2887_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_box(0);
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
v___x_2890_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2723_, v_val_2885_, v_name_2729_, v_levelParams_2724_, v___x_2889_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
v___y_2823_ = v___x_2882_;
v___y_2824_ = v_a_2862_;
v___y_2825_ = v___x_2890_;
goto v___jp_2822_;
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2891_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_2885_);
v___x_2892_ = l_Lean_MessageData_ofExpr(v_val_2885_);
v___x_2893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2730_, v___x_2893_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2896_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref(v___x_2894_);
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
v___x_2896_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2723_, v_val_2885_, v_name_2729_, v_levelParams_2724_, v_a_2895_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
v___y_2823_ = v___x_2882_;
v___y_2824_ = v_a_2862_;
v___y_2825_ = v___x_2896_;
goto v___jp_2822_;
}
else
{
lean_dec(v_val_2885_);
lean_dec(v_name_2729_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
v___y_2823_ = v___x_2882_;
v___y_2824_ = v_a_2862_;
v___y_2825_ = v___x_2894_;
goto v___jp_2822_;
}
}
}
else
{
lean_object* v___x_2897_; 
lean_dec(v_a_2884_);
lean_del_object(v___x_2793_);
lean_dec(v_name_2729_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
v___x_2897_ = lean_box(0);
v___y_2818_ = v___x_2882_;
v___y_2819_ = v_a_2862_;
v_a_2820_ = v___x_2897_;
goto v___jp_2817_;
}
}
else
{
lean_object* v_a_2898_; 
lean_dec(v_name_2729_);
lean_dec(v_levelParams_2724_);
lean_dec(v_name_2723_);
v_a_2898_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2883_);
v___y_2811_ = v___x_2882_;
v___y_2812_ = v_a_2862_;
v_a_2813_ = v_a_2898_;
goto v___jp_2810_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_00_u03b1_2971_, lean_object* v_x_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2972_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2979_, lean_object* v_x_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_00_u03b1_2979_, v_x_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2990_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2992_ = l_Lean_Name_append(v_ctorName_2990_, v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
uint8_t v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = 1;
v___x_3000_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2993_, v___x_2999_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_3008_, lean_object* v_t_3009_, lean_object* v_acc_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_3009_, v_a_3011_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3037_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3037_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3037_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3023_ = l_Lean_Expr_cleanupAnnotations(v_a_3014_);
v___x_3024_ = l_Lean_Expr_isApp(v___x_3023_);
if (v___x_3024_ == 0)
{
lean_dec_ref(v___x_3023_);
goto v___jp_3018_;
}
else
{
lean_object* v_arg_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v_arg_3025_ = lean_ctor_get(v___x_3023_, 1);
lean_inc_ref(v_arg_3025_);
v___x_3026_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3023_);
v___x_3027_ = l_Lean_Expr_isApp(v___x_3026_);
if (v___x_3027_ == 0)
{
lean_dec_ref(v___x_3026_);
lean_dec_ref(v_arg_3025_);
goto v___jp_3018_;
}
else
{
lean_object* v_arg_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v_arg_3028_ = lean_ctor_get(v___x_3026_, 1);
lean_inc_ref(v_arg_3028_);
v___x_3029_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3026_);
v___x_3030_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3031_ = l_Lean_Expr_isConstOf(v___x_3029_, v___x_3030_);
lean_dec_ref(v___x_3029_);
if (v___x_3031_ == 0)
{
lean_dec_ref(v_arg_3028_);
lean_dec_ref(v_arg_3025_);
goto v___jp_3018_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_del_object(v___x_3016_);
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = l_Lean_mkProj(v___x_3030_, v___x_3032_, v_e_3008_);
lean_inc_ref(v___x_3033_);
v___x_3034_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_3033_, v_arg_3028_, v_acc_3010_, v_a_3011_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
v_e_3008_ = v___x_3033_;
v_t_3009_ = v_arg_3025_;
v_acc_3010_ = v_a_3035_;
goto _start;
}
else
{
lean_dec_ref(v___x_3033_);
lean_dec_ref(v_arg_3025_);
return v___x_3034_;
}
}
}
}
v___jp_3018_:
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3019_ = lean_array_push(v_acc_3010_, v_e_3008_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3019_);
v___x_3021_ = v___x_3016_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_acc_3010_);
lean_dec_ref(v_e_3008_);
v_a_3038_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3013_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3013_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_3046_, lean_object* v_t_3047_, lean_object* v_acc_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3046_, v_t_3047_, v_acc_3048_, v_a_3049_);
lean_dec(v_a_3049_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_3052_, lean_object* v_t_3053_, lean_object* v_acc_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3052_, v_t_3053_, v_acc_3054_, v_a_3056_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3061_, lean_object* v_t_3062_, lean_object* v_acc_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3061_, v_t_3062_, v_acc_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v___x_3076_; 
lean_inc(v_a_3072_);
lean_inc_ref(v_e_3070_);
v___x_3076_ = lean_infer_type(v_e_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref(v___x_3076_);
v___x_3078_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3079_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3070_, v_a_3077_, v___x_3078_, v_a_3072_);
lean_dec(v_a_3072_);
return v___x_3079_;
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_a_3072_);
lean_dec_ref(v_e_3070_);
v_a_3080_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3076_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3076_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
return v_res_3094_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = lean_box(0);
v___x_3101_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2));
v___x_3102_ = l_Lean_mkConst(v___x_3101_, v___x_3100_);
return v___x_3102_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4));
v___x_3105_ = l_Lean_stringToMessageData(v___x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_b_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v___x_3112_; 
lean_inc(v_b_3106_);
v___x_3112_ = l_Lean_MVarId_getType(v_b_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3193_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3193_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3193_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
if (lean_obj_tag(v_a_3113_) == 7)
{
lean_object* v_binderType_3117_; lean_object* v_body_3118_; uint8_t v___x_3119_; lean_object* v_mvarId_u2082_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; 
v_binderType_3117_ = lean_ctor_get(v_a_3113_, 1);
lean_inc_ref(v_binderType_3117_);
v_body_3118_ = lean_ctor_get(v_a_3113_, 2);
lean_inc_ref(v_body_3118_);
lean_dec_ref(v_a_3113_);
v___x_3119_ = l_Lean_Expr_hasLooseBVars(v_body_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3138_; 
lean_del_object(v___x_3115_);
v___x_3138_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3117_, v___y_3108_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref(v___x_3138_);
v___x_3140_ = l_Lean_Expr_cleanupAnnotations(v_a_3139_);
v___x_3141_ = l_Lean_Expr_isApp(v___x_3140_);
if (v___x_3141_ == 0)
{
lean_dec_ref(v___x_3140_);
lean_dec_ref(v_body_3118_);
lean_inc(v___y_3110_);
lean_inc_ref(v___y_3109_);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
v_mvarId_u2082_3121_ = v_b_3106_;
v___y_3122_ = v___y_3107_;
v___y_3123_ = v___y_3108_;
v___y_3124_ = v___y_3109_;
v___y_3125_ = v___y_3110_;
goto v___jp_3120_;
}
else
{
lean_object* v_arg_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v_arg_3142_ = lean_ctor_get(v___x_3140_, 1);
lean_inc_ref(v_arg_3142_);
v___x_3143_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3140_);
v___x_3144_ = l_Lean_Expr_isApp(v___x_3143_);
if (v___x_3144_ == 0)
{
lean_dec_ref(v___x_3143_);
lean_dec_ref(v_arg_3142_);
lean_dec_ref(v_body_3118_);
lean_inc(v___y_3110_);
lean_inc_ref(v___y_3109_);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
v_mvarId_u2082_3121_ = v_b_3106_;
v___y_3122_ = v___y_3107_;
v___y_3123_ = v___y_3108_;
v___y_3124_ = v___y_3109_;
v___y_3125_ = v___y_3110_;
goto v___jp_3120_;
}
else
{
lean_object* v_arg_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v_arg_3145_ = lean_ctor_get(v___x_3143_, 1);
lean_inc_ref(v_arg_3145_);
v___x_3146_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3143_);
v___x_3147_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3148_ = l_Lean_Expr_isConstOf(v___x_3146_, v___x_3147_);
lean_dec_ref(v___x_3146_);
if (v___x_3148_ == 0)
{
lean_dec_ref(v_arg_3145_);
lean_dec_ref(v_arg_3142_);
lean_dec_ref(v_body_3118_);
lean_inc(v___y_3110_);
lean_inc_ref(v___y_3109_);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
v_mvarId_u2082_3121_ = v_b_3106_;
v___y_3122_ = v___y_3107_;
v___y_3123_ = v___y_3108_;
v___y_3124_ = v___y_3109_;
v___y_3125_ = v___y_3110_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3149_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3);
v___x_3150_ = l_Lean_mkApp3(v___x_3149_, v_arg_3145_, v_arg_3142_, v_body_3118_);
v___x_3151_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_3110_);
lean_inc_ref(v___y_3109_);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
lean_inc(v_b_3106_);
v___x_3152_ = l_Lean_MVarId_applyN(v_b_3106_, v___x_3150_, v___x_3151_, v___x_3148_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3152_);
if (lean_obj_tag(v_a_3153_) == 1)
{
lean_object* v_tail_3169_; 
v_tail_3169_ = lean_ctor_get(v_a_3153_, 1);
if (lean_obj_tag(v_tail_3169_) == 0)
{
lean_object* v_head_3170_; 
lean_dec(v_b_3106_);
v_head_3170_ = lean_ctor_get(v_a_3153_, 0);
lean_inc(v_head_3170_);
lean_dec_ref(v_a_3153_);
lean_inc(v___y_3110_);
lean_inc_ref(v___y_3109_);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
v_mvarId_u2082_3121_ = v_head_3170_;
v___y_3122_ = v___y_3107_;
v___y_3123_ = v___y_3108_;
v___y_3124_ = v___y_3109_;
v___y_3125_ = v___y_3110_;
goto v___jp_3120_;
}
else
{
lean_dec_ref(v_a_3153_);
lean_inc(v___y_3110_);
lean_inc_ref(v___y_3109_);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
v___y_3155_ = v___y_3107_;
v___y_3156_ = v___y_3108_;
v___y_3157_ = v___y_3109_;
v___y_3158_ = v___y_3110_;
goto v___jp_3154_;
}
}
else
{
lean_dec(v_a_3153_);
lean_inc(v___y_3110_);
lean_inc_ref(v___y_3109_);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
v___y_3155_ = v___y_3107_;
v___y_3156_ = v___y_3108_;
v___y_3157_ = v___y_3109_;
v___y_3158_ = v___y_3110_;
goto v___jp_3154_;
}
v___jp_3154_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5);
v___x_3160_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3159_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_dec_ref(v___x_3160_);
v_mvarId_u2082_3121_ = v_b_3106_;
v___y_3122_ = v___y_3155_;
v___y_3123_ = v___y_3156_;
v___y_3124_ = v___y_3157_;
v___y_3125_ = v___y_3158_;
goto v___jp_3120_;
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v_b_3106_);
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v_b_3106_);
v_a_3171_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3152_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3152_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
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
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec_ref(v_body_3118_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v_b_3106_);
v_a_3179_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3138_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3138_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v___x_3188_; 
lean_dec_ref(v_body_3118_);
lean_dec_ref(v_binderType_3117_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v_b_3106_);
v___x_3188_ = v___x_3115_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_b_3106_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
v___jp_3120_:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3121_, v___x_3119_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v_snd_3128_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
v_snd_3128_ = lean_ctor_get(v_a_3127_, 1);
lean_inc(v_snd_3128_);
lean_dec(v_a_3127_);
v_b_3106_ = v_snd_3128_;
goto _start;
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
v_a_3130_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3126_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3126_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
else
{
lean_object* v___x_3191_; 
lean_dec(v_a_3113_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v_b_3106_);
v___x_3191_ = v___x_3115_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_b_3106_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v_b_3106_);
v_a_3194_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3112_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3112_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_b_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_b_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3209_, lean_object* v_x_3210_, lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v_ks_3213_; lean_object* v_vs_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3238_; 
v_ks_3213_ = lean_ctor_get(v_x_3209_, 0);
v_vs_3214_ = lean_ctor_get(v_x_3209_, 1);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_x_3209_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3216_ = v_x_3209_;
v_isShared_3217_ = v_isSharedCheck_3238_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_vs_3214_);
lean_inc(v_ks_3213_);
lean_dec(v_x_3209_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3238_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3218_ = lean_array_get_size(v_ks_3213_);
v___x_3219_ = lean_nat_dec_lt(v_x_3210_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_dec(v_x_3210_);
v___x_3220_ = lean_array_push(v_ks_3213_, v_x_3211_);
v___x_3221_ = lean_array_push(v_vs_3214_, v_x_3212_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 1, v___x_3221_);
lean_ctor_set(v___x_3216_, 0, v___x_3220_);
v___x_3223_ = v___x_3216_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
else
{
lean_object* v_k_x27_3225_; uint8_t v___x_3226_; 
v_k_x27_3225_ = lean_array_fget_borrowed(v_ks_3213_, v_x_3210_);
v___x_3226_ = l_Lean_instBEqMVarId_beq(v_x_3211_, v_k_x27_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3228_; 
if (v_isShared_3217_ == 0)
{
v___x_3228_ = v___x_3216_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_ks_3213_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_vs_3214_);
v___x_3228_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = lean_unsigned_to_nat(1u);
v___x_3230_ = lean_nat_add(v_x_3210_, v___x_3229_);
lean_dec(v_x_3210_);
v_x_3209_ = v___x_3228_;
v_x_3210_ = v___x_3230_;
goto _start;
}
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3233_ = lean_array_fset(v_ks_3213_, v_x_3210_, v_x_3211_);
v___x_3234_ = lean_array_fset(v_vs_3214_, v_x_3210_, v_x_3212_);
lean_dec(v_x_3210_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 1, v___x_3234_);
lean_ctor_set(v___x_3216_, 0, v___x_3233_);
v___x_3236_ = v___x_3216_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3239_, lean_object* v_k_3240_, lean_object* v_v_3241_){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = lean_unsigned_to_nat(0u);
v___x_3243_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3239_, v___x_3242_, v_k_3240_, v_v_3241_);
return v___x_3243_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_3244_; size_t v___x_3245_; size_t v___x_3246_; 
v___x_3244_ = ((size_t)5ULL);
v___x_3245_ = ((size_t)1ULL);
v___x_3246_ = lean_usize_shift_left(v___x_3245_, v___x_3244_);
return v___x_3246_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_3247_; size_t v___x_3248_; size_t v___x_3249_; 
v___x_3247_ = ((size_t)1ULL);
v___x_3248_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3249_ = lean_usize_sub(v___x_3248_, v___x_3247_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3251_, size_t v_x_3252_, size_t v_x_3253_, lean_object* v_x_3254_, lean_object* v_x_3255_){
_start:
{
if (lean_obj_tag(v_x_3251_) == 0)
{
lean_object* v_es_3256_; size_t v___x_3257_; size_t v___x_3258_; size_t v___x_3259_; size_t v___x_3260_; lean_object* v_j_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v_es_3256_ = lean_ctor_get(v_x_3251_, 0);
v___x_3257_ = ((size_t)5ULL);
v___x_3258_ = ((size_t)1ULL);
v___x_3259_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3260_ = lean_usize_land(v_x_3252_, v___x_3259_);
v_j_3261_ = lean_usize_to_nat(v___x_3260_);
v___x_3262_ = lean_array_get_size(v_es_3256_);
v___x_3263_ = lean_nat_dec_lt(v_j_3261_, v___x_3262_);
if (v___x_3263_ == 0)
{
lean_dec(v_j_3261_);
lean_dec(v_x_3255_);
lean_dec(v_x_3254_);
return v_x_3251_;
}
else
{
lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3300_; 
lean_inc_ref(v_es_3256_);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_x_3251_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; 
v_unused_3301_ = lean_ctor_get(v_x_3251_, 0);
lean_dec(v_unused_3301_);
v___x_3265_ = v_x_3251_;
v_isShared_3266_ = v_isSharedCheck_3300_;
goto v_resetjp_3264_;
}
else
{
lean_dec(v_x_3251_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3300_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_v_3267_; lean_object* v___x_3268_; lean_object* v_xs_x27_3269_; lean_object* v___y_3271_; 
v_v_3267_ = lean_array_fget(v_es_3256_, v_j_3261_);
v___x_3268_ = lean_box(0);
v_xs_x27_3269_ = lean_array_fset(v_es_3256_, v_j_3261_, v___x_3268_);
switch(lean_obj_tag(v_v_3267_))
{
case 0:
{
lean_object* v_key_3276_; lean_object* v_val_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3287_; 
v_key_3276_ = lean_ctor_get(v_v_3267_, 0);
v_val_3277_ = lean_ctor_get(v_v_3267_, 1);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_v_3267_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3279_ = v_v_3267_;
v_isShared_3280_ = v_isSharedCheck_3287_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_val_3277_);
lean_inc(v_key_3276_);
lean_dec(v_v_3267_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3287_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
uint8_t v___x_3281_; 
v___x_3281_ = l_Lean_instBEqMVarId_beq(v_x_3254_, v_key_3276_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_del_object(v___x_3279_);
v___x_3282_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3276_, v_val_3277_, v_x_3254_, v_x_3255_);
v___x_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
v___y_3271_ = v___x_3283_;
goto v___jp_3270_;
}
else
{
lean_object* v___x_3285_; 
lean_dec(v_val_3277_);
lean_dec(v_key_3276_);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 1, v_x_3255_);
lean_ctor_set(v___x_3279_, 0, v_x_3254_);
v___x_3285_ = v___x_3279_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_x_3254_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_x_3255_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
v___y_3271_ = v___x_3285_;
goto v___jp_3270_;
}
}
}
}
case 1:
{
lean_object* v_node_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3298_; 
v_node_3288_ = lean_ctor_get(v_v_3267_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_v_3267_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3290_ = v_v_3267_;
v_isShared_3291_ = v_isSharedCheck_3298_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_node_3288_);
lean_dec(v_v_3267_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3298_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
size_t v___x_3292_; size_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3292_ = lean_usize_shift_right(v_x_3252_, v___x_3257_);
v___x_3293_ = lean_usize_add(v_x_3253_, v___x_3258_);
v___x_3294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3288_, v___x_3292_, v___x_3293_, v_x_3254_, v_x_3255_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3294_);
v___x_3296_ = v___x_3290_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
v___y_3271_ = v___x_3296_;
goto v___jp_3270_;
}
}
}
default: 
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v_x_3254_);
lean_ctor_set(v___x_3299_, 1, v_x_3255_);
v___y_3271_ = v___x_3299_;
goto v___jp_3270_;
}
}
v___jp_3270_:
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3272_ = lean_array_fset(v_xs_x27_3269_, v_j_3261_, v___y_3271_);
lean_dec(v_j_3261_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v___x_3272_);
v___x_3274_ = v___x_3265_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
else
{
lean_object* v_ks_3302_; lean_object* v_vs_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3323_; 
v_ks_3302_ = lean_ctor_get(v_x_3251_, 0);
v_vs_3303_ = lean_ctor_get(v_x_3251_, 1);
v_isSharedCheck_3323_ = !lean_is_exclusive(v_x_3251_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3305_ = v_x_3251_;
v_isShared_3306_ = v_isSharedCheck_3323_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_vs_3303_);
lean_inc(v_ks_3302_);
lean_dec(v_x_3251_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3323_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_ks_3302_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_vs_3303_);
v___x_3308_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v_newNode_3309_; uint8_t v___y_3311_; size_t v___x_3317_; uint8_t v___x_3318_; 
v_newNode_3309_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3308_, v_x_3254_, v_x_3255_);
v___x_3317_ = ((size_t)7ULL);
v___x_3318_ = lean_usize_dec_le(v___x_3317_, v_x_3253_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3319_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3309_);
v___x_3320_ = lean_unsigned_to_nat(4u);
v___x_3321_ = lean_nat_dec_lt(v___x_3319_, v___x_3320_);
lean_dec(v___x_3319_);
v___y_3311_ = v___x_3321_;
goto v___jp_3310_;
}
else
{
v___y_3311_ = v___x_3318_;
goto v___jp_3310_;
}
v___jp_3310_:
{
if (v___y_3311_ == 0)
{
lean_object* v_ks_3312_; lean_object* v_vs_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_ks_3312_ = lean_ctor_get(v_newNode_3309_, 0);
lean_inc_ref(v_ks_3312_);
v_vs_3313_ = lean_ctor_get(v_newNode_3309_, 1);
lean_inc_ref(v_vs_3313_);
lean_dec_ref(v_newNode_3309_);
v___x_3314_ = lean_unsigned_to_nat(0u);
v___x_3315_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_3316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3253_, v_ks_3312_, v_vs_3313_, v___x_3314_, v___x_3315_);
lean_dec_ref(v_vs_3313_);
lean_dec_ref(v_ks_3312_);
return v___x_3316_;
}
else
{
return v_newNode_3309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3324_, lean_object* v_keys_3325_, lean_object* v_vals_3326_, lean_object* v_i_3327_, lean_object* v_entries_3328_){
_start:
{
lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___x_3329_ = lean_array_get_size(v_keys_3325_);
v___x_3330_ = lean_nat_dec_lt(v_i_3327_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_dec(v_i_3327_);
return v_entries_3328_;
}
else
{
lean_object* v_k_3331_; lean_object* v_v_3332_; uint64_t v___x_3333_; size_t v_h_3334_; size_t v___x_3335_; lean_object* v___x_3336_; size_t v___x_3337_; size_t v___x_3338_; size_t v___x_3339_; size_t v_h_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_k_3331_ = lean_array_fget_borrowed(v_keys_3325_, v_i_3327_);
v_v_3332_ = lean_array_fget_borrowed(v_vals_3326_, v_i_3327_);
v___x_3333_ = l_Lean_instHashableMVarId_hash(v_k_3331_);
v_h_3334_ = lean_uint64_to_usize(v___x_3333_);
v___x_3335_ = ((size_t)5ULL);
v___x_3336_ = lean_unsigned_to_nat(1u);
v___x_3337_ = ((size_t)1ULL);
v___x_3338_ = lean_usize_sub(v_depth_3324_, v___x_3337_);
v___x_3339_ = lean_usize_mul(v___x_3335_, v___x_3338_);
v_h_3340_ = lean_usize_shift_right(v_h_3334_, v___x_3339_);
v___x_3341_ = lean_nat_add(v_i_3327_, v___x_3336_);
lean_dec(v_i_3327_);
lean_inc(v_v_3332_);
lean_inc(v_k_3331_);
v___x_3342_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3328_, v_h_3340_, v_depth_3324_, v_k_3331_, v_v_3332_);
v_i_3327_ = v___x_3341_;
v_entries_3328_ = v___x_3342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3344_, lean_object* v_keys_3345_, lean_object* v_vals_3346_, lean_object* v_i_3347_, lean_object* v_entries_3348_){
_start:
{
size_t v_depth_boxed_3349_; lean_object* v_res_3350_; 
v_depth_boxed_3349_ = lean_unbox_usize(v_depth_3344_);
lean_dec(v_depth_3344_);
v_res_3350_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3349_, v_keys_3345_, v_vals_3346_, v_i_3347_, v_entries_3348_);
lean_dec_ref(v_vals_3346_);
lean_dec_ref(v_keys_3345_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_, lean_object* v_x_3355_){
_start:
{
size_t v_x_5146__boxed_3356_; size_t v_x_5147__boxed_3357_; lean_object* v_res_3358_; 
v_x_5146__boxed_3356_ = lean_unbox_usize(v_x_3352_);
lean_dec(v_x_3352_);
v_x_5147__boxed_3357_ = lean_unbox_usize(v_x_3353_);
lean_dec(v_x_3353_);
v_res_3358_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3351_, v_x_5146__boxed_3356_, v_x_5147__boxed_3357_, v_x_3354_, v_x_3355_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3359_, lean_object* v_x_3360_, lean_object* v_x_3361_){
_start:
{
uint64_t v___x_3362_; size_t v___x_3363_; size_t v___x_3364_; lean_object* v___x_3365_; 
v___x_3362_ = l_Lean_instHashableMVarId_hash(v_x_3360_);
v___x_3363_ = lean_uint64_to_usize(v___x_3362_);
v___x_3364_ = ((size_t)1ULL);
v___x_3365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3359_, v___x_3363_, v___x_3364_, v_x_3360_, v_x_3361_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3366_, lean_object* v_val_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v___x_3370_; lean_object* v_mctx_3371_; lean_object* v_cache_3372_; lean_object* v_zetaDeltaFVarIds_3373_; lean_object* v_postponed_3374_; lean_object* v_diag_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3402_; 
v___x_3370_ = lean_st_ref_take(v___y_3368_);
v_mctx_3371_ = lean_ctor_get(v___x_3370_, 0);
v_cache_3372_ = lean_ctor_get(v___x_3370_, 1);
v_zetaDeltaFVarIds_3373_ = lean_ctor_get(v___x_3370_, 2);
v_postponed_3374_ = lean_ctor_get(v___x_3370_, 3);
v_diag_3375_ = lean_ctor_get(v___x_3370_, 4);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3377_ = v___x_3370_;
v_isShared_3378_ = v_isSharedCheck_3402_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_diag_3375_);
lean_inc(v_postponed_3374_);
lean_inc(v_zetaDeltaFVarIds_3373_);
lean_inc(v_cache_3372_);
lean_inc(v_mctx_3371_);
lean_dec(v___x_3370_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3402_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v_depth_3379_; lean_object* v_levelAssignDepth_3380_; lean_object* v_mvarCounter_3381_; lean_object* v_lDepth_3382_; lean_object* v_decls_3383_; lean_object* v_userNames_3384_; lean_object* v_lAssignment_3385_; lean_object* v_eAssignment_3386_; lean_object* v_dAssignment_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3401_; 
v_depth_3379_ = lean_ctor_get(v_mctx_3371_, 0);
v_levelAssignDepth_3380_ = lean_ctor_get(v_mctx_3371_, 1);
v_mvarCounter_3381_ = lean_ctor_get(v_mctx_3371_, 2);
v_lDepth_3382_ = lean_ctor_get(v_mctx_3371_, 3);
v_decls_3383_ = lean_ctor_get(v_mctx_3371_, 4);
v_userNames_3384_ = lean_ctor_get(v_mctx_3371_, 5);
v_lAssignment_3385_ = lean_ctor_get(v_mctx_3371_, 6);
v_eAssignment_3386_ = lean_ctor_get(v_mctx_3371_, 7);
v_dAssignment_3387_ = lean_ctor_get(v_mctx_3371_, 8);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_mctx_3371_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3389_ = v_mctx_3371_;
v_isShared_3390_ = v_isSharedCheck_3401_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_dAssignment_3387_);
lean_inc(v_eAssignment_3386_);
lean_inc(v_lAssignment_3385_);
lean_inc(v_userNames_3384_);
lean_inc(v_decls_3383_);
lean_inc(v_lDepth_3382_);
lean_inc(v_mvarCounter_3381_);
lean_inc(v_levelAssignDepth_3380_);
lean_inc(v_depth_3379_);
lean_dec(v_mctx_3371_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3401_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3391_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3386_, v_mvarId_3366_, v_val_3367_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 7, v___x_3391_);
v___x_3393_ = v___x_3389_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_depth_3379_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_levelAssignDepth_3380_);
lean_ctor_set(v_reuseFailAlloc_3400_, 2, v_mvarCounter_3381_);
lean_ctor_set(v_reuseFailAlloc_3400_, 3, v_lDepth_3382_);
lean_ctor_set(v_reuseFailAlloc_3400_, 4, v_decls_3383_);
lean_ctor_set(v_reuseFailAlloc_3400_, 5, v_userNames_3384_);
lean_ctor_set(v_reuseFailAlloc_3400_, 6, v_lAssignment_3385_);
lean_ctor_set(v_reuseFailAlloc_3400_, 7, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3400_, 8, v_dAssignment_3387_);
v___x_3393_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
lean_object* v___x_3395_; 
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v___x_3393_);
v___x_3395_ = v___x_3377_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3393_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_cache_3372_);
lean_ctor_set(v_reuseFailAlloc_3399_, 2, v_zetaDeltaFVarIds_3373_);
lean_ctor_set(v_reuseFailAlloc_3399_, 3, v_postponed_3374_);
lean_ctor_set(v_reuseFailAlloc_3399_, 4, v_diag_3375_);
v___x_3395_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = lean_st_ref_set(v___y_3368_, v___x_3395_);
v___x_3397_ = lean_box(0);
v___x_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
return v___x_3398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3403_, lean_object* v_val_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3403_, v_val_3404_, v___y_3405_);
lean_dec(v___y_3405_);
return v_res_3407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_box(0);
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3415_ = l_Lean_mkConst(v___x_3414_, v___x_3413_);
return v___x_3415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3422_ = l_Lean_stringToMessageData(v___x_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3423_, lean_object* v_xs_3424_, lean_object* v_type_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_box(0);
lean_inc_ref(v___y_3426_);
v___x_3432_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3425_, v___x_3431_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; uint8_t v___x_3438_; lean_object* v___y_3440_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref(v___x_3432_);
v___x_3434_ = l_Lean_Expr_mvarId_x21(v_a_3433_);
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3437_ = 1;
v___x_3438_ = 0;
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3452_ = lean_box(0);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc(v___y_3427_);
lean_inc_ref(v___y_3426_);
v___x_3453_ = l_Lean_MVarId_apply(v___x_3434_, v___x_3436_, v___x_3451_, v___x_3452_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
if (lean_obj_tag(v_a_3454_) == 1)
{
lean_object* v_tail_3468_; 
v_tail_3468_ = lean_ctor_get(v_a_3454_, 1);
lean_inc(v_tail_3468_);
if (lean_obj_tag(v_tail_3468_) == 1)
{
lean_object* v_tail_3469_; 
v_tail_3469_ = lean_ctor_get(v_tail_3468_, 1);
if (lean_obj_tag(v_tail_3469_) == 0)
{
lean_object* v_toConstantVal_3470_; lean_object* v_head_3471_; lean_object* v_head_3472_; lean_object* v_name_3473_; lean_object* v_levelParams_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v_toConstantVal_3470_ = lean_ctor_get(v_ctorVal_3423_, 0);
lean_inc_ref(v_toConstantVal_3470_);
lean_dec_ref(v_ctorVal_3423_);
v_head_3471_ = lean_ctor_get(v_a_3454_, 0);
lean_inc(v_head_3471_);
lean_dec_ref(v_a_3454_);
v_head_3472_ = lean_ctor_get(v_tail_3468_, 0);
lean_inc(v_head_3472_);
lean_dec_ref(v_tail_3468_);
v_name_3473_ = lean_ctor_get(v_toConstantVal_3470_, 0);
lean_inc(v_name_3473_);
v_levelParams_3474_ = lean_ctor_get(v_toConstantVal_3470_, 1);
lean_inc(v_levelParams_3474_);
lean_dec_ref(v_toConstantVal_3470_);
lean_inc(v_name_3473_);
v___x_3475_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3473_);
v___x_3476_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3474_, v___x_3435_);
v___x_3477_ = l_Lean_mkConst(v___x_3475_, v___x_3476_);
v___x_3478_ = l_Lean_mkAppN(v___x_3477_, v_xs_3424_);
v___x_3479_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3471_, v___x_3478_, v___y_3427_);
lean_dec_ref(v___x_3479_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc(v___y_3427_);
lean_inc_ref(v___y_3426_);
v___x_3480_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_head_3472_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3482_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___x_3480_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc(v___y_3427_);
lean_inc_ref(v___y_3426_);
v___x_3482_ = l_Lean_MVarId_refl(v_a_3481_, v___x_3437_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_dec(v_name_3473_);
v___y_3440_ = v___x_3482_;
goto v___jp_3439_;
}
else
{
lean_object* v_a_3483_; uint8_t v___y_3485_; uint8_t v___x_3488_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
lean_inc(v_a_3483_);
v___x_3488_ = l_Lean_Exception_isInterrupt(v_a_3483_);
if (v___x_3488_ == 0)
{
uint8_t v___x_3489_; 
v___x_3489_ = l_Lean_Exception_isRuntime(v_a_3483_);
v___y_3485_ = v___x_3489_;
goto v___jp_3484_;
}
else
{
lean_dec(v_a_3483_);
v___y_3485_ = v___x_3488_;
goto v___jp_3484_;
}
v___jp_3484_:
{
if (v___y_3485_ == 0)
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec_ref(v___x_3482_);
v___x_3486_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3473_);
v___x_3487_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3486_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
v___y_3440_ = v___x_3487_;
goto v___jp_3439_;
}
else
{
lean_dec(v_name_3473_);
v___y_3440_ = v___x_3482_;
goto v___jp_3439_;
}
}
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec(v_name_3473_);
lean_dec(v_a_3433_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
v_a_3490_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3480_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3480_);
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
}
else
{
lean_dec_ref(v_tail_3468_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3433_);
v___y_3456_ = v___y_3426_;
v___y_3457_ = v___y_3427_;
v___y_3458_ = v___y_3428_;
v___y_3459_ = v___y_3429_;
goto v___jp_3455_;
}
}
else
{
lean_dec(v_tail_3468_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3433_);
v___y_3456_ = v___y_3426_;
v___y_3457_ = v___y_3427_;
v___y_3458_ = v___y_3428_;
v___y_3459_ = v___y_3429_;
goto v___jp_3455_;
}
}
else
{
lean_dec(v_a_3454_);
lean_dec(v_a_3433_);
v___y_3456_ = v___y_3426_;
v___y_3457_ = v___y_3427_;
v___y_3458_ = v___y_3428_;
v___y_3459_ = v___y_3429_;
goto v___jp_3455_;
}
v___jp_3455_:
{
lean_object* v_toConstantVal_3460_; lean_object* v_name_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_toConstantVal_3460_ = lean_ctor_get(v_ctorVal_3423_, 0);
lean_inc_ref(v_toConstantVal_3460_);
lean_dec_ref(v_ctorVal_3423_);
v_name_3461_ = lean_ctor_get(v_toConstantVal_3460_, 0);
lean_inc(v_name_3461_);
lean_dec_ref(v_toConstantVal_3460_);
v___x_3462_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3463_ = l_Lean_MessageData_ofName(v_name_3461_);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3466_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v___x_3467_;
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec(v_a_3433_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec_ref(v_ctorVal_3423_);
v_a_3498_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3453_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3453_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
v___jp_3439_:
{
if (lean_obj_tag(v___y_3440_) == 0)
{
uint8_t v___x_3441_; lean_object* v___x_3442_; 
lean_dec_ref(v___y_3440_);
v___x_3441_ = 1;
v___x_3442_ = l_Lean_Meta_mkLambdaFVars(v_xs_3424_, v_a_3433_, v___x_3438_, v___x_3437_, v___x_3438_, v___x_3437_, v___x_3441_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
return v___x_3442_;
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v_a_3433_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
v_a_3443_ = lean_ctor_get(v___y_3440_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___y_3440_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___y_3440_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___y_3440_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
else
{
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec_ref(v_ctorVal_3423_);
return v___x_3432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3506_, lean_object* v_xs_3507_, lean_object* v_type_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3506_, v_xs_3507_, v_type_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec_ref(v_xs_3507_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3515_, lean_object* v_targetType_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v___f_3522_; uint8_t v___x_3523_; lean_object* v___x_3524_; 
v___f_3522_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3522_, 0, v_ctorVal_3515_);
v___x_3523_ = 0;
v___x_3524_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3516_, v___f_3522_, v___x_3523_, v___x_3523_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3525_, lean_object* v_targetType_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3525_, v_targetType_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3533_, lean_object* v_val_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3533_, v_val_3534_, v___y_3536_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3541_, lean_object* v_val_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3541_, v_val_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3549_, lean_object* v_x_3550_, lean_object* v_x_3551_, lean_object* v_x_3552_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3550_, v_x_3551_, v_x_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3554_, lean_object* v_x_3555_, size_t v_x_3556_, size_t v_x_3557_, lean_object* v_x_3558_, lean_object* v_x_3559_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3555_, v_x_3556_, v_x_3557_, v_x_3558_, v_x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3561_, lean_object* v_x_3562_, lean_object* v_x_3563_, lean_object* v_x_3564_, lean_object* v_x_3565_, lean_object* v_x_3566_){
_start:
{
size_t v_x_5622__boxed_3567_; size_t v_x_5623__boxed_3568_; lean_object* v_res_3569_; 
v_x_5622__boxed_3567_ = lean_unbox_usize(v_x_3563_);
lean_dec(v_x_3563_);
v_x_5623__boxed_3568_ = lean_unbox_usize(v_x_3564_);
lean_dec(v_x_3564_);
v_res_3569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3561_, v_x_3562_, v_x_5622__boxed_3567_, v_x_5623__boxed_3568_, v_x_3565_, v_x_3566_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3570_, lean_object* v_n_3571_, lean_object* v_k_3572_, lean_object* v_v_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3571_, v_k_3572_, v_v_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3575_, size_t v_depth_3576_, lean_object* v_keys_3577_, lean_object* v_vals_3578_, lean_object* v_heq_3579_, lean_object* v_i_3580_, lean_object* v_entries_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3576_, v_keys_3577_, v_vals_3578_, v_i_3580_, v_entries_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3583_, lean_object* v_depth_3584_, lean_object* v_keys_3585_, lean_object* v_vals_3586_, lean_object* v_heq_3587_, lean_object* v_i_3588_, lean_object* v_entries_3589_){
_start:
{
size_t v_depth_boxed_3590_; lean_object* v_res_3591_; 
v_depth_boxed_3590_ = lean_unbox_usize(v_depth_3584_);
lean_dec(v_depth_3584_);
v_res_3591_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3583_, v_depth_boxed_3590_, v_keys_3585_, v_vals_3586_, v_heq_3587_, v_i_3588_, v_entries_3589_);
lean_dec_ref(v_vals_3586_);
lean_dec_ref(v_keys_3585_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3592_, lean_object* v_x_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_, lean_object* v_x_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3593_, v_x_3594_, v_x_3595_, v_x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3598_, lean_object* v_val_3599_, lean_object* v_name_3600_, lean_object* v_levelParams_3601_, uint8_t v___x_3602_, uint8_t v_hasTrace_3603_, lean_object* v_____r_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; 
lean_inc(v___y_3608_);
lean_inc_ref(v___y_3607_);
lean_inc(v___y_3606_);
lean_inc_ref(v___y_3605_);
lean_inc_ref(v_val_3599_);
v___x_3610_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3598_, v_val_3599_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v_a_3613_; lean_object* v___x_3614_; lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3631_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3610_);
v___x_3612_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3599_, v___y_3606_);
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref(v___x_3612_);
v___x_3614_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3611_, v___y_3606_);
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3631_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3631_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3624_; 
lean_inc(v_name_3600_);
v___x_3619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3619_, 0, v_name_3600_);
lean_ctor_set(v___x_3619_, 1, v_levelParams_3601_);
lean_ctor_set(v___x_3619_, 2, v_a_3613_);
v___x_3620_ = lean_box(0);
lean_inc(v_name_3600_);
v___x_3621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3621_, 0, v_name_3600_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3619_);
lean_ctor_set(v___x_3622_, 1, v_a_3615_);
lean_ctor_set(v___x_3622_, 2, v___x_3621_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 2);
lean_ctor_set(v___x_3617_, 0, v___x_3622_);
v___x_3624_ = v___x_3617_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3625_; 
lean_inc(v___y_3608_);
lean_inc_ref(v___y_3607_);
v___x_3625_ = l_Lean_addDecl(v___x_3624_, v___x_3602_, v___y_3607_, v___y_3608_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v___x_3626_; uint8_t v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
lean_dec_ref(v___x_3625_);
v___x_3626_ = l_Lean_Meta_simpExtension;
v___x_3627_ = 0;
v___x_3628_ = lean_unsigned_to_nat(1000u);
v___x_3629_ = l_Lean_Meta_addSimpTheorem(v___x_3626_, v_name_3600_, v_hasTrace_3603_, v___x_3602_, v___x_3627_, v___x_3628_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
return v___x_3629_;
}
else
{
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v_name_3600_);
return v___x_3625_;
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v_levelParams_3601_);
lean_dec(v_name_3600_);
lean_dec_ref(v_val_3599_);
v_a_3632_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3610_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3610_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3640_, lean_object* v_val_3641_, lean_object* v_name_3642_, lean_object* v_levelParams_3643_, lean_object* v___x_3644_, lean_object* v_hasTrace_3645_, lean_object* v_____r_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
uint8_t v___x_6804__boxed_3652_; uint8_t v_hasTrace_boxed_3653_; lean_object* v_res_3654_; 
v___x_6804__boxed_3652_ = lean_unbox(v___x_3644_);
v_hasTrace_boxed_3653_ = lean_unbox(v_hasTrace_3645_);
v_res_3654_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3640_, v_val_3641_, v_name_3642_, v_levelParams_3643_, v___x_6804__boxed_3652_, v_hasTrace_boxed_3653_, v_____r_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3655_, lean_object* v_val_3656_, lean_object* v_name_3657_, lean_object* v_levelParams_3658_, uint8_t v___x_3659_, lean_object* v_____r_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v___x_3666_; 
lean_inc(v___y_3664_);
lean_inc_ref(v___y_3663_);
lean_inc(v___y_3662_);
lean_inc_ref(v___y_3661_);
lean_inc_ref(v_val_3656_);
v___x_3666_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3655_, v_val_3656_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; lean_object* v_a_3669_; lean_object* v___x_3670_; lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3688_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref(v___x_3666_);
v___x_3668_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3656_, v___y_3662_);
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref(v___x_3668_);
v___x_3670_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3667_, v___y_3662_);
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3688_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3688_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
lean_inc(v_name_3657_);
v___x_3675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3675_, 0, v_name_3657_);
lean_ctor_set(v___x_3675_, 1, v_levelParams_3658_);
lean_ctor_set(v___x_3675_, 2, v_a_3669_);
v___x_3676_ = lean_box(0);
lean_inc(v_name_3657_);
v___x_3677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3677_, 0, v_name_3657_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3675_);
lean_ctor_set(v___x_3678_, 1, v_a_3671_);
lean_ctor_set(v___x_3678_, 2, v___x_3677_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set_tag(v___x_3673_, 2);
lean_ctor_set(v___x_3673_, 0, v___x_3678_);
v___x_3680_ = v___x_3673_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
uint8_t v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = 0;
lean_inc(v___y_3664_);
lean_inc_ref(v___y_3663_);
v___x_3682_ = l_Lean_addDecl(v___x_3680_, v___x_3681_, v___y_3663_, v___y_3664_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v___x_3683_; uint8_t v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
lean_dec_ref(v___x_3682_);
v___x_3683_ = l_Lean_Meta_simpExtension;
v___x_3684_ = 0;
v___x_3685_ = lean_unsigned_to_nat(1000u);
v___x_3686_ = l_Lean_Meta_addSimpTheorem(v___x_3683_, v_name_3657_, v___x_3659_, v___x_3681_, v___x_3684_, v___x_3685_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
return v___x_3686_;
}
else
{
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v_name_3657_);
return v___x_3682_;
}
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v_levelParams_3658_);
lean_dec(v_name_3657_);
lean_dec_ref(v_val_3656_);
v_a_3689_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3666_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3666_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3697_, lean_object* v_val_3698_, lean_object* v_name_3699_, lean_object* v_levelParams_3700_, lean_object* v___x_3701_, lean_object* v_____r_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
uint8_t v___x_6892__boxed_3708_; lean_object* v_res_3709_; 
v___x_6892__boxed_3708_ = lean_unbox(v___x_3701_);
v_res_3709_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3697_, v_val_3698_, v_name_3699_, v_levelParams_3700_, v___x_6892__boxed_3708_, v_____r_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v_toConstantVal_3716_; lean_object* v_options_3717_; lean_object* v_name_3718_; lean_object* v_levelParams_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3966_; 
v_toConstantVal_3716_ = lean_ctor_get(v_ctorVal_3710_, 0);
lean_inc_ref(v_toConstantVal_3716_);
v_options_3717_ = lean_ctor_get(v_a_3713_, 2);
v_name_3718_ = lean_ctor_get(v_toConstantVal_3716_, 0);
v_levelParams_3719_ = lean_ctor_get(v_toConstantVal_3716_, 1);
v_isSharedCheck_3966_ = !lean_is_exclusive(v_toConstantVal_3716_);
if (v_isSharedCheck_3966_ == 0)
{
lean_object* v_unused_3967_; 
v_unused_3967_ = lean_ctor_get(v_toConstantVal_3716_, 2);
lean_dec(v_unused_3967_);
v___x_3721_ = v_toConstantVal_3716_;
v_isShared_3722_ = v_isSharedCheck_3966_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_levelParams_3719_);
lean_inc(v_name_3718_);
lean_dec(v_toConstantVal_3716_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3966_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
uint8_t v_hasTrace_3723_; lean_object* v_name_3724_; lean_object* v_cls_3725_; 
v_hasTrace_3723_ = lean_ctor_get_uint8(v_options_3717_, sizeof(void*)*1);
v_name_3724_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3718_);
v_cls_3725_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
if (v_hasTrace_3723_ == 0)
{
lean_object* v___x_3726_; 
lean_inc(v_a_3714_);
lean_inc_ref(v_a_3713_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc_ref(v_ctorVal_3710_);
v___x_3726_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3781_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3729_ = v___x_3726_;
v_isShared_3730_ = v_isSharedCheck_3781_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3726_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3781_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
if (lean_obj_tag(v_a_3727_) == 1)
{
lean_object* v_val_3731_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___x_3770_; lean_object* v_a_3771_; uint8_t v___x_3772_; 
lean_del_object(v___x_3729_);
v_val_3731_ = lean_ctor_get(v_a_3727_, 0);
lean_inc(v_val_3731_);
lean_dec_ref(v_a_3727_);
v___x_3770_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3725_, v_a_3713_);
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = lean_unbox(v_a_3771_);
lean_dec(v_a_3771_);
if (v___x_3772_ == 0)
{
v___y_3733_ = v_a_3711_;
v___y_3734_ = v_a_3712_;
v___y_3735_ = v_a_3713_;
v___y_3736_ = v_a_3714_;
goto v___jp_3732_;
}
else
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3773_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_3731_);
v___x_3774_ = l_Lean_MessageData_ofExpr(v_val_3731_);
v___x_3775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3773_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_3725_, v___x_3775_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_dec_ref(v___x_3776_);
v___y_3733_ = v_a_3711_;
v___y_3734_ = v_a_3712_;
v___y_3735_ = v_a_3713_;
v___y_3736_ = v_a_3714_;
goto v___jp_3732_;
}
else
{
lean_dec(v_val_3731_);
lean_dec(v_name_3724_);
lean_del_object(v___x_3721_);
lean_dec(v_levelParams_3719_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec_ref(v_ctorVal_3710_);
return v___x_3776_;
}
}
v___jp_3732_:
{
lean_object* v___x_3737_; 
lean_inc(v___y_3736_);
lean_inc_ref(v___y_3735_);
lean_inc(v___y_3734_);
lean_inc_ref(v___y_3733_);
lean_inc(v_val_3731_);
v___x_3737_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3710_, v_val_3731_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; lean_object* v_a_3740_; lean_object* v___x_3741_; lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3761_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___x_3737_);
v___x_3739_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3731_, v___y_3734_);
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref(v___x_3739_);
v___x_3741_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3738_, v___y_3734_);
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3744_ = v___x_3741_;
v_isShared_3745_ = v_isSharedCheck_3761_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3761_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
lean_inc(v_name_3724_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 2, v_a_3740_);
lean_ctor_set(v___x_3721_, 0, v_name_3724_);
v___x_3747_ = v___x_3721_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_name_3724_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_levelParams_3719_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v_a_3740_);
v___x_3747_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3748_ = lean_box(0);
lean_inc(v_name_3724_);
v___x_3749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3749_, 0, v_name_3724_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3747_);
lean_ctor_set(v___x_3750_, 1, v_a_3742_);
lean_ctor_set(v___x_3750_, 2, v___x_3749_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set_tag(v___x_3744_, 2);
lean_ctor_set(v___x_3744_, 0, v___x_3750_);
v___x_3752_ = v___x_3744_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
lean_object* v___x_3753_; 
lean_inc(v___y_3736_);
lean_inc_ref(v___y_3735_);
v___x_3753_ = l_Lean_addDecl(v___x_3752_, v_hasTrace_3723_, v___y_3735_, v___y_3736_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v___x_3754_; uint8_t v___x_3755_; uint8_t v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
lean_dec_ref(v___x_3753_);
v___x_3754_ = l_Lean_Meta_simpExtension;
v___x_3755_ = 1;
v___x_3756_ = 0;
v___x_3757_ = lean_unsigned_to_nat(1000u);
v___x_3758_ = l_Lean_Meta_addSimpTheorem(v___x_3754_, v_name_3724_, v___x_3755_, v_hasTrace_3723_, v___x_3756_, v___x_3757_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
return v___x_3758_;
}
else
{
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v_name_3724_);
return v___x_3753_;
}
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v_val_3731_);
lean_dec(v_name_3724_);
lean_del_object(v___x_3721_);
lean_dec(v_levelParams_3719_);
v_a_3762_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3737_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3737_);
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
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3779_; 
lean_dec(v_a_3727_);
lean_dec(v_name_3724_);
lean_del_object(v___x_3721_);
lean_dec(v_levelParams_3719_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec_ref(v_ctorVal_3710_);
v___x_3777_ = lean_box(0);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3777_);
v___x_3779_ = v___x_3729_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec(v_name_3724_);
lean_del_object(v___x_3721_);
lean_dec(v_levelParams_3719_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec_ref(v_ctorVal_3710_);
v_a_3782_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3726_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3726_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
else
{
lean_object* v___x_3790_; lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3965_; 
v___x_3790_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3725_, v_a_3713_);
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3793_ = v___x_3790_;
v_isShared_3794_ = v_isSharedCheck_3965_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3790_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3965_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___f_3795_; lean_object* v___x_3796_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v_a_3800_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v_a_3813_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v_a_3820_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v_a_3831_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v_a_3847_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v_a_3852_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; uint8_t v___x_3899_; 
lean_inc(v_name_3724_);
v___f_3795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3795_, 0, v_name_3724_);
v___x_3796_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1));
v___x_3899_ = lean_unbox(v_a_3791_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3900_ = l_Lean_trace_profiler;
v___x_3901_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3717_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; 
lean_dec_ref(v___f_3795_);
lean_del_object(v___x_3793_);
lean_dec(v_a_3791_);
lean_inc(v_a_3714_);
lean_inc_ref(v_a_3713_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc_ref(v_ctorVal_3710_);
v___x_3902_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3956_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3956_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3956_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
if (lean_obj_tag(v_a_3903_) == 1)
{
lean_object* v_val_3907_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___x_3945_; lean_object* v_a_3946_; uint8_t v___x_3947_; 
lean_del_object(v___x_3905_);
v_val_3907_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_val_3907_);
lean_dec_ref(v_a_3903_);
v___x_3945_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3725_, v_a_3713_);
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref(v___x_3945_);
v___x_3947_ = lean_unbox(v_a_3946_);
lean_dec(v_a_3946_);
if (v___x_3947_ == 0)
{
v___y_3909_ = v_a_3711_;
v___y_3910_ = v_a_3712_;
v___y_3911_ = v_a_3713_;
v___y_3912_ = v_a_3714_;
goto v___jp_3908_;
}
else
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3948_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_3907_);
v___x_3949_ = l_Lean_MessageData_ofExpr(v_val_3907_);
v___x_3950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
v___x_3951_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_3725_, v___x_3950_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_dec_ref(v___x_3951_);
v___y_3909_ = v_a_3711_;
v___y_3910_ = v_a_3712_;
v___y_3911_ = v_a_3713_;
v___y_3912_ = v_a_3714_;
goto v___jp_3908_;
}
else
{
lean_dec(v_val_3907_);
lean_dec(v_name_3724_);
lean_del_object(v___x_3721_);
lean_dec(v_levelParams_3719_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec_ref(v_ctorVal_3710_);
return v___x_3951_;
}
}
v___jp_3908_:
{
lean_object* v___x_3913_; 
lean_inc(v___y_3912_);
lean_inc_ref(v___y_3911_);
lean_inc(v___y_3910_);
lean_inc_ref(v___y_3909_);
lean_inc(v_val_3907_);
v___x_3913_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3710_, v_val_3907_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3936_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref(v___x_3913_);
v___x_3915_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3907_, v___y_3910_);
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v___x_3915_);
v___x_3917_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3914_, v___y_3910_);
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3936_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3936_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
lean_inc(v_name_3724_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 2, v_a_3916_);
lean_ctor_set(v___x_3721_, 0, v_name_3724_);
v___x_3923_ = v___x_3721_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_name_3724_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_levelParams_3719_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_a_3916_);
v___x_3923_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3924_ = lean_box(0);
lean_inc(v_name_3724_);
v___x_3925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3925_, 0, v_name_3724_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
v___x_3926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3923_);
lean_ctor_set(v___x_3926_, 1, v_a_3918_);
lean_ctor_set(v___x_3926_, 2, v___x_3925_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set_tag(v___x_3920_, 2);
lean_ctor_set(v___x_3920_, 0, v___x_3926_);
v___x_3928_ = v___x_3920_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; 
lean_inc(v___y_3912_);
lean_inc_ref(v___y_3911_);
v___x_3929_ = l_Lean_addDecl(v___x_3928_, v___x_3901_, v___y_3911_, v___y_3912_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v___x_3930_; uint8_t v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec_ref(v___x_3929_);
v___x_3930_ = l_Lean_Meta_simpExtension;
v___x_3931_ = 0;
v___x_3932_ = lean_unsigned_to_nat(1000u);
v___x_3933_ = l_Lean_Meta_addSimpTheorem(v___x_3930_, v_name_3724_, v_hasTrace_3723_, v___x_3901_, v___x_3931_, v___x_3932_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
return v___x_3933_;
}
else
{
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v_name_3724_);
return v___x_3929_;
}
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v_val_3907_);
lean_dec(v_name_3724_);
lean_del_object(v___x_3721_);
lean_dec(v_levelParams_3719_);
v_a_3937_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3913_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3913_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3954_; 
lean_dec(v_a_3903_);
lean_dec(v_name_3724_);
lean_del_object(v___x_3721_);
lean_dec(v_levelParams_3719_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec_ref(v_ctorVal_3710_);
v___x_3952_ = lean_box(0);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3952_);
v___x_3954_ = v___x_3905_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec(v_name_3724_);
lean_del_object(v___x_3721_);
lean_dec(v_levelParams_3719_);
lean_dec(v_a_3714_);
lean_dec_ref(v_a_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_a_3711_);
lean_dec_ref(v_ctorVal_3710_);
v_a_3957_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3902_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3902_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_inc_ref(v_options_3717_);
lean_del_object(v___x_3721_);
goto v___jp_3860_;
}
}
else
{
lean_inc_ref(v_options_3717_);
lean_del_object(v___x_3721_);
goto v___jp_3860_;
}
v___jp_3797_:
{
lean_object* v___x_3801_; double v___x_3802_; double v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; lean_object* v___x_3809_; 
v___x_3801_ = lean_io_get_num_heartbeats();
v___x_3802_ = lean_float_of_nat(v___y_3798_);
v___x_3803_ = lean_float_of_nat(v___x_3801_);
v___x_3804_ = lean_box_float(v___x_3802_);
v___x_3805_ = lean_box_float(v___x_3803_);
v___x_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v_a_3800_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_unbox(v_a_3791_);
lean_dec(v_a_3791_);
v___x_3809_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3725_, v_hasTrace_3723_, v___x_3796_, v_options_3717_, v___x_3808_, v___y_3799_, v___f_3795_, v___x_3807_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
lean_dec_ref(v_options_3717_);
return v___x_3809_;
}
v___jp_3810_:
{
lean_object* v___x_3815_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v_a_3813_);
v___x_3815_ = v___x_3793_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
v___y_3798_ = v___y_3811_;
v___y_3799_ = v___y_3812_;
v_a_3800_ = v___x_3815_;
goto v___jp_3797_;
}
}
v___jp_3817_:
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3821_, 0, v_a_3820_);
v___y_3798_ = v___y_3818_;
v___y_3799_ = v___y_3819_;
v_a_3800_ = v___x_3821_;
goto v___jp_3797_;
}
v___jp_3822_:
{
if (lean_obj_tag(v___y_3825_) == 0)
{
lean_object* v_a_3826_; 
lean_del_object(v___x_3793_);
v_a_3826_ = lean_ctor_get(v___y_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref(v___y_3825_);
v___y_3818_ = v___y_3823_;
v___y_3819_ = v___y_3824_;
v_a_3820_ = v_a_3826_;
goto v___jp_3817_;
}
else
{
lean_object* v_a_3827_; 
v_a_3827_ = lean_ctor_get(v___y_3825_, 0);
lean_inc(v_a_3827_);
lean_dec_ref(v___y_3825_);
v___y_3811_ = v___y_3823_;
v___y_3812_ = v___y_3824_;
v_a_3813_ = v_a_3827_;
goto v___jp_3810_;
}
}
v___jp_3828_:
{
lean_object* v___x_3832_; double v___x_3833_; double v___x_3834_; double v___x_3835_; double v___x_3836_; double v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; lean_object* v___x_3843_; 
v___x_3832_ = lean_io_mono_nanos_now();
v___x_3833_ = lean_float_of_nat(v___y_3829_);
v___x_3834_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3835_ = lean_float_div(v___x_3833_, v___x_3834_);
v___x_3836_ = lean_float_of_nat(v___x_3832_);
v___x_3837_ = lean_float_div(v___x_3836_, v___x_3834_);
v___x_3838_ = lean_box_float(v___x_3835_);
v___x_3839_ = lean_box_float(v___x_3837_);
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3838_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v_a_3831_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
v___x_3842_ = lean_unbox(v_a_3791_);
lean_dec(v_a_3791_);
v___x_3843_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3725_, v_hasTrace_3723_, v___x_3796_, v_options_3717_, v___x_3842_, v___y_3830_, v___f_3795_, v___x_3841_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
lean_dec_ref(v_options_3717_);
return v___x_3843_;
}
v___jp_3844_:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3848_, 0, v_a_3847_);
v___y_3829_ = v___y_3845_;
v___y_3830_ = v___y_3846_;
v_a_3831_ = v___x_3848_;
goto v___jp_3828_;
}
v___jp_3849_:
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_a_3852_);
v___y_3829_ = v___y_3850_;
v___y_3830_ = v___y_3851_;
v_a_3831_ = v___x_3853_;
goto v___jp_3828_;
}
v___jp_3854_:
{
if (lean_obj_tag(v___y_3857_) == 0)
{
lean_object* v_a_3858_; 
v_a_3858_ = lean_ctor_get(v___y_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref(v___y_3857_);
v___y_3845_ = v___y_3855_;
v___y_3846_ = v___y_3856_;
v_a_3847_ = v_a_3858_;
goto v___jp_3844_;
}
else
{
lean_object* v_a_3859_; 
v_a_3859_ = lean_ctor_get(v___y_3857_, 0);
lean_inc(v_a_3859_);
lean_dec_ref(v___y_3857_);
v___y_3850_ = v___y_3855_;
v___y_3851_ = v___y_3856_;
v_a_3852_ = v_a_3859_;
goto v___jp_3849_;
}
}
v___jp_3860_:
{
lean_object* v___x_3861_; lean_object* v_a_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3861_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3714_);
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref(v___x_3861_);
v___x_3863_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3864_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3717_, v___x_3863_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_del_object(v___x_3793_);
v___x_3865_ = lean_io_mono_nanos_now();
lean_inc(v_a_3714_);
lean_inc_ref(v_a_3713_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc_ref(v_ctorVal_3710_);
v___x_3866_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3866_);
if (lean_obj_tag(v_a_3867_) == 1)
{
lean_object* v_val_3868_; lean_object* v___x_3869_; lean_object* v_a_3870_; uint8_t v___x_3871_; 
v_val_3868_ = lean_ctor_get(v_a_3867_, 0);
lean_inc(v_val_3868_);
lean_dec_ref(v_a_3867_);
v___x_3869_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3725_, v_a_3713_);
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref(v___x_3869_);
v___x_3871_ = lean_unbox(v_a_3870_);
lean_dec(v_a_3870_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = lean_box(0);
lean_inc(v_a_3714_);
lean_inc_ref(v_a_3713_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
v___x_3873_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3710_, v_val_3868_, v_name_3724_, v_levelParams_3719_, v___x_3864_, v_hasTrace_3723_, v___x_3872_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
v___y_3855_ = v___x_3865_;
v___y_3856_ = v_a_3862_;
v___y_3857_ = v___x_3873_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3874_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_3868_);
v___x_3875_ = l_Lean_MessageData_ofExpr(v_val_3868_);
v___x_3876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3874_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
v___x_3877_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_3725_, v___x_3876_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3879_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref(v___x_3877_);
lean_inc(v_a_3714_);
lean_inc_ref(v_a_3713_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
v___x_3879_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3710_, v_val_3868_, v_name_3724_, v_levelParams_3719_, v___x_3864_, v_hasTrace_3723_, v_a_3878_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
v___y_3855_ = v___x_3865_;
v___y_3856_ = v_a_3862_;
v___y_3857_ = v___x_3879_;
goto v___jp_3854_;
}
else
{
lean_dec(v_val_3868_);
lean_dec(v_name_3724_);
lean_dec(v_levelParams_3719_);
lean_dec_ref(v_ctorVal_3710_);
v___y_3855_ = v___x_3865_;
v___y_3856_ = v_a_3862_;
v___y_3857_ = v___x_3877_;
goto v___jp_3854_;
}
}
}
else
{
lean_object* v___x_3880_; 
lean_dec(v_a_3867_);
lean_dec(v_name_3724_);
lean_dec(v_levelParams_3719_);
lean_dec_ref(v_ctorVal_3710_);
v___x_3880_ = lean_box(0);
v___y_3845_ = v___x_3865_;
v___y_3846_ = v_a_3862_;
v_a_3847_ = v___x_3880_;
goto v___jp_3844_;
}
}
else
{
lean_object* v_a_3881_; 
lean_dec(v_name_3724_);
lean_dec(v_levelParams_3719_);
lean_dec_ref(v_ctorVal_3710_);
v_a_3881_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3881_);
lean_dec_ref(v___x_3866_);
v___y_3850_ = v___x_3865_;
v___y_3851_ = v_a_3862_;
v_a_3852_ = v_a_3881_;
goto v___jp_3849_;
}
}
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3714_);
lean_inc_ref(v_a_3713_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
lean_inc_ref(v_ctorVal_3710_);
v___x_3883_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref(v___x_3883_);
if (lean_obj_tag(v_a_3884_) == 1)
{
lean_object* v_val_3885_; lean_object* v___x_3886_; lean_object* v_a_3887_; uint8_t v___x_3888_; 
v_val_3885_ = lean_ctor_get(v_a_3884_, 0);
lean_inc(v_val_3885_);
lean_dec_ref(v_a_3884_);
v___x_3886_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3725_, v_a_3713_);
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref(v___x_3886_);
v___x_3888_ = lean_unbox(v_a_3887_);
lean_dec(v_a_3887_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_box(0);
lean_inc(v_a_3714_);
lean_inc_ref(v_a_3713_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
v___x_3890_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3710_, v_val_3885_, v_name_3724_, v_levelParams_3719_, v___x_3864_, v___x_3889_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
v___y_3823_ = v___x_3882_;
v___y_3824_ = v_a_3862_;
v___y_3825_ = v___x_3890_;
goto v___jp_3822_;
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3891_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_3885_);
v___x_3892_ = l_Lean_MessageData_ofExpr(v_val_3885_);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_3725_, v___x_3893_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3896_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref(v___x_3894_);
lean_inc(v_a_3714_);
lean_inc_ref(v_a_3713_);
lean_inc(v_a_3712_);
lean_inc_ref(v_a_3711_);
v___x_3896_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3710_, v_val_3885_, v_name_3724_, v_levelParams_3719_, v___x_3864_, v_a_3895_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
v___y_3823_ = v___x_3882_;
v___y_3824_ = v_a_3862_;
v___y_3825_ = v___x_3896_;
goto v___jp_3822_;
}
else
{
lean_dec(v_val_3885_);
lean_dec(v_name_3724_);
lean_dec(v_levelParams_3719_);
lean_dec_ref(v_ctorVal_3710_);
v___y_3823_ = v___x_3882_;
v___y_3824_ = v_a_3862_;
v___y_3825_ = v___x_3894_;
goto v___jp_3822_;
}
}
}
else
{
lean_object* v___x_3897_; 
lean_dec(v_a_3884_);
lean_del_object(v___x_3793_);
lean_dec(v_name_3724_);
lean_dec(v_levelParams_3719_);
lean_dec_ref(v_ctorVal_3710_);
v___x_3897_ = lean_box(0);
v___y_3818_ = v___x_3882_;
v___y_3819_ = v_a_3862_;
v_a_3820_ = v___x_3897_;
goto v___jp_3817_;
}
}
else
{
lean_object* v_a_3898_; 
lean_dec(v_name_3724_);
lean_dec(v_levelParams_3719_);
lean_dec_ref(v_ctorVal_3710_);
v_a_3898_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3898_);
lean_dec_ref(v___x_3883_);
v___y_3811_ = v___x_3882_;
v___y_3812_ = v_a_3862_;
v_a_3813_ = v_a_3898_;
goto v___jp_3810_;
}
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
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3975_, lean_object* v_decl_3976_, lean_object* v_ref_3977_){
_start:
{
lean_object* v_defValue_3979_; lean_object* v_descr_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4007_; 
v_defValue_3979_ = lean_ctor_get(v_decl_3976_, 0);
v_descr_3980_ = lean_ctor_get(v_decl_3976_, 1);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_decl_3976_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3982_ = v_decl_3976_;
v_isShared_3983_ = v_isSharedCheck_4007_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_descr_3980_);
lean_inc(v_defValue_3979_);
lean_dec(v_decl_3976_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4007_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; uint8_t v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3984_ = lean_alloc_ctor(1, 0, 1);
v___x_3985_ = lean_unbox(v_defValue_3979_);
lean_ctor_set_uint8(v___x_3984_, 0, v___x_3985_);
lean_inc(v_name_3975_);
v___x_3986_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3986_, 0, v_name_3975_);
lean_ctor_set(v___x_3986_, 1, v_ref_3977_);
lean_ctor_set(v___x_3986_, 2, v___x_3984_);
lean_ctor_set(v___x_3986_, 3, v_descr_3980_);
lean_inc(v_name_3975_);
v___x_3987_ = lean_register_option(v_name_3975_, v___x_3986_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3997_; 
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3997_ == 0)
{
lean_object* v_unused_3998_; 
v_unused_3998_ = lean_ctor_get(v___x_3987_, 0);
lean_dec(v_unused_3998_);
v___x_3989_ = v___x_3987_;
v_isShared_3990_ = v_isSharedCheck_3997_;
goto v_resetjp_3988_;
}
else
{
lean_dec(v___x_3987_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3997_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 1, v_defValue_3979_);
lean_ctor_set(v___x_3982_, 0, v_name_3975_);
v___x_3992_ = v___x_3982_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_name_3975_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v_defValue_3979_);
v___x_3992_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3994_; 
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v___x_3992_);
v___x_3994_ = v___x_3989_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3992_);
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
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_del_object(v___x_3982_);
lean_dec(v_defValue_3979_);
lean_dec(v_name_3975_);
v_a_3999_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3987_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3987_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4008_, lean_object* v_decl_4009_, lean_object* v_ref_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4008_, v_decl_4009_, v_ref_4010_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4026_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4027_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4028_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4029_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4026_, v___x_4027_, v___x_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4032_, uint8_t v_isExporting_4033_, lean_object* v___x_4034_, lean_object* v___y_4035_, lean_object* v___x_4036_, lean_object* v_a_x3f_4037_){
_start:
{
lean_object* v___x_4039_; lean_object* v_env_4040_; lean_object* v_nextMacroScope_4041_; lean_object* v_ngen_4042_; lean_object* v_auxDeclNGen_4043_; lean_object* v_traceState_4044_; lean_object* v_messages_4045_; lean_object* v_infoState_4046_; lean_object* v_snapshotTasks_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4072_; 
v___x_4039_ = lean_st_ref_take(v___y_4032_);
v_env_4040_ = lean_ctor_get(v___x_4039_, 0);
v_nextMacroScope_4041_ = lean_ctor_get(v___x_4039_, 1);
v_ngen_4042_ = lean_ctor_get(v___x_4039_, 2);
v_auxDeclNGen_4043_ = lean_ctor_get(v___x_4039_, 3);
v_traceState_4044_ = lean_ctor_get(v___x_4039_, 4);
v_messages_4045_ = lean_ctor_get(v___x_4039_, 6);
v_infoState_4046_ = lean_ctor_get(v___x_4039_, 7);
v_snapshotTasks_4047_ = lean_ctor_get(v___x_4039_, 8);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4072_ == 0)
{
lean_object* v_unused_4073_; 
v_unused_4073_ = lean_ctor_get(v___x_4039_, 5);
lean_dec(v_unused_4073_);
v___x_4049_ = v___x_4039_;
v_isShared_4050_ = v_isSharedCheck_4072_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_snapshotTasks_4047_);
lean_inc(v_infoState_4046_);
lean_inc(v_messages_4045_);
lean_inc(v_traceState_4044_);
lean_inc(v_auxDeclNGen_4043_);
lean_inc(v_ngen_4042_);
lean_inc(v_nextMacroScope_4041_);
lean_inc(v_env_4040_);
lean_dec(v___x_4039_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4072_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4051_; lean_object* v___x_4053_; 
v___x_4051_ = l_Lean_Environment_setExporting(v_env_4040_, v_isExporting_4033_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 5, v___x_4034_);
lean_ctor_set(v___x_4049_, 0, v___x_4051_);
v___x_4053_ = v___x_4049_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4051_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_nextMacroScope_4041_);
lean_ctor_set(v_reuseFailAlloc_4071_, 2, v_ngen_4042_);
lean_ctor_set(v_reuseFailAlloc_4071_, 3, v_auxDeclNGen_4043_);
lean_ctor_set(v_reuseFailAlloc_4071_, 4, v_traceState_4044_);
lean_ctor_set(v_reuseFailAlloc_4071_, 5, v___x_4034_);
lean_ctor_set(v_reuseFailAlloc_4071_, 6, v_messages_4045_);
lean_ctor_set(v_reuseFailAlloc_4071_, 7, v_infoState_4046_);
lean_ctor_set(v_reuseFailAlloc_4071_, 8, v_snapshotTasks_4047_);
v___x_4053_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v_mctx_4056_; lean_object* v_zetaDeltaFVarIds_4057_; lean_object* v_postponed_4058_; lean_object* v_diag_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4069_; 
v___x_4054_ = lean_st_ref_set(v___y_4032_, v___x_4053_);
v___x_4055_ = lean_st_ref_take(v___y_4035_);
v_mctx_4056_ = lean_ctor_get(v___x_4055_, 0);
v_zetaDeltaFVarIds_4057_ = lean_ctor_get(v___x_4055_, 2);
v_postponed_4058_ = lean_ctor_get(v___x_4055_, 3);
v_diag_4059_ = lean_ctor_get(v___x_4055_, 4);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4069_ == 0)
{
lean_object* v_unused_4070_; 
v_unused_4070_ = lean_ctor_get(v___x_4055_, 1);
lean_dec(v_unused_4070_);
v___x_4061_ = v___x_4055_;
v_isShared_4062_ = v_isSharedCheck_4069_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_diag_4059_);
lean_inc(v_postponed_4058_);
lean_inc(v_zetaDeltaFVarIds_4057_);
lean_inc(v_mctx_4056_);
lean_dec(v___x_4055_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4069_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 1, v___x_4036_);
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_mctx_4056_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v___x_4036_);
lean_ctor_set(v_reuseFailAlloc_4068_, 2, v_zetaDeltaFVarIds_4057_);
lean_ctor_set(v_reuseFailAlloc_4068_, 3, v_postponed_4058_);
lean_ctor_set(v_reuseFailAlloc_4068_, 4, v_diag_4059_);
v___x_4064_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = lean_st_ref_set(v___y_4035_, v___x_4064_);
v___x_4066_ = lean_box(0);
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
return v___x_4067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4074_, lean_object* v_isExporting_4075_, lean_object* v___x_4076_, lean_object* v___y_4077_, lean_object* v___x_4078_, lean_object* v_a_x3f_4079_, lean_object* v___y_4080_){
_start:
{
uint8_t v_isExporting_boxed_4081_; lean_object* v_res_4082_; 
v_isExporting_boxed_4081_ = lean_unbox(v_isExporting_4075_);
v_res_4082_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4074_, v_isExporting_boxed_4081_, v___x_4076_, v___y_4077_, v___x_4078_, v_a_x3f_4079_);
lean_dec(v_a_x3f_4079_);
lean_dec(v___y_4077_);
lean_dec(v___y_4074_);
return v_res_4082_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4083_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
return v___x_4085_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
lean_ctor_set(v___x_4087_, 1, v___x_4086_);
return v___x_4087_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4089_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
lean_ctor_set(v___x_4089_, 2, v___x_4088_);
lean_ctor_set(v___x_4089_, 3, v___x_4088_);
lean_ctor_set(v___x_4089_, 4, v___x_4088_);
lean_ctor_set(v___x_4089_, 5, v___x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4090_, uint8_t v_isExporting_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v___x_4097_; lean_object* v_env_4098_; uint8_t v_isExporting_4099_; lean_object* v___x_4100_; lean_object* v_env_4101_; lean_object* v_nextMacroScope_4102_; lean_object* v_ngen_4103_; lean_object* v_auxDeclNGen_4104_; lean_object* v_traceState_4105_; lean_object* v_messages_4106_; lean_object* v_infoState_4107_; lean_object* v_snapshotTasks_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4162_; 
v___x_4097_ = lean_st_ref_get(v___y_4095_);
v_env_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc_ref(v_env_4098_);
lean_dec(v___x_4097_);
v_isExporting_4099_ = lean_ctor_get_uint8(v_env_4098_, sizeof(void*)*8);
lean_dec_ref(v_env_4098_);
v___x_4100_ = lean_st_ref_take(v___y_4095_);
v_env_4101_ = lean_ctor_get(v___x_4100_, 0);
v_nextMacroScope_4102_ = lean_ctor_get(v___x_4100_, 1);
v_ngen_4103_ = lean_ctor_get(v___x_4100_, 2);
v_auxDeclNGen_4104_ = lean_ctor_get(v___x_4100_, 3);
v_traceState_4105_ = lean_ctor_get(v___x_4100_, 4);
v_messages_4106_ = lean_ctor_get(v___x_4100_, 6);
v_infoState_4107_ = lean_ctor_get(v___x_4100_, 7);
v_snapshotTasks_4108_ = lean_ctor_get(v___x_4100_, 8);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4162_ == 0)
{
lean_object* v_unused_4163_; 
v_unused_4163_ = lean_ctor_get(v___x_4100_, 5);
lean_dec(v_unused_4163_);
v___x_4110_ = v___x_4100_;
v_isShared_4111_ = v_isSharedCheck_4162_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_snapshotTasks_4108_);
lean_inc(v_infoState_4107_);
lean_inc(v_messages_4106_);
lean_inc(v_traceState_4105_);
lean_inc(v_auxDeclNGen_4104_);
lean_inc(v_ngen_4103_);
lean_inc(v_nextMacroScope_4102_);
lean_inc(v_env_4101_);
lean_dec(v___x_4100_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4162_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4115_; 
v___x_4112_ = l_Lean_Environment_setExporting(v_env_4101_, v_isExporting_4091_);
v___x_4113_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 5, v___x_4113_);
lean_ctor_set(v___x_4110_, 0, v___x_4112_);
v___x_4115_ = v___x_4110_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v_nextMacroScope_4102_);
lean_ctor_set(v_reuseFailAlloc_4161_, 2, v_ngen_4103_);
lean_ctor_set(v_reuseFailAlloc_4161_, 3, v_auxDeclNGen_4104_);
lean_ctor_set(v_reuseFailAlloc_4161_, 4, v_traceState_4105_);
lean_ctor_set(v_reuseFailAlloc_4161_, 5, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4161_, 6, v_messages_4106_);
lean_ctor_set(v_reuseFailAlloc_4161_, 7, v_infoState_4107_);
lean_ctor_set(v_reuseFailAlloc_4161_, 8, v_snapshotTasks_4108_);
v___x_4115_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v_mctx_4118_; lean_object* v_zetaDeltaFVarIds_4119_; lean_object* v_postponed_4120_; lean_object* v_diag_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4159_; 
v___x_4116_ = lean_st_ref_set(v___y_4095_, v___x_4115_);
v___x_4117_ = lean_st_ref_take(v___y_4093_);
v_mctx_4118_ = lean_ctor_get(v___x_4117_, 0);
v_zetaDeltaFVarIds_4119_ = lean_ctor_get(v___x_4117_, 2);
v_postponed_4120_ = lean_ctor_get(v___x_4117_, 3);
v_diag_4121_ = lean_ctor_get(v___x_4117_, 4);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4159_ == 0)
{
lean_object* v_unused_4160_; 
v_unused_4160_ = lean_ctor_get(v___x_4117_, 1);
lean_dec(v_unused_4160_);
v___x_4123_ = v___x_4117_;
v_isShared_4124_ = v_isSharedCheck_4159_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_diag_4121_);
lean_inc(v_postponed_4120_);
lean_inc(v_zetaDeltaFVarIds_4119_);
lean_inc(v_mctx_4118_);
lean_dec(v___x_4117_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4159_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4125_; lean_object* v___x_4127_; 
v___x_4125_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 1, v___x_4125_);
v___x_4127_ = v___x_4123_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_mctx_4118_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v___x_4125_);
lean_ctor_set(v_reuseFailAlloc_4158_, 2, v_zetaDeltaFVarIds_4119_);
lean_ctor_set(v_reuseFailAlloc_4158_, 3, v_postponed_4120_);
lean_ctor_set(v_reuseFailAlloc_4158_, 4, v_diag_4121_);
v___x_4127_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
lean_object* v___x_4128_; lean_object* v_r_4129_; 
v___x_4128_ = lean_st_ref_set(v___y_4093_, v___x_4127_);
lean_inc(v___y_4095_);
lean_inc(v___y_4093_);
v_r_4129_ = lean_apply_5(v_x_4090_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, lean_box(0));
if (lean_obj_tag(v_r_4129_) == 0)
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4146_; 
v_a_4130_ = lean_ctor_get(v_r_4129_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_r_4129_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4132_ = v_r_4129_;
v_isShared_4133_ = v_isSharedCheck_4146_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v_r_4129_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4146_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
lean_inc(v_a_4130_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set_tag(v___x_4132_, 1);
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
lean_object* v___x_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
v___x_4136_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4095_, v_isExporting_4099_, v___x_4113_, v___y_4093_, v___x_4125_, v___x_4135_);
lean_dec_ref(v___x_4135_);
lean_dec(v___y_4093_);
lean_dec(v___y_4095_);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4143_ == 0)
{
lean_object* v_unused_4144_; 
v_unused_4144_ = lean_ctor_get(v___x_4136_, 0);
lean_dec(v_unused_4144_);
v___x_4138_ = v___x_4136_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_dec(v___x_4136_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 0, v_a_4130_);
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4130_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
v_a_4147_ = lean_ctor_get(v_r_4129_, 0);
lean_inc(v_a_4147_);
lean_dec_ref(v_r_4129_);
v___x_4148_ = lean_box(0);
v___x_4149_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4095_, v_isExporting_4099_, v___x_4113_, v___y_4093_, v___x_4125_, v___x_4148_);
lean_dec(v___y_4093_);
lean_dec(v___y_4095_);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; 
v_unused_4157_ = lean_ctor_get(v___x_4149_, 0);
lean_dec(v_unused_4157_);
v___x_4151_ = v___x_4149_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_dec(v___x_4149_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
lean_ctor_set_tag(v___x_4151_, 1);
lean_ctor_set(v___x_4151_, 0, v_a_4147_);
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4147_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4164_, lean_object* v_isExporting_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
uint8_t v_isExporting_boxed_4171_; lean_object* v_res_4172_; 
v_isExporting_boxed_4171_ = lean_unbox(v_isExporting_4165_);
v_res_4172_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4164_, v_isExporting_boxed_4171_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4173_, lean_object* v_x_4174_, uint8_t v_isExporting_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4174_, v_isExporting_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4182_, lean_object* v_x_4183_, lean_object* v_isExporting_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
uint8_t v_isExporting_boxed_4190_; lean_object* v_res_4191_; 
v_isExporting_boxed_4190_ = lean_unbox(v_isExporting_4184_);
v_res_4191_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4182_, v_x_4183_, v_isExporting_boxed_4190_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4192_, lean_object* v_localInsts_4193_, lean_object* v_x_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4192_, v_localInsts_4193_, v_x_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
v_a_4209_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4200_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4200_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4217_, lean_object* v_localInsts_4218_, lean_object* v_x_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4217_, v_localInsts_4218_, v_x_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4226_, lean_object* v_lctx_4227_, lean_object* v_localInsts_4228_, lean_object* v_x_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4227_, v_localInsts_4228_, v_x_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4236_, lean_object* v_lctx_4237_, lean_object* v_localInsts_4238_, lean_object* v_x_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4236_, v_lctx_4237_, v_localInsts_4238_, v_x_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4246_, lean_object* v_x_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4253_ = l_Lean_MessageData_ofName(v_declName_4246_);
v___x_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4255_, lean_object* v_x_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4255_, v_x_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec_ref(v_x_4256_);
return v_res_4262_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4263_; 
v___x_4263_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v_toApplicative_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4337_; 
v___x_4274_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4275_ = l_ReaderT_instMonad___redArg(v___x_4274_);
v_toApplicative_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4337_ == 0)
{
lean_object* v_unused_4338_; 
v_unused_4338_ = lean_ctor_get(v___x_4275_, 1);
lean_dec(v_unused_4338_);
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4337_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_toApplicative_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4337_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v_toFunctor_4280_; lean_object* v_toSeq_4281_; lean_object* v_toSeqLeft_4282_; lean_object* v_toSeqRight_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4335_; 
v_toFunctor_4280_ = lean_ctor_get(v_toApplicative_4276_, 0);
v_toSeq_4281_ = lean_ctor_get(v_toApplicative_4276_, 2);
v_toSeqLeft_4282_ = lean_ctor_get(v_toApplicative_4276_, 3);
v_toSeqRight_4283_ = lean_ctor_get(v_toApplicative_4276_, 4);
v_isSharedCheck_4335_ = !lean_is_exclusive(v_toApplicative_4276_);
if (v_isSharedCheck_4335_ == 0)
{
lean_object* v_unused_4336_; 
v_unused_4336_ = lean_ctor_get(v_toApplicative_4276_, 1);
lean_dec(v_unused_4336_);
v___x_4285_ = v_toApplicative_4276_;
v_isShared_4286_ = v_isSharedCheck_4335_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_toSeqRight_4283_);
lean_inc(v_toSeqLeft_4282_);
lean_inc(v_toSeq_4281_);
lean_inc(v_toFunctor_4280_);
lean_dec(v_toApplicative_4276_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4335_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___f_4287_; lean_object* v___f_4288_; lean_object* v___f_4289_; lean_object* v___f_4290_; lean_object* v___x_4291_; lean_object* v___f_4292_; lean_object* v___f_4293_; lean_object* v___f_4294_; lean_object* v___x_4296_; 
v___f_4287_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4288_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4280_);
v___f_4289_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4289_, 0, v_toFunctor_4280_);
v___f_4290_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4290_, 0, v_toFunctor_4280_);
v___x_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___f_4289_);
lean_ctor_set(v___x_4291_, 1, v___f_4290_);
v___f_4292_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4292_, 0, v_toSeqRight_4283_);
v___f_4293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4293_, 0, v_toSeqLeft_4282_);
v___f_4294_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4294_, 0, v_toSeq_4281_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 4, v___f_4292_);
lean_ctor_set(v___x_4285_, 3, v___f_4293_);
lean_ctor_set(v___x_4285_, 2, v___f_4294_);
lean_ctor_set(v___x_4285_, 1, v___f_4287_);
lean_ctor_set(v___x_4285_, 0, v___x_4291_);
v___x_4296_ = v___x_4285_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4291_);
lean_ctor_set(v_reuseFailAlloc_4334_, 1, v___f_4287_);
lean_ctor_set(v_reuseFailAlloc_4334_, 2, v___f_4294_);
lean_ctor_set(v_reuseFailAlloc_4334_, 3, v___f_4293_);
lean_ctor_set(v_reuseFailAlloc_4334_, 4, v___f_4292_);
v___x_4296_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v___x_4298_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 1, v___f_4288_);
lean_ctor_set(v___x_4278_, 0, v___x_4296_);
v___x_4298_ = v___x_4278_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4296_);
lean_ctor_set(v_reuseFailAlloc_4333_, 1, v___f_4288_);
v___x_4298_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
lean_object* v___x_4299_; lean_object* v_toApplicative_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4331_; 
v___x_4299_ = l_ReaderT_instMonad___redArg(v___x_4298_);
v_toApplicative_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4331_ == 0)
{
lean_object* v_unused_4332_; 
v_unused_4332_ = lean_ctor_get(v___x_4299_, 1);
lean_dec(v_unused_4332_);
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4331_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_toApplicative_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4331_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v_toFunctor_4304_; lean_object* v_toSeq_4305_; lean_object* v_toSeqLeft_4306_; lean_object* v_toSeqRight_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4329_; 
v_toFunctor_4304_ = lean_ctor_get(v_toApplicative_4300_, 0);
v_toSeq_4305_ = lean_ctor_get(v_toApplicative_4300_, 2);
v_toSeqLeft_4306_ = lean_ctor_get(v_toApplicative_4300_, 3);
v_toSeqRight_4307_ = lean_ctor_get(v_toApplicative_4300_, 4);
v_isSharedCheck_4329_ = !lean_is_exclusive(v_toApplicative_4300_);
if (v_isSharedCheck_4329_ == 0)
{
lean_object* v_unused_4330_; 
v_unused_4330_ = lean_ctor_get(v_toApplicative_4300_, 1);
lean_dec(v_unused_4330_);
v___x_4309_ = v_toApplicative_4300_;
v_isShared_4310_ = v_isSharedCheck_4329_;
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
v_isShared_4310_ = v_isSharedCheck_4329_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___f_4311_; lean_object* v___f_4312_; lean_object* v___f_4313_; lean_object* v___f_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___f_4317_; lean_object* v___f_4318_; lean_object* v___x_4320_; 
v___f_4311_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4312_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
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
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4315_);
lean_ctor_set(v_reuseFailAlloc_4328_, 1, v___f_4311_);
lean_ctor_set(v_reuseFailAlloc_4328_, 2, v___f_4318_);
lean_ctor_set(v_reuseFailAlloc_4328_, 3, v___f_4317_);
lean_ctor_set(v_reuseFailAlloc_4328_, 4, v___f_4316_);
v___x_4320_ = v_reuseFailAlloc_4328_;
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
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4320_);
lean_ctor_set(v_reuseFailAlloc_4327_, 1, v___f_4312_);
v___x_4322_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_18785__overap_4325_; lean_object* v___x_4326_; 
v___x_4323_ = lean_box(0);
v___x_4324_ = l_instInhabitedOfMonad___redArg(v___x_4322_, v___x_4323_);
v___x_18785__overap_4325_ = lean_panic_fn(v___x_4324_, v_msg_4268_);
v___x_4326_ = lean_apply_5(v___x_18785__overap_4325_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, lean_box(0));
return v___x_4326_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
return v_res_4345_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4347_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4348_ = l_Lean_stringToMessageData(v___x_4347_);
return v___x_4348_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4351_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4352_ = lean_unsigned_to_nat(11u);
v___x_4353_ = lean_unsigned_to_nat(122u);
v___x_4354_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4355_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4356_ = l_mkPanicMessageWithDecl(v___x_4355_, v___x_4354_, v___x_4353_, v___x_4352_, v___x_4351_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v___x_4371_; lean_object* v_env_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; 
v___x_4371_ = lean_st_ref_get(v___y_4361_);
v_env_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc_ref(v_env_4372_);
lean_dec(v___x_4371_);
v___x_4373_ = 0;
lean_inc(v_constName_4357_);
v___x_4374_ = l_Lean_Environment_findAsync_x3f(v_env_4372_, v_constName_4357_, v___x_4373_);
if (lean_obj_tag(v___x_4374_) == 1)
{
lean_object* v_val_4375_; uint8_t v_kind_4376_; 
v_val_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_val_4375_);
lean_dec_ref(v___x_4374_);
v_kind_4376_ = lean_ctor_get_uint8(v_val_4375_, sizeof(void*)*3);
if (v_kind_4376_ == 6)
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4375_);
if (lean_obj_tag(v___x_4377_) == 6)
{
lean_object* v_val_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v_constName_4357_);
v_val_4378_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4377_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_val_4378_);
lean_dec(v___x_4377_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
lean_ctor_set_tag(v___x_4380_, 0);
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_val_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
else
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
lean_dec_ref(v___x_4377_);
v___x_4386_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
lean_inc(v___y_4361_);
lean_inc_ref(v___y_4360_);
lean_inc(v___y_4359_);
lean_inc_ref(v___y_4358_);
v___x_4387_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4386_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4396_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4390_ = v___x_4387_;
v_isShared_4391_ = v_isSharedCheck_4396_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4387_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4396_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
if (lean_obj_tag(v_a_4388_) == 0)
{
lean_del_object(v___x_4390_);
goto v___jp_4363_;
}
else
{
lean_object* v_val_4392_; lean_object* v___x_4394_; 
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v_constName_4357_);
v_val_4392_ = lean_ctor_get(v_a_4388_, 0);
lean_inc(v_val_4392_);
lean_dec_ref(v_a_4388_);
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 0, v_val_4392_);
v___x_4394_ = v___x_4390_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_val_4392_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v_constName_4357_);
v_a_4397_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4387_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4387_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
}
else
{
lean_dec(v_val_4375_);
goto v___jp_4363_;
}
}
else
{
lean_dec(v___x_4374_);
goto v___jp_4363_;
}
v___jp_4363_:
{
lean_object* v___x_4364_; uint8_t v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4364_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4365_ = 0;
v___x_4366_ = l_Lean_MessageData_ofConstName(v_constName_4357_, v___x_4365_);
v___x_4367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4364_);
lean_ctor_set(v___x_4367_, 1, v___x_4366_);
v___x_4368_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4367_);
lean_ctor_set(v___x_4369_, 1, v___x_4368_);
v___x_4370_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4369_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
return v___x_4370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4412_, lean_object* v___x_4413_, lean_object* v___x_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; 
lean_inc(v___y_4418_);
lean_inc_ref(v___y_4417_);
lean_inc(v___y_4416_);
lean_inc_ref(v___y_4415_);
v___x_4420_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4412_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4432_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4423_ = v___x_4420_;
v_isShared_4424_ = v_isSharedCheck_4432_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4420_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4432_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v_numFields_4425_; uint8_t v___x_4426_; 
v_numFields_4425_ = lean_ctor_get(v_a_4421_, 4);
v___x_4426_ = lean_nat_dec_lt(v___x_4413_, v_numFields_4425_);
if (v___x_4426_ == 0)
{
lean_object* v___x_4428_; 
lean_dec(v_a_4421_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 0, v___x_4414_);
v___x_4428_ = v___x_4423_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4414_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
else
{
lean_object* v___x_4430_; 
lean_del_object(v___x_4423_);
lean_inc(v___y_4418_);
lean_inc_ref(v___y_4417_);
lean_inc(v___y_4416_);
lean_inc_ref(v___y_4415_);
lean_inc(v_a_4421_);
v___x_4430_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4421_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v___x_4431_; 
lean_dec_ref(v___x_4430_);
v___x_4431_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4421_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
return v___x_4431_;
}
else
{
lean_dec(v_a_4421_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
v_a_4433_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4420_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4420_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4441_, lean_object* v___x_4442_, lean_object* v___x_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4441_, v___x_4442_, v___x_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
lean_dec(v___x_4442_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4450_, uint8_t v___x_4451_, lean_object* v_as_x27_4452_, lean_object* v_b_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
if (lean_obj_tag(v_as_x27_4452_) == 0)
{
lean_object* v___x_4459_; 
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
v___x_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4459_, 0, v_b_4453_);
return v___x_4459_;
}
else
{
lean_object* v_head_4460_; lean_object* v_tail_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___f_4464_; uint8_t v___y_4466_; uint8_t v___x_4469_; 
v_head_4460_ = lean_ctor_get(v_as_x27_4452_, 0);
lean_inc(v_head_4460_);
v_tail_4461_ = lean_ctor_get(v_as_x27_4452_, 1);
lean_inc(v_tail_4461_);
lean_dec_ref(v_as_x27_4452_);
v___x_4462_ = lean_unsigned_to_nat(0u);
v___x_4463_ = lean_box(0);
lean_inc(v_head_4460_);
v___f_4464_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4464_, 0, v_head_4460_);
lean_closure_set(v___f_4464_, 1, v___x_4462_);
lean_closure_set(v___f_4464_, 2, v___x_4463_);
v___x_4469_ = l_Lean_isPrivateName(v_head_4460_);
lean_dec(v_head_4460_);
if (v___x_4469_ == 0)
{
v___y_4466_ = v___y_4450_;
goto v___jp_4465_;
}
else
{
v___y_4466_ = v___x_4451_;
goto v___jp_4465_;
}
v___jp_4465_:
{
lean_object* v___x_4467_; 
lean_inc(v___y_4457_);
lean_inc_ref(v___y_4456_);
lean_inc(v___y_4455_);
lean_inc_ref(v___y_4454_);
v___x_4467_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4464_, v___y_4466_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_dec_ref(v___x_4467_);
v_as_x27_4452_ = v_tail_4461_;
v_b_4453_ = v___x_4463_;
goto _start;
}
else
{
lean_dec(v_tail_4461_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
return v___x_4467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4470_, lean_object* v___x_4471_, lean_object* v_as_x27_4472_, lean_object* v_b_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
uint8_t v___y_19711__boxed_4479_; uint8_t v___x_19712__boxed_4480_; lean_object* v_res_4481_; 
v___y_19711__boxed_4479_ = lean_unbox(v___y_4470_);
v___x_19712__boxed_4480_ = lean_unbox(v___x_4471_);
v_res_4481_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_19711__boxed_4479_, v___x_19712__boxed_4480_, v_as_x27_4472_, v_b_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4482_, uint8_t v_hasTrace_4483_, lean_object* v_ctors_4484_, lean_object* v___x_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4482_, v_hasTrace_4483_, v_ctors_4484_, v___x_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4498_; 
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v___x_4491_, 0);
lean_dec(v_unused_4499_);
v___x_4493_ = v___x_4491_;
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
else
{
lean_dec(v___x_4491_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4498_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 0, v___x_4485_);
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4485_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
}
else
{
return v___x_4491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4500_, lean_object* v_hasTrace_4501_, lean_object* v_ctors_4502_, lean_object* v___x_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
uint8_t v___y_19756__boxed_4509_; uint8_t v_hasTrace_boxed_4510_; lean_object* v_res_4511_; 
v___y_19756__boxed_4509_ = lean_unbox(v___y_4500_);
v_hasTrace_boxed_4510_ = lean_unbox(v_hasTrace_4501_);
v_res_4511_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_19756__boxed_4509_, v_hasTrace_boxed_4510_, v_ctors_4502_, v___x_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t v_hasTrace_4512_, uint8_t v___x_4513_, lean_object* v_ctors_4514_, lean_object* v___x_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v___x_4521_; 
v___x_4521_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_hasTrace_4512_, v___x_4513_, v_ctors_4514_, v___x_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4528_ == 0)
{
lean_object* v_unused_4529_; 
v_unused_4529_ = lean_ctor_get(v___x_4521_, 0);
lean_dec(v_unused_4529_);
v___x_4523_ = v___x_4521_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_dec(v___x_4521_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4515_);
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4515_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
else
{
return v___x_4521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object* v_hasTrace_4530_, lean_object* v___x_4531_, lean_object* v_ctors_4532_, lean_object* v___x_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
uint8_t v_hasTrace_boxed_4539_; uint8_t v___x_19797__boxed_4540_; lean_object* v_res_4541_; 
v_hasTrace_boxed_4539_ = lean_unbox(v_hasTrace_4530_);
v___x_19797__boxed_4540_ = lean_unbox(v___x_4531_);
v_res_4541_ = l_Lean_Meta_mkInjectiveTheorems___lam__2(v_hasTrace_boxed_4539_, v___x_19797__boxed_4540_, v_ctors_4532_, v___x_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t v___x_4542_, uint8_t v_isUnsafe_4543_, lean_object* v_ctors_4544_, lean_object* v___x_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4542_, v_isUnsafe_4543_, v_ctors_4544_, v___x_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4558_ == 0)
{
lean_object* v_unused_4559_; 
v_unused_4559_ = lean_ctor_get(v___x_4551_, 0);
lean_dec(v_unused_4559_);
v___x_4553_ = v___x_4551_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_dec(v___x_4551_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 0, v___x_4545_);
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4545_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
else
{
return v___x_4551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object* v___x_4560_, lean_object* v_isUnsafe_4561_, lean_object* v_ctors_4562_, lean_object* v___x_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_){
_start:
{
uint8_t v___x_19838__boxed_4569_; uint8_t v_isUnsafe_boxed_4570_; lean_object* v_res_4571_; 
v___x_19838__boxed_4569_ = lean_unbox(v___x_4560_);
v_isUnsafe_boxed_4570_ = lean_unbox(v_isUnsafe_4561_);
v_res_4571_ = l_Lean_Meta_mkInjectiveTheorems___lam__3(v___x_19838__boxed_4569_, v_isUnsafe_boxed_4570_, v_ctors_4562_, v___x_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
return v_res_4571_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4573_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4574_ = l_Lean_stringToMessageData(v___x_4573_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v___x_4581_; lean_object* v_env_4582_; lean_object* v___x_4583_; 
v___x_4581_ = lean_st_ref_get(v___y_4579_);
v_env_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc_ref(v_env_4582_);
lean_dec(v___x_4581_);
lean_inc(v_constName_4575_);
v___x_4583_ = l_Lean_isInductiveCore_x3f(v_env_4582_, v_constName_4575_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v___x_4584_; uint8_t v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4584_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4585_ = 0;
v___x_4586_ = l_Lean_MessageData_ofConstName(v_constName_4575_, v___x_4585_);
v___x_4587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4584_);
lean_ctor_set(v___x_4587_, 1, v___x_4586_);
v___x_4588_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4587_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4589_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
return v___x_4590_;
}
else
{
lean_object* v_val_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4598_; 
lean_dec(v_constName_4575_);
v_val_4591_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4593_ = v___x_4583_;
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_val_4591_);
lean_dec(v___x_4583_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
lean_ctor_set_tag(v___x_4593_, 0);
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_val_4591_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
return v_res_4605_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4606_; 
v___x_4606_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4606_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4607_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
return v___x_4608_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4609_ = lean_unsigned_to_nat(32u);
v___x_4610_ = lean_mk_empty_array_with_capacity(v___x_4609_);
v___x_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
return v___x_4611_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4612_ = ((size_t)5ULL);
v___x_4613_ = lean_unsigned_to_nat(0u);
v___x_4614_ = lean_unsigned_to_nat(32u);
v___x_4615_ = lean_mk_empty_array_with_capacity(v___x_4614_);
v___x_4616_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4617_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
lean_ctor_set(v___x_4617_, 1, v___x_4615_);
lean_ctor_set(v___x_4617_, 2, v___x_4613_);
lean_ctor_set(v___x_4617_, 3, v___x_4613_);
lean_ctor_set_usize(v___x_4617_, 4, v___x_4612_);
return v___x_4617_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4618_ = lean_box(1);
v___x_4619_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4620_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
lean_ctor_set(v___x_4621_, 1, v___x_4619_);
lean_ctor_set(v___x_4621_, 2, v___x_4618_);
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_){
_start:
{
lean_object* v___x_4630_; lean_object* v_options_4631_; lean_object* v___x_4632_; 
v___x_4630_ = lean_st_ref_get(v_a_4628_);
v_options_4631_ = lean_ctor_get(v_a_4627_, 2);
lean_inc(v_a_4628_);
lean_inc_ref(v_a_4627_);
lean_inc(v_a_4626_);
lean_inc_ref(v_a_4625_);
lean_inc(v_declName_4624_);
v___x_4632_ = l_Lean_Meta_isInductivePredicate(v_declName_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4822_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4635_ = v___x_4632_;
v_isShared_4636_ = v_isSharedCheck_4822_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4632_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4822_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v_env_4642_; lean_object* v___f_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; lean_object* v___y_4647_; uint8_t v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v_a_4652_; lean_object* v___y_4662_; lean_object* v___y_4663_; uint8_t v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v_a_4667_; lean_object* v___y_4670_; lean_object* v___y_4671_; uint8_t v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v_a_4675_; lean_object* v___y_4678_; lean_object* v___y_4679_; uint8_t v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v_a_4683_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v___y_4698_; uint8_t v___y_4699_; lean_object* v___y_4700_; lean_object* v_a_4701_; lean_object* v___y_4704_; lean_object* v___y_4705_; lean_object* v___y_4706_; uint8_t v___y_4707_; lean_object* v___y_4708_; lean_object* v_a_4709_; uint8_t v___y_4712_; uint8_t v___y_4713_; lean_object* v___y_4714_; lean_object* v___y_4715_; uint8_t v___y_4753_; uint8_t v___x_4819_; 
v_env_4642_ = lean_ctor_get(v___x_4630_, 0);
lean_inc_ref(v_env_4642_);
lean_dec(v___x_4630_);
lean_inc(v_declName_4624_);
v___f_4643_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4643_, 0, v_declName_4624_);
v___x_4644_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4645_ = 1;
v___x_4819_ = l_Lean_Environment_contains(v_env_4642_, v___x_4644_, v___x_4645_);
if (v___x_4819_ == 0)
{
v___y_4753_ = v___x_4819_;
goto v___jp_4752_;
}
else
{
lean_object* v___x_4820_; uint8_t v___x_4821_; 
v___x_4820_ = l_Lean_Meta_genInjectivity;
v___x_4821_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4631_, v___x_4820_);
v___y_4753_ = v___x_4821_;
goto v___jp_4752_;
}
v___jp_4637_:
{
lean_object* v___x_4638_; lean_object* v___x_4640_; 
v___x_4638_ = lean_box(0);
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 0, v___x_4638_);
v___x_4640_ = v___x_4635_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
v___jp_4646_:
{
lean_object* v___x_4653_; double v___x_4654_; double v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4653_ = lean_io_get_num_heartbeats();
v___x_4654_ = lean_float_of_nat(v___y_4651_);
v___x_4655_ = lean_float_of_nat(v___x_4653_);
v___x_4656_ = lean_box_float(v___x_4654_);
v___x_4657_ = lean_box_float(v___x_4655_);
v___x_4658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4656_);
lean_ctor_set(v___x_4658_, 1, v___x_4657_);
v___x_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4659_, 0, v_a_4652_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
v___x_4660_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4649_, v___x_4645_, v___y_4647_, v_options_4631_, v___y_4648_, v___y_4650_, v___f_4643_, v___x_4659_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
lean_dec_ref(v_options_4631_);
return v___x_4660_;
}
v___jp_4661_:
{
lean_object* v___x_4668_; 
v___x_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4668_, 0, v_a_4667_);
v___y_4647_ = v___y_4662_;
v___y_4648_ = v___y_4664_;
v___y_4649_ = v___y_4663_;
v___y_4650_ = v___y_4665_;
v___y_4651_ = v___y_4666_;
v_a_4652_ = v___x_4668_;
goto v___jp_4646_;
}
v___jp_4669_:
{
lean_object* v___x_4676_; 
v___x_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4676_, 0, v_a_4675_);
v___y_4647_ = v___y_4670_;
v___y_4648_ = v___y_4672_;
v___y_4649_ = v___y_4671_;
v___y_4650_ = v___y_4673_;
v___y_4651_ = v___y_4674_;
v_a_4652_ = v___x_4676_;
goto v___jp_4646_;
}
v___jp_4677_:
{
lean_object* v___x_4684_; double v___x_4685_; double v___x_4686_; double v___x_4687_; double v___x_4688_; double v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4684_ = lean_io_mono_nanos_now();
v___x_4685_ = lean_float_of_nat(v___y_4678_);
v___x_4686_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_4687_ = lean_float_div(v___x_4685_, v___x_4686_);
v___x_4688_ = lean_float_of_nat(v___x_4684_);
v___x_4689_ = lean_float_div(v___x_4688_, v___x_4686_);
v___x_4690_ = lean_box_float(v___x_4687_);
v___x_4691_ = lean_box_float(v___x_4689_);
v___x_4692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4690_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
v___x_4693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4693_, 0, v_a_4683_);
lean_ctor_set(v___x_4693_, 1, v___x_4692_);
v___x_4694_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4681_, v___x_4645_, v___y_4679_, v_options_4631_, v___y_4680_, v___y_4682_, v___f_4643_, v___x_4693_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
lean_dec_ref(v_options_4631_);
return v___x_4694_;
}
v___jp_4695_:
{
lean_object* v___x_4702_; 
v___x_4702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4702_, 0, v_a_4701_);
v___y_4678_ = v___y_4696_;
v___y_4679_ = v___y_4697_;
v___y_4680_ = v___y_4699_;
v___y_4681_ = v___y_4698_;
v___y_4682_ = v___y_4700_;
v_a_4683_ = v___x_4702_;
goto v___jp_4677_;
}
v___jp_4703_:
{
lean_object* v___x_4710_; 
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v_a_4709_);
v___y_4678_ = v___y_4704_;
v___y_4679_ = v___y_4705_;
v___y_4680_ = v___y_4707_;
v___y_4681_ = v___y_4706_;
v___y_4682_ = v___y_4708_;
v_a_4683_ = v___x_4710_;
goto v___jp_4677_;
}
v___jp_4711_:
{
lean_object* v___x_4716_; lean_object* v_a_4717_; lean_object* v___x_4718_; uint8_t v___x_4719_; 
v___x_4716_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4628_);
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref(v___x_4716_);
v___x_4718_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4719_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4631_, v___x_4718_);
if (v___x_4719_ == 0)
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4720_ = lean_io_mono_nanos_now();
v___x_4721_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; uint8_t v_isUnsafe_4723_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4722_);
lean_dec_ref(v___x_4721_);
v_isUnsafe_4723_ = lean_ctor_get_uint8(v_a_4722_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4723_ == 0)
{
lean_object* v_ctors_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___f_4730_; lean_object* v___x_4731_; 
v_ctors_4724_ = lean_ctor_get(v_a_4722_, 4);
lean_inc(v_ctors_4724_);
lean_dec(v_a_4722_);
v___x_4725_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4726_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4727_ = lean_box(0);
v___x_4728_ = lean_box(v___y_4712_);
v___x_4729_ = lean_box(v___x_4719_);
v___f_4730_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4730_, 0, v___x_4728_);
lean_closure_set(v___f_4730_, 1, v___x_4729_);
lean_closure_set(v___f_4730_, 2, v_ctors_4724_);
lean_closure_set(v___f_4730_, 3, v___x_4727_);
lean_inc(v_a_4628_);
lean_inc_ref(v_a_4627_);
lean_inc(v_a_4626_);
lean_inc_ref(v_a_4625_);
v___x_4731_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4725_, v___x_4726_, v___f_4730_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4732_);
lean_dec_ref(v___x_4731_);
v___y_4696_ = v___x_4720_;
v___y_4697_ = v___y_4714_;
v___y_4698_ = v___y_4715_;
v___y_4699_ = v___y_4713_;
v___y_4700_ = v_a_4717_;
v_a_4701_ = v_a_4732_;
goto v___jp_4695_;
}
else
{
lean_object* v_a_4733_; 
v_a_4733_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4733_);
lean_dec_ref(v___x_4731_);
v___y_4704_ = v___x_4720_;
v___y_4705_ = v___y_4714_;
v___y_4706_ = v___y_4715_;
v___y_4707_ = v___y_4713_;
v___y_4708_ = v_a_4717_;
v_a_4709_ = v_a_4733_;
goto v___jp_4703_;
}
}
else
{
lean_object* v___x_4734_; 
lean_dec(v_a_4722_);
v___x_4734_ = lean_box(0);
v___y_4696_ = v___x_4720_;
v___y_4697_ = v___y_4714_;
v___y_4698_ = v___y_4715_;
v___y_4699_ = v___y_4713_;
v___y_4700_ = v_a_4717_;
v_a_4701_ = v___x_4734_;
goto v___jp_4695_;
}
}
else
{
lean_object* v_a_4735_; 
v_a_4735_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4735_);
lean_dec_ref(v___x_4721_);
v___y_4704_ = v___x_4720_;
v___y_4705_ = v___y_4714_;
v___y_4706_ = v___y_4715_;
v___y_4707_ = v___y_4713_;
v___y_4708_ = v_a_4717_;
v_a_4709_ = v_a_4735_;
goto v___jp_4703_;
}
}
else
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_io_get_num_heartbeats();
v___x_4737_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; uint8_t v_isUnsafe_4739_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref(v___x_4737_);
v_isUnsafe_4739_ = lean_ctor_get_uint8(v_a_4738_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4739_ == 0)
{
lean_object* v_ctors_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___f_4746_; lean_object* v___x_4747_; 
v_ctors_4740_ = lean_ctor_get(v_a_4738_, 4);
lean_inc(v_ctors_4740_);
lean_dec(v_a_4738_);
v___x_4741_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4742_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4743_ = lean_box(0);
v___x_4744_ = lean_box(v___x_4719_);
v___x_4745_ = lean_box(v_isUnsafe_4739_);
v___f_4746_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed), 9, 4);
lean_closure_set(v___f_4746_, 0, v___x_4744_);
lean_closure_set(v___f_4746_, 1, v___x_4745_);
lean_closure_set(v___f_4746_, 2, v_ctors_4740_);
lean_closure_set(v___f_4746_, 3, v___x_4743_);
lean_inc(v_a_4628_);
lean_inc_ref(v_a_4627_);
lean_inc(v_a_4626_);
lean_inc_ref(v_a_4625_);
v___x_4747_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4741_, v___x_4742_, v___f_4746_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref(v___x_4747_);
v___y_4662_ = v___y_4714_;
v___y_4663_ = v___y_4715_;
v___y_4664_ = v___y_4713_;
v___y_4665_ = v_a_4717_;
v___y_4666_ = v___x_4736_;
v_a_4667_ = v_a_4748_;
goto v___jp_4661_;
}
else
{
lean_object* v_a_4749_; 
v_a_4749_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4749_);
lean_dec_ref(v___x_4747_);
v___y_4670_ = v___y_4714_;
v___y_4671_ = v___y_4715_;
v___y_4672_ = v___y_4713_;
v___y_4673_ = v_a_4717_;
v___y_4674_ = v___x_4736_;
v_a_4675_ = v_a_4749_;
goto v___jp_4669_;
}
}
else
{
lean_object* v___x_4750_; 
lean_dec(v_a_4738_);
v___x_4750_ = lean_box(0);
v___y_4662_ = v___y_4714_;
v___y_4663_ = v___y_4715_;
v___y_4664_ = v___y_4713_;
v___y_4665_ = v_a_4717_;
v___y_4666_ = v___x_4736_;
v_a_4667_ = v___x_4750_;
goto v___jp_4661_;
}
}
else
{
lean_object* v_a_4751_; 
v_a_4751_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4751_);
lean_dec_ref(v___x_4737_);
v___y_4670_ = v___y_4714_;
v___y_4671_ = v___y_4715_;
v___y_4672_ = v___y_4713_;
v___y_4673_ = v_a_4717_;
v___y_4674_ = v___x_4736_;
v_a_4675_ = v_a_4751_;
goto v___jp_4669_;
}
}
}
v___jp_4752_:
{
if (v___y_4753_ == 0)
{
lean_dec_ref(v___f_4643_);
lean_dec(v_a_4633_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_declName_4624_);
goto v___jp_4637_;
}
else
{
uint8_t v___x_4754_; 
v___x_4754_ = lean_unbox(v_a_4633_);
lean_dec(v_a_4633_);
if (v___x_4754_ == 0)
{
uint8_t v_hasTrace_4755_; 
lean_del_object(v___x_4635_);
v_hasTrace_4755_ = lean_ctor_get_uint8(v_options_4631_, sizeof(void*)*1);
if (v_hasTrace_4755_ == 0)
{
lean_object* v___x_4756_; 
lean_dec_ref(v___f_4643_);
v___x_4756_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4774_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4759_ = v___x_4756_;
v_isShared_4760_ = v_isSharedCheck_4774_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4756_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4774_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
uint8_t v_isUnsafe_4761_; 
v_isUnsafe_4761_ = lean_ctor_get_uint8(v_a_4757_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4761_ == 0)
{
lean_object* v_ctors_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___f_4768_; lean_object* v___x_4769_; 
lean_del_object(v___x_4759_);
v_ctors_4762_ = lean_ctor_get(v_a_4757_, 4);
lean_inc(v_ctors_4762_);
lean_dec(v_a_4757_);
v___x_4763_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4764_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4765_ = lean_box(0);
v___x_4766_ = lean_box(v___y_4753_);
v___x_4767_ = lean_box(v_hasTrace_4755_);
v___f_4768_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4768_, 0, v___x_4766_);
lean_closure_set(v___f_4768_, 1, v___x_4767_);
lean_closure_set(v___f_4768_, 2, v_ctors_4762_);
lean_closure_set(v___f_4768_, 3, v___x_4765_);
v___x_4769_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4763_, v___x_4764_, v___f_4768_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
return v___x_4769_;
}
else
{
lean_object* v___x_4770_; lean_object* v___x_4772_; 
lean_dec(v_a_4757_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
v___x_4770_ = lean_box(0);
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 0, v___x_4770_);
v___x_4772_ = v___x_4759_;
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
}
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4782_; 
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
v_a_4775_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4777_ = v___x_4756_;
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4756_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4775_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
else
{
lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v_a_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; 
v___x_4783_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4784_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v___x_4783_, v_a_4627_);
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
lean_inc(v_a_4785_);
lean_dec_ref(v___x_4784_);
v___x_4786_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1));
v___x_4787_ = lean_unbox(v_a_4785_);
if (v___x_4787_ == 0)
{
lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4788_ = l_Lean_trace_profiler;
v___x_4789_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4631_, v___x_4788_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; 
lean_dec(v_a_4785_);
lean_dec_ref(v___f_4643_);
v___x_4790_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4808_; 
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4793_ = v___x_4790_;
v_isShared_4794_ = v_isSharedCheck_4808_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4808_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
uint8_t v_isUnsafe_4795_; 
v_isUnsafe_4795_ = lean_ctor_get_uint8(v_a_4791_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4795_ == 0)
{
lean_object* v_ctors_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___f_4802_; lean_object* v___x_4803_; 
lean_del_object(v___x_4793_);
v_ctors_4796_ = lean_ctor_get(v_a_4791_, 4);
lean_inc(v_ctors_4796_);
lean_dec(v_a_4791_);
v___x_4797_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4798_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4799_ = lean_box(0);
v___x_4800_ = lean_box(v_hasTrace_4755_);
v___x_4801_ = lean_box(v___x_4789_);
v___f_4802_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4802_, 0, v___x_4800_);
lean_closure_set(v___f_4802_, 1, v___x_4801_);
lean_closure_set(v___f_4802_, 2, v_ctors_4796_);
lean_closure_set(v___f_4802_, 3, v___x_4799_);
v___x_4803_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4797_, v___x_4798_, v___f_4802_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
return v___x_4803_;
}
else
{
lean_object* v___x_4804_; lean_object* v___x_4806_; 
lean_dec(v_a_4791_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
v___x_4804_ = lean_box(0);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 0, v___x_4804_);
v___x_4806_ = v___x_4793_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4804_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
else
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4816_; 
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
v_a_4809_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4811_ = v___x_4790_;
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4790_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4816_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4814_; 
if (v_isShared_4812_ == 0)
{
v___x_4814_ = v___x_4811_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_a_4809_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
}
}
else
{
uint8_t v___x_4817_; 
lean_inc_ref(v_options_4631_);
v___x_4817_ = lean_unbox(v_a_4785_);
lean_dec(v_a_4785_);
v___y_4712_ = v_hasTrace_4755_;
v___y_4713_ = v___x_4817_;
v___y_4714_ = v___x_4786_;
v___y_4715_ = v___x_4783_;
goto v___jp_4711_;
}
}
else
{
uint8_t v___x_4818_; 
lean_inc_ref(v_options_4631_);
v___x_4818_ = lean_unbox(v_a_4785_);
lean_dec(v_a_4785_);
v___y_4712_ = v_hasTrace_4755_;
v___y_4713_ = v___x_4818_;
v___y_4714_ = v___x_4786_;
v___y_4715_ = v___x_4783_;
goto v___jp_4711_;
}
}
}
else
{
lean_dec_ref(v___f_4643_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_declName_4624_);
goto v___jp_4637_;
}
}
}
}
}
else
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4830_; 
lean_dec(v___x_4630_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_declName_4624_);
v_a_4823_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4825_ = v___x_4632_;
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v___x_4632_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4828_; 
if (v_isShared_4826_ == 0)
{
v___x_4828_ = v___x_4825_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_a_4823_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4838_, uint8_t v___x_4839_, lean_object* v_as_4840_, lean_object* v_as_x27_4841_, lean_object* v_b_4842_, lean_object* v_a_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4838_, v___x_4839_, v_as_x27_4841_, v_b_4842_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4850_, lean_object* v___x_4851_, lean_object* v_as_4852_, lean_object* v_as_x27_4853_, lean_object* v_b_4854_, lean_object* v_a_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
uint8_t v___y_20466__boxed_4861_; uint8_t v___x_20467__boxed_4862_; lean_object* v_res_4863_; 
v___y_20466__boxed_4861_ = lean_unbox(v___y_4850_);
v___x_20467__boxed_4862_ = lean_unbox(v___x_4851_);
v_res_4863_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_20466__boxed_4861_, v___x_20467__boxed_4862_, v_as_4852_, v_as_x27_4853_, v_b_4854_, v_a_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
lean_dec(v_as_4852_);
return v_res_4863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4904_ = lean_unsigned_to_nat(4172903888u);
v___x_4905_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4906_ = l_Lean_Name_num___override(v___x_4905_, v___x_4904_);
return v___x_4906_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4908_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4909_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4910_ = l_Lean_Name_str___override(v___x_4909_, v___x_4908_);
return v___x_4910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
v___x_4912_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4913_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4914_ = l_Lean_Name_str___override(v___x_4913_, v___x_4912_);
return v___x_4914_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4915_ = lean_unsigned_to_nat(2u);
v___x_4916_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4917_ = l_Lean_Name_num___override(v___x_4916_, v___x_4915_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4919_; uint8_t v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4919_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4920_ = 0;
v___x_4921_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4922_ = l_Lean_registerTraceClass(v___x_4919_, v___x_4920_, v___x_4921_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4923_){
_start:
{
lean_object* v_res_4924_; 
v_res_4924_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4925_, lean_object* v_b_4926_){
_start:
{
lean_object* v_array_4927_; lean_object* v_start_4928_; lean_object* v_stop_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4942_; 
v_array_4927_ = lean_ctor_get(v_a_4925_, 0);
v_start_4928_ = lean_ctor_get(v_a_4925_, 1);
v_stop_4929_ = lean_ctor_get(v_a_4925_, 2);
v_isSharedCheck_4942_ = !lean_is_exclusive(v_a_4925_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4931_ = v_a_4925_;
v_isShared_4932_ = v_isSharedCheck_4942_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_stop_4929_);
lean_inc(v_start_4928_);
lean_inc(v_array_4927_);
lean_dec(v_a_4925_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4942_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
uint8_t v___x_4933_; 
v___x_4933_ = lean_nat_dec_lt(v_start_4928_, v_stop_4929_);
if (v___x_4933_ == 0)
{
lean_del_object(v___x_4931_);
lean_dec(v_stop_4929_);
lean_dec(v_start_4928_);
lean_dec_ref(v_array_4927_);
return v_b_4926_;
}
else
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4937_; 
v___x_4934_ = lean_unsigned_to_nat(1u);
v___x_4935_ = lean_nat_add(v_start_4928_, v___x_4934_);
lean_inc_ref(v_array_4927_);
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 1, v___x_4935_);
v___x_4937_ = v___x_4931_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_array_4927_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v___x_4935_);
lean_ctor_set(v_reuseFailAlloc_4941_, 2, v_stop_4929_);
v___x_4937_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4938_ = lean_array_fget(v_array_4927_, v_start_4928_);
lean_dec(v_start_4928_);
lean_dec_ref(v_array_4927_);
v___x_4939_ = lean_array_push(v_b_4926_, v___x_4938_);
v_a_4925_ = v___x_4937_;
v_b_4926_ = v___x_4939_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4943_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4944_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4944_);
return v___x_4945_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4946_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4947_ = lean_unsigned_to_nat(0u);
v___x_4948_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
lean_ctor_set(v___x_4948_, 1, v___x_4947_);
lean_ctor_set(v___x_4948_, 2, v___x_4947_);
lean_ctor_set(v___x_4948_, 3, v___x_4946_);
lean_ctor_set(v___x_4948_, 4, v___x_4946_);
lean_ctor_set(v___x_4948_, 5, v___x_4946_);
lean_ctor_set(v___x_4948_, 6, v___x_4946_);
lean_ctor_set(v___x_4948_, 7, v___x_4946_);
lean_ctor_set(v___x_4948_, 8, v___x_4946_);
return v___x_4948_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4949_ = lean_box(1);
v___x_4950_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4951_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4951_);
lean_ctor_set(v___x_4952_, 1, v___x_4950_);
lean_ctor_set(v___x_4952_, 2, v___x_4949_);
return v___x_4952_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4954_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4955_ = l_Lean_stringToMessageData(v___x_4954_);
return v___x_4955_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4957_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4958_ = l_Lean_stringToMessageData(v___x_4957_);
return v___x_4958_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4961_ = l_Lean_stringToMessageData(v___x_4960_);
return v___x_4961_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4963_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4964_ = l_Lean_stringToMessageData(v___x_4963_);
return v___x_4964_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4966_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4967_ = l_Lean_stringToMessageData(v___x_4966_);
return v___x_4967_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4969_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4970_ = l_Lean_stringToMessageData(v___x_4969_);
return v___x_4970_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4972_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4973_ = l_Lean_stringToMessageData(v___x_4972_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4974_, lean_object* v_declHint_4975_, lean_object* v___y_4976_){
_start:
{
lean_object* v___x_4978_; lean_object* v_env_4979_; uint8_t v___x_4980_; 
v___x_4978_ = lean_st_ref_get(v___y_4976_);
v_env_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc_ref(v_env_4979_);
lean_dec(v___x_4978_);
v___x_4980_ = l_Lean_Name_isAnonymous(v_declHint_4975_);
if (v___x_4980_ == 0)
{
uint8_t v_isExporting_4981_; 
v_isExporting_4981_ = lean_ctor_get_uint8(v_env_4979_, sizeof(void*)*8);
if (v_isExporting_4981_ == 0)
{
lean_object* v___x_4982_; 
lean_dec_ref(v_env_4979_);
lean_dec(v_declHint_4975_);
v___x_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4982_, 0, v_msg_4974_);
return v___x_4982_;
}
else
{
lean_object* v___x_4983_; uint8_t v___x_4984_; 
lean_inc_ref(v_env_4979_);
v___x_4983_ = l_Lean_Environment_setExporting(v_env_4979_, v___x_4980_);
lean_inc(v_declHint_4975_);
lean_inc_ref(v___x_4983_);
v___x_4984_ = l_Lean_Environment_contains(v___x_4983_, v_declHint_4975_, v_isExporting_4981_);
if (v___x_4984_ == 0)
{
lean_object* v___x_4985_; 
lean_dec_ref(v___x_4983_);
lean_dec_ref(v_env_4979_);
lean_dec(v_declHint_4975_);
v___x_4985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4985_, 0, v_msg_4974_);
return v___x_4985_;
}
else
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v_c_4991_; lean_object* v___x_4992_; 
v___x_4986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4987_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4988_ = l_Lean_Options_empty;
v___x_4989_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4983_);
lean_ctor_set(v___x_4989_, 1, v___x_4986_);
lean_ctor_set(v___x_4989_, 2, v___x_4987_);
lean_ctor_set(v___x_4989_, 3, v___x_4988_);
lean_inc(v_declHint_4975_);
v___x_4990_ = l_Lean_MessageData_ofConstName(v_declHint_4975_, v___x_4980_);
v_c_4991_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4991_, 0, v___x_4989_);
lean_ctor_set(v_c_4991_, 1, v___x_4990_);
v___x_4992_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4979_, v_declHint_4975_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
lean_dec_ref(v_env_4979_);
lean_dec(v_declHint_4975_);
v___x_4993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
lean_ctor_set(v___x_4994_, 1, v_c_4991_);
v___x_4995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4994_);
lean_ctor_set(v___x_4996_, 1, v___x_4995_);
v___x_4997_ = l_Lean_MessageData_note(v___x_4996_);
v___x_4998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4998_, 0, v_msg_4974_);
lean_ctor_set(v___x_4998_, 1, v___x_4997_);
v___x_4999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4998_);
return v___x_4999_;
}
else
{
lean_object* v_val_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5035_; 
v_val_5000_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5002_ = v___x_4992_;
v_isShared_5003_ = v_isSharedCheck_5035_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_val_5000_);
lean_dec(v___x_4992_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5035_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v_mod_5007_; uint8_t v___x_5008_; 
v___x_5004_ = lean_box(0);
v___x_5005_ = l_Lean_Environment_header(v_env_4979_);
lean_dec_ref(v_env_4979_);
v___x_5006_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5005_);
v_mod_5007_ = lean_array_get(v___x_5004_, v___x_5006_, v_val_5000_);
lean_dec(v_val_5000_);
lean_dec_ref(v___x_5006_);
v___x_5008_ = l_Lean_isPrivateName(v_declHint_4975_);
lean_dec(v_declHint_4975_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5020_; 
v___x_5009_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_5010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
lean_ctor_set(v___x_5010_, 1, v_c_4991_);
v___x_5011_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_5012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5010_);
lean_ctor_set(v___x_5012_, 1, v___x_5011_);
v___x_5013_ = l_Lean_MessageData_ofName(v_mod_5007_);
v___x_5014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5012_);
lean_ctor_set(v___x_5014_, 1, v___x_5013_);
v___x_5015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_5016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5016_, 0, v___x_5014_);
lean_ctor_set(v___x_5016_, 1, v___x_5015_);
v___x_5017_ = l_Lean_MessageData_note(v___x_5016_);
v___x_5018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5018_, 0, v_msg_4974_);
lean_ctor_set(v___x_5018_, 1, v___x_5017_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set_tag(v___x_5002_, 0);
lean_ctor_set(v___x_5002_, 0, v___x_5018_);
v___x_5020_ = v___x_5002_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5018_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
else
{
lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5033_; 
v___x_5022_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_5023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5022_);
lean_ctor_set(v___x_5023_, 1, v_c_4991_);
v___x_5024_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_5025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5023_);
lean_ctor_set(v___x_5025_, 1, v___x_5024_);
v___x_5026_ = l_Lean_MessageData_ofName(v_mod_5007_);
v___x_5027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5027_, 0, v___x_5025_);
lean_ctor_set(v___x_5027_, 1, v___x_5026_);
v___x_5028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_5029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5029_, 0, v___x_5027_);
lean_ctor_set(v___x_5029_, 1, v___x_5028_);
v___x_5030_ = l_Lean_MessageData_note(v___x_5029_);
v___x_5031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5031_, 0, v_msg_4974_);
lean_ctor_set(v___x_5031_, 1, v___x_5030_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set_tag(v___x_5002_, 0);
lean_ctor_set(v___x_5002_, 0, v___x_5031_);
v___x_5033_ = v___x_5002_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v___x_5031_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5036_; 
lean_dec_ref(v_env_4979_);
lean_dec(v_declHint_4975_);
v___x_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5036_, 0, v_msg_4974_);
return v___x_5036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_5037_, lean_object* v_declHint_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5037_, v_declHint_5038_, v___y_5039_);
lean_dec(v___y_5039_);
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_5042_, lean_object* v_declHint_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v___x_5049_; lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5059_; 
v___x_5049_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5042_, v_declHint_5043_, v___y_5047_);
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5052_ = v___x_5049_;
v_isShared_5053_ = v_isSharedCheck_5059_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5049_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5059_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5057_; 
v___x_5054_ = l_Lean_unknownIdentifierMessageTag;
v___x_5055_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5055_, 0, v___x_5054_);
lean_ctor_set(v___x_5055_, 1, v_a_5050_);
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 0, v___x_5055_);
v___x_5057_ = v___x_5052_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5055_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5060_, lean_object* v_declHint_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5060_, v_declHint_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
lean_dec(v___y_5065_);
lean_dec_ref(v___y_5064_);
lean_dec(v___y_5063_);
lean_dec_ref(v___y_5062_);
return v_res_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5068_, lean_object* v_msg_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_){
_start:
{
lean_object* v_fileName_5075_; lean_object* v_fileMap_5076_; lean_object* v_options_5077_; lean_object* v_currRecDepth_5078_; lean_object* v_maxRecDepth_5079_; lean_object* v_ref_5080_; lean_object* v_currNamespace_5081_; lean_object* v_openDecls_5082_; lean_object* v_initHeartbeats_5083_; lean_object* v_maxHeartbeats_5084_; lean_object* v_quotContext_5085_; lean_object* v_currMacroScope_5086_; uint8_t v_diag_5087_; lean_object* v_cancelTk_x3f_5088_; uint8_t v_suppressElabErrors_5089_; lean_object* v_inheritedTraceOptions_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5099_; 
v_fileName_5075_ = lean_ctor_get(v___y_5072_, 0);
v_fileMap_5076_ = lean_ctor_get(v___y_5072_, 1);
v_options_5077_ = lean_ctor_get(v___y_5072_, 2);
v_currRecDepth_5078_ = lean_ctor_get(v___y_5072_, 3);
v_maxRecDepth_5079_ = lean_ctor_get(v___y_5072_, 4);
v_ref_5080_ = lean_ctor_get(v___y_5072_, 5);
v_currNamespace_5081_ = lean_ctor_get(v___y_5072_, 6);
v_openDecls_5082_ = lean_ctor_get(v___y_5072_, 7);
v_initHeartbeats_5083_ = lean_ctor_get(v___y_5072_, 8);
v_maxHeartbeats_5084_ = lean_ctor_get(v___y_5072_, 9);
v_quotContext_5085_ = lean_ctor_get(v___y_5072_, 10);
v_currMacroScope_5086_ = lean_ctor_get(v___y_5072_, 11);
v_diag_5087_ = lean_ctor_get_uint8(v___y_5072_, sizeof(void*)*14);
v_cancelTk_x3f_5088_ = lean_ctor_get(v___y_5072_, 12);
v_suppressElabErrors_5089_ = lean_ctor_get_uint8(v___y_5072_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5090_ = lean_ctor_get(v___y_5072_, 13);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___y_5072_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5092_ = v___y_5072_;
v_isShared_5093_ = v_isSharedCheck_5099_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_inheritedTraceOptions_5090_);
lean_inc(v_cancelTk_x3f_5088_);
lean_inc(v_currMacroScope_5086_);
lean_inc(v_quotContext_5085_);
lean_inc(v_maxHeartbeats_5084_);
lean_inc(v_initHeartbeats_5083_);
lean_inc(v_openDecls_5082_);
lean_inc(v_currNamespace_5081_);
lean_inc(v_ref_5080_);
lean_inc(v_maxRecDepth_5079_);
lean_inc(v_currRecDepth_5078_);
lean_inc(v_options_5077_);
lean_inc(v_fileMap_5076_);
lean_inc(v_fileName_5075_);
lean_dec(v___y_5072_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5099_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v_ref_5094_; lean_object* v___x_5096_; 
v_ref_5094_ = l_Lean_replaceRef(v_ref_5068_, v_ref_5080_);
lean_dec(v_ref_5080_);
if (v_isShared_5093_ == 0)
{
lean_ctor_set(v___x_5092_, 5, v_ref_5094_);
v___x_5096_ = v___x_5092_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_fileName_5075_);
lean_ctor_set(v_reuseFailAlloc_5098_, 1, v_fileMap_5076_);
lean_ctor_set(v_reuseFailAlloc_5098_, 2, v_options_5077_);
lean_ctor_set(v_reuseFailAlloc_5098_, 3, v_currRecDepth_5078_);
lean_ctor_set(v_reuseFailAlloc_5098_, 4, v_maxRecDepth_5079_);
lean_ctor_set(v_reuseFailAlloc_5098_, 5, v_ref_5094_);
lean_ctor_set(v_reuseFailAlloc_5098_, 6, v_currNamespace_5081_);
lean_ctor_set(v_reuseFailAlloc_5098_, 7, v_openDecls_5082_);
lean_ctor_set(v_reuseFailAlloc_5098_, 8, v_initHeartbeats_5083_);
lean_ctor_set(v_reuseFailAlloc_5098_, 9, v_maxHeartbeats_5084_);
lean_ctor_set(v_reuseFailAlloc_5098_, 10, v_quotContext_5085_);
lean_ctor_set(v_reuseFailAlloc_5098_, 11, v_currMacroScope_5086_);
lean_ctor_set(v_reuseFailAlloc_5098_, 12, v_cancelTk_x3f_5088_);
lean_ctor_set(v_reuseFailAlloc_5098_, 13, v_inheritedTraceOptions_5090_);
lean_ctor_set_uint8(v_reuseFailAlloc_5098_, sizeof(void*)*14, v_diag_5087_);
lean_ctor_set_uint8(v_reuseFailAlloc_5098_, sizeof(void*)*14 + 1, v_suppressElabErrors_5089_);
v___x_5096_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5097_; 
v___x_5097_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5069_, v___y_5070_, v___y_5071_, v___x_5096_, v___y_5073_);
lean_dec_ref(v___x_5096_);
return v___x_5097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5100_, lean_object* v_msg_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_){
_start:
{
lean_object* v_res_5107_; 
v_res_5107_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5100_, v_msg_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_);
lean_dec(v___y_5105_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_dec(v_ref_5100_);
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5108_, lean_object* v_msg_5109_, lean_object* v_declHint_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v___x_5116_; lean_object* v_a_5117_; lean_object* v___x_5118_; 
v___x_5116_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5109_, v_declHint_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
v_a_5117_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_a_5117_);
lean_dec_ref(v___x_5116_);
v___x_5118_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5108_, v_a_5117_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5119_, lean_object* v_msg_5120_, lean_object* v_declHint_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
lean_object* v_res_5127_; 
v_res_5127_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5119_, v_msg_5120_, v_declHint_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
lean_dec(v___y_5125_);
lean_dec(v___y_5123_);
lean_dec_ref(v___y_5122_);
lean_dec(v_ref_5119_);
return v_res_5127_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5129_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5130_ = l_Lean_stringToMessageData(v___x_5129_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5131_, lean_object* v_constName_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v___x_5138_; uint8_t v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5138_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5139_ = 0;
lean_inc(v_constName_5132_);
v___x_5140_ = l_Lean_MessageData_ofConstName(v_constName_5132_, v___x_5139_);
v___x_5141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5138_);
lean_ctor_set(v___x_5141_, 1, v___x_5140_);
v___x_5142_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5141_);
lean_ctor_set(v___x_5143_, 1, v___x_5142_);
v___x_5144_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5131_, v___x_5143_, v_constName_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5145_, lean_object* v_constName_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5145_, v_constName_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_);
lean_dec(v___y_5150_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v_ref_5145_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v_ref_5159_; lean_object* v___x_5160_; 
v_ref_5159_ = lean_ctor_get(v___y_5156_, 5);
lean_inc(v_ref_5159_);
v___x_5160_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5159_, v_constName_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
lean_dec(v_ref_5159_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
lean_dec(v___y_5165_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_){
_start:
{
lean_object* v___x_5174_; lean_object* v_env_5175_; uint8_t v___x_5176_; lean_object* v___x_5177_; 
v___x_5174_ = lean_st_ref_get(v___y_5172_);
v_env_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc_ref(v_env_5175_);
lean_dec(v___x_5174_);
v___x_5176_ = 0;
lean_inc(v_constName_5168_);
v___x_5177_ = l_Lean_Environment_find_x3f(v_env_5175_, v_constName_5168_, v___x_5176_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v___x_5178_; 
v___x_5178_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
return v___x_5178_;
}
else
{
lean_object* v_val_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
lean_dec_ref(v___y_5171_);
lean_dec(v_constName_5168_);
v_val_5179_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5177_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_val_5179_);
lean_dec(v___x_5177_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
lean_ctor_set_tag(v___x_5181_, 0);
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_val_5179_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
lean_object* v_res_5193_; 
v_res_5193_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_);
lean_dec(v___y_5191_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5196_, lean_object* v_x_5197_, lean_object* v_x_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
if (lean_obj_tag(v_x_5196_) == 5)
{
lean_object* v_fn_5204_; lean_object* v_arg_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v_fn_5204_ = lean_ctor_get(v_x_5196_, 0);
lean_inc_ref(v_fn_5204_);
v_arg_5205_ = lean_ctor_get(v_x_5196_, 1);
lean_inc_ref(v_arg_5205_);
lean_dec_ref(v_x_5196_);
v___x_5206_ = lean_array_set(v_x_5197_, v_x_5198_, v_arg_5205_);
v___x_5207_ = lean_unsigned_to_nat(1u);
v___x_5208_ = lean_nat_sub(v_x_5198_, v___x_5207_);
lean_dec(v_x_5198_);
v_x_5196_ = v_fn_5204_;
v_x_5197_ = v___x_5206_;
v_x_5198_ = v___x_5208_;
goto _start;
}
else
{
lean_dec(v_x_5198_);
if (lean_obj_tag(v_x_5196_) == 4)
{
lean_object* v_declName_5210_; lean_object* v___x_5211_; 
v_declName_5210_ = lean_ctor_get(v_x_5196_, 0);
lean_inc(v_declName_5210_);
lean_dec_ref(v_x_5196_);
v___x_5211_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5210_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5243_; 
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5214_ = v___x_5211_;
v_isShared_5215_ = v_isSharedCheck_5243_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5211_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5243_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v_lower_5217_; lean_object* v_upper_5218_; 
if (lean_obj_tag(v_a_5212_) == 5)
{
lean_object* v_val_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5240_; 
v_val_5226_ = lean_ctor_get(v_a_5212_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v_a_5212_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5228_ = v_a_5212_;
v_isShared_5229_ = v_isSharedCheck_5240_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_val_5226_);
lean_dec(v_a_5212_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5240_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v_numParams_5230_; lean_object* v_numIndices_5231_; lean_object* v___x_5232_; uint8_t v___x_5233_; 
v_numParams_5230_ = lean_ctor_get(v_val_5226_, 1);
lean_inc(v_numParams_5230_);
v_numIndices_5231_ = lean_ctor_get(v_val_5226_, 2);
lean_inc(v_numIndices_5231_);
lean_dec_ref(v_val_5226_);
v___x_5232_ = lean_unsigned_to_nat(0u);
v___x_5233_ = lean_nat_dec_eq(v_numIndices_5231_, v___x_5232_);
lean_dec(v_numIndices_5231_);
if (v___x_5233_ == 0)
{
lean_object* v___x_5234_; uint8_t v___x_5235_; 
lean_del_object(v___x_5228_);
v___x_5234_ = lean_array_get_size(v_x_5197_);
v___x_5235_ = lean_nat_dec_le(v_numParams_5230_, v___x_5232_);
if (v___x_5235_ == 0)
{
v_lower_5217_ = v_numParams_5230_;
v_upper_5218_ = v___x_5234_;
goto v___jp_5216_;
}
else
{
lean_dec(v_numParams_5230_);
v_lower_5217_ = v___x_5232_;
v_upper_5218_ = v___x_5234_;
goto v___jp_5216_;
}
}
else
{
lean_object* v___x_5236_; lean_object* v___x_5238_; 
lean_dec(v_numParams_5230_);
lean_del_object(v___x_5214_);
lean_dec_ref(v_x_5197_);
v___x_5236_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5229_ == 0)
{
lean_ctor_set_tag(v___x_5228_, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5236_);
v___x_5238_ = v___x_5228_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5236_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
else
{
lean_object* v___x_5241_; lean_object* v___x_5242_; 
lean_del_object(v___x_5214_);
lean_dec(v_a_5212_);
lean_dec_ref(v_x_5197_);
v___x_5241_ = lean_box(0);
v___x_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5242_, 0, v___x_5241_);
return v___x_5242_;
}
v___jp_5216_:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5224_; 
v___x_5219_ = l_Array_toSubarray___redArg(v_x_5197_, v_lower_5217_, v_upper_5218_);
v___x_5220_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5221_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5219_, v___x_5220_);
v___x_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5221_);
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 0, v___x_5222_);
v___x_5224_ = v___x_5214_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v___x_5222_);
v___x_5224_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
return v___x_5224_;
}
}
}
}
else
{
lean_object* v_a_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5251_; 
lean_dec_ref(v_x_5197_);
v_a_5244_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5246_ = v___x_5211_;
v_isShared_5247_ = v_isSharedCheck_5251_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_a_5244_);
lean_dec(v___x_5211_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5251_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v___x_5249_; 
if (v_isShared_5247_ == 0)
{
v___x_5249_ = v___x_5246_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v_a_5244_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
}
}
else
{
lean_object* v___x_5252_; lean_object* v___x_5253_; 
lean_dec_ref(v___y_5201_);
lean_dec_ref(v_x_5197_);
lean_dec_ref(v_x_5196_);
v___x_5252_ = lean_box(0);
v___x_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5253_, 0, v___x_5252_);
return v___x_5253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5254_, lean_object* v_x_5255_, lean_object* v_x_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5254_, v_x_5255_, v_x_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_);
lean_dec(v___y_5260_);
lean_dec(v___y_5258_);
lean_dec_ref(v___y_5257_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_){
_start:
{
lean_object* v___x_5269_; 
lean_inc(v_a_5267_);
lean_inc_ref(v_a_5266_);
lean_inc(v_a_5265_);
lean_inc_ref(v_a_5264_);
v___x_5269_ = lean_infer_type(v_ctorApp_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_);
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_object* v_a_5270_; lean_object* v___x_5271_; 
v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_a_5270_);
lean_dec_ref(v___x_5269_);
lean_inc(v_a_5267_);
lean_inc_ref(v_a_5266_);
lean_inc(v_a_5265_);
lean_inc_ref(v_a_5264_);
v___x_5271_ = l_Lean_Meta_whnfD(v_a_5270_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_);
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_object* v_a_5272_; lean_object* v_dummy_5273_; lean_object* v_nargs_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
lean_inc(v_a_5272_);
lean_dec_ref(v___x_5271_);
v_dummy_5273_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5274_ = l_Lean_Expr_getAppNumArgs(v_a_5272_);
lean_inc(v_nargs_5274_);
v___x_5275_ = lean_mk_array(v_nargs_5274_, v_dummy_5273_);
v___x_5276_ = lean_unsigned_to_nat(1u);
v___x_5277_ = lean_nat_sub(v_nargs_5274_, v___x_5276_);
lean_dec(v_nargs_5274_);
v___x_5278_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5272_, v___x_5275_, v___x_5277_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_);
lean_dec(v_a_5267_);
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
return v___x_5278_;
}
else
{
lean_object* v_a_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5286_; 
lean_dec(v_a_5267_);
lean_dec_ref(v_a_5266_);
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
v_a_5279_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5281_ = v___x_5271_;
v_isShared_5282_ = v_isSharedCheck_5286_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_a_5279_);
lean_dec(v___x_5271_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5286_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
lean_object* v___x_5284_; 
if (v_isShared_5282_ == 0)
{
v___x_5284_ = v___x_5281_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_a_5279_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
}
else
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5294_; 
lean_dec(v_a_5267_);
lean_dec_ref(v_a_5266_);
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
v_a_5287_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5289_ = v___x_5269_;
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5269_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
lean_object* v___x_5292_; 
if (v_isShared_5290_ == 0)
{
v___x_5292_ = v___x_5289_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_a_5287_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5302_, lean_object* v_R_5303_, lean_object* v_a_5304_, lean_object* v_b_5305_){
_start:
{
lean_object* v___x_5306_; 
v___x_5306_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5304_, v_b_5305_);
return v___x_5306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5307_, lean_object* v_constName_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v___x_5314_; 
v___x_5314_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5315_, lean_object* v_constName_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5315_, v_constName_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_);
lean_dec(v___y_5320_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5323_, lean_object* v_ref_5324_, lean_object* v_constName_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
lean_object* v___x_5331_; 
v___x_5331_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5324_, v_constName_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
return v___x_5331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5332_, lean_object* v_ref_5333_, lean_object* v_constName_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5332_, v_ref_5333_, v_constName_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_);
lean_dec(v___y_5338_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
lean_dec(v_ref_5333_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5341_, lean_object* v_ref_5342_, lean_object* v_msg_5343_, lean_object* v_declHint_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_){
_start:
{
lean_object* v___x_5350_; 
v___x_5350_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5342_, v_msg_5343_, v_declHint_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
return v___x_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5351_, lean_object* v_ref_5352_, lean_object* v_msg_5353_, lean_object* v_declHint_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v_res_5360_; 
v_res_5360_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5351_, v_ref_5352_, v_msg_5353_, v_declHint_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_);
lean_dec(v___y_5358_);
lean_dec(v___y_5356_);
lean_dec_ref(v___y_5355_);
lean_dec(v_ref_5352_);
return v_res_5360_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5361_, lean_object* v_declHint_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_){
_start:
{
lean_object* v___x_5368_; 
v___x_5368_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5361_, v_declHint_5362_, v___y_5366_);
return v___x_5368_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5369_, lean_object* v_declHint_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5369_, v_declHint_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5377_, lean_object* v_ref_5378_, lean_object* v_msg_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v___x_5385_; 
v___x_5385_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5378_, v_msg_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
return v___x_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5386_, lean_object* v_ref_5387_, lean_object* v_msg_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_){
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5386_, v_ref_5387_, v_msg_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_);
lean_dec(v___y_5392_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
lean_dec(v_ref_5387_);
return v_res_5394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5395_, lean_object* v_body_5396_, lean_object* v_args2_5397_, lean_object* v_ctorVal_5398_, lean_object* v_args1_5399_, lean_object* v_k_5400_, lean_object* v_arg2_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_){
_start:
{
lean_object* v_res_5407_; 
v_res_5407_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5395_, v_body_5396_, v_args2_5397_, v_ctorVal_5398_, v_args1_5399_, v_k_5400_, v_arg2_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
lean_dec_ref(v_body_5396_);
lean_dec(v_i_5395_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5408_, lean_object* v_args1_5409_, lean_object* v_k_5410_, lean_object* v_i_5411_, lean_object* v_type_5412_, lean_object* v_args2_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_){
_start:
{
lean_object* v___x_5419_; uint8_t v___x_5420_; 
v___x_5419_ = lean_array_get_size(v_args1_5409_);
v___x_5420_ = lean_nat_dec_lt(v_i_5411_, v___x_5419_);
if (v___x_5420_ == 0)
{
lean_object* v___x_5421_; 
lean_dec_ref(v_type_5412_);
lean_dec(v_i_5411_);
lean_dec_ref(v_args1_5409_);
lean_dec_ref(v_ctorVal_5408_);
v___x_5421_ = lean_apply_6(v_k_5410_, v_args2_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, lean_box(0));
return v___x_5421_;
}
else
{
lean_object* v___x_5422_; 
lean_inc(v_a_5417_);
lean_inc_ref(v_a_5416_);
lean_inc(v_a_5415_);
lean_inc_ref(v_a_5414_);
v___x_5422_ = lean_whnf(v_type_5412_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 0);
lean_inc(v_a_5423_);
lean_dec_ref(v___x_5422_);
if (lean_obj_tag(v_a_5423_) == 7)
{
lean_object* v_binderName_5424_; lean_object* v_binderType_5425_; lean_object* v_body_5426_; lean_object* v___f_5427_; uint8_t v___x_5428_; uint8_t v___x_5429_; lean_object* v___x_5430_; 
v_binderName_5424_ = lean_ctor_get(v_a_5423_, 0);
lean_inc(v_binderName_5424_);
v_binderType_5425_ = lean_ctor_get(v_a_5423_, 1);
lean_inc_ref(v_binderType_5425_);
v_body_5426_ = lean_ctor_get(v_a_5423_, 2);
lean_inc_ref(v_body_5426_);
lean_dec_ref(v_a_5423_);
v___f_5427_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5427_, 0, v_i_5411_);
lean_closure_set(v___f_5427_, 1, v_body_5426_);
lean_closure_set(v___f_5427_, 2, v_args2_5413_);
lean_closure_set(v___f_5427_, 3, v_ctorVal_5408_);
lean_closure_set(v___f_5427_, 4, v_args1_5409_);
lean_closure_set(v___f_5427_, 5, v_k_5410_);
v___x_5428_ = 1;
v___x_5429_ = 0;
v___x_5430_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5424_, v___x_5428_, v_binderType_5425_, v___f_5427_, v___x_5429_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_);
return v___x_5430_;
}
else
{
lean_object* v_toConstantVal_5431_; lean_object* v_name_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
lean_dec(v_a_5423_);
lean_dec_ref(v_args2_5413_);
lean_dec(v_i_5411_);
lean_dec_ref(v_k_5410_);
lean_dec_ref(v_args1_5409_);
v_toConstantVal_5431_ = lean_ctor_get(v_ctorVal_5408_, 0);
lean_inc_ref(v_toConstantVal_5431_);
lean_dec_ref(v_ctorVal_5408_);
v_name_5432_ = lean_ctor_get(v_toConstantVal_5431_, 0);
lean_inc(v_name_5432_);
lean_dec_ref(v_toConstantVal_5431_);
v___x_5433_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5434_ = l_Lean_MessageData_ofName(v_name_5432_);
v___x_5435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5435_, 0, v___x_5433_);
lean_ctor_set(v___x_5435_, 1, v___x_5434_);
v___x_5436_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5435_);
lean_ctor_set(v___x_5437_, 1, v___x_5436_);
v___x_5438_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5437_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_);
lean_dec(v_a_5417_);
lean_dec_ref(v_a_5416_);
lean_dec(v_a_5415_);
lean_dec_ref(v_a_5414_);
return v___x_5438_;
}
}
else
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5446_; 
lean_dec(v_a_5417_);
lean_dec_ref(v_a_5416_);
lean_dec(v_a_5415_);
lean_dec_ref(v_a_5414_);
lean_dec_ref(v_args2_5413_);
lean_dec(v_i_5411_);
lean_dec_ref(v_k_5410_);
lean_dec_ref(v_args1_5409_);
lean_dec_ref(v_ctorVal_5408_);
v_a_5439_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5441_ = v___x_5422_;
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5422_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5444_; 
if (v_isShared_5442_ == 0)
{
v___x_5444_ = v___x_5441_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5447_, lean_object* v_body_5448_, lean_object* v_args2_5449_, lean_object* v_ctorVal_5450_, lean_object* v_args1_5451_, lean_object* v_k_5452_, lean_object* v_arg2_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; 
v___x_5459_ = lean_unsigned_to_nat(1u);
v___x_5460_ = lean_nat_add(v_i_5447_, v___x_5459_);
v___x_5461_ = lean_expr_instantiate1(v_body_5448_, v_arg2_5453_);
v___x_5462_ = lean_array_push(v_args2_5449_, v_arg2_5453_);
v___x_5463_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5450_, v_args1_5451_, v_k_5452_, v___x_5460_, v___x_5461_, v___x_5462_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
return v___x_5463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5464_, lean_object* v_args1_5465_, lean_object* v_k_5466_, lean_object* v_i_5467_, lean_object* v_type_5468_, lean_object* v_args2_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5464_, v_args1_5465_, v_k_5466_, v_i_5467_, v_type_5468_, v_args2_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5476_, lean_object* v_us_5477_, lean_object* v_args1_5478_, lean_object* v___x_5479_, lean_object* v_numParams_5480_, lean_object* v___x_5481_, lean_object* v_args2_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_){
_start:
{
lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; 
lean_inc(v_us_5477_);
v___x_5488_ = l_Lean_mkConst(v_name_5476_, v_us_5477_);
lean_inc_ref(v___x_5488_);
v___x_5489_ = l_Lean_mkAppN(v___x_5488_, v_args1_5478_);
v___x_5490_ = l_Lean_mkAppN(v___x_5488_, v_args2_5482_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc_ref(v___x_5490_);
lean_inc_ref(v___x_5489_);
v___x_5491_ = l_Lean_Meta_mkEqHEq(v___x_5489_, v___x_5490_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
if (lean_obj_tag(v___x_5491_) == 0)
{
lean_object* v_a_5492_; lean_object* v___x_5493_; uint8_t v___x_5494_; lean_object* v___x_5495_; 
v_a_5492_ = lean_ctor_get(v___x_5491_, 0);
lean_inc(v_a_5492_);
lean_dec_ref(v___x_5491_);
lean_inc_ref(v_args2_5482_);
v___x_5493_ = l_Array_toSubarray___redArg(v_args2_5482_, v___x_5479_, v_numParams_5480_);
v___x_5494_ = 1;
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc_ref(v_args2_5482_);
v___x_5495_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5478_, v_args2_5482_, v___x_5494_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5616_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5616_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5616_ == 0)
{
v___x_5498_ = v___x_5495_;
v_isShared_5499_ = v_isSharedCheck_5616_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_a_5496_);
lean_dec(v___x_5495_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5616_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v___x_5500_; 
v___x_5500_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5496_);
if (lean_obj_tag(v___x_5500_) == 1)
{
lean_object* v_val_5501_; lean_object* v___x_5502_; 
lean_del_object(v___x_5498_);
v_val_5501_ = lean_ctor_get(v___x_5500_, 0);
lean_inc(v_val_5501_);
lean_dec_ref(v___x_5500_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
v___x_5502_ = l_Lean_mkArrow(v_a_5492_, v_val_5501_, v___y_5485_, v___y_5486_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v_a_5503_; lean_object* v___x_5504_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_a_5503_);
lean_dec_ref(v___x_5502_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
v___x_5504_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5489_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5595_; 
v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5507_ = v___x_5504_;
v_isShared_5508_ = v_isSharedCheck_5595_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5504_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5595_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
if (lean_obj_tag(v_a_5505_) == 1)
{
lean_object* v_val_5509_; lean_object* v___x_5510_; 
lean_del_object(v___x_5507_);
v_val_5509_ = lean_ctor_get(v_a_5505_, 0);
lean_inc(v_val_5509_);
lean_dec_ref(v_a_5505_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
v___x_5510_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5490_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
if (lean_obj_tag(v___x_5510_) == 0)
{
lean_object* v_a_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5582_; 
v_a_5511_ = lean_ctor_get(v___x_5510_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5510_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5513_ = v___x_5510_;
v_isShared_5514_ = v_isSharedCheck_5582_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_a_5511_);
lean_dec(v___x_5510_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5582_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
if (lean_obj_tag(v_a_5511_) == 1)
{
lean_object* v_val_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5577_; 
lean_del_object(v___x_5513_);
v_val_5515_ = lean_ctor_get(v_a_5511_, 0);
v_isSharedCheck_5577_ = !lean_is_exclusive(v_a_5511_);
if (v_isSharedCheck_5577_ == 0)
{
v___x_5517_ = v_a_5511_;
v_isShared_5518_ = v_isSharedCheck_5577_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_val_5515_);
lean_dec(v_a_5511_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5577_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; uint8_t v___x_5523_; lean_object* v___x_5524_; 
v___x_5519_ = l_Subarray_copy___redArg(v___x_5481_);
v___x_5520_ = l_Array_append___redArg(v___x_5519_, v_val_5509_);
v___x_5521_ = l_Subarray_copy___redArg(v___x_5493_);
v___x_5522_ = l_Array_append___redArg(v___x_5521_, v_val_5515_);
lean_dec(v_val_5515_);
v___x_5523_ = 0;
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
v___x_5524_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5520_, v___x_5522_, v___x_5523_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
lean_dec_ref(v___x_5520_);
if (lean_obj_tag(v___x_5524_) == 0)
{
lean_object* v_a_5525_; lean_object* v___x_5526_; 
v_a_5525_ = lean_ctor_get(v___x_5524_, 0);
lean_inc(v_a_5525_);
lean_dec_ref(v___x_5524_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
v___x_5526_ = l_Lean_mkArrowN(v_a_5525_, v_a_5503_, v___y_5485_, v___y_5486_);
lean_dec(v_a_5525_);
if (lean_obj_tag(v___x_5526_) == 0)
{
lean_object* v_a_5527_; uint8_t v___x_5528_; lean_object* v___x_5529_; 
v_a_5527_ = lean_ctor_get(v___x_5526_, 0);
lean_inc(v_a_5527_);
lean_dec_ref(v___x_5526_);
v___x_5528_ = 1;
v___x_5529_ = l_Lean_Meta_mkForallFVars(v_args2_5482_, v_a_5527_, v___x_5523_, v___x_5494_, v___x_5494_, v___x_5528_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
lean_dec_ref(v_args2_5482_);
if (lean_obj_tag(v___x_5529_) == 0)
{
lean_object* v_a_5530_; lean_object* v___x_5531_; 
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
lean_inc(v_a_5530_);
lean_dec_ref(v___x_5529_);
v___x_5531_ = l_Lean_Meta_mkForallFVars(v_args1_5478_, v_a_5530_, v___x_5523_, v___x_5494_, v___x_5494_, v___x_5528_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
if (lean_obj_tag(v___x_5531_) == 0)
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5544_; 
v_a_5532_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5534_ = v___x_5531_;
v_isShared_5535_ = v_isSharedCheck_5544_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5531_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5544_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5539_; 
v___x_5536_ = lean_array_get_size(v_val_5509_);
lean_dec(v_val_5509_);
v___x_5537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5537_, 0, v_a_5532_);
lean_ctor_set(v___x_5537_, 1, v_us_5477_);
lean_ctor_set(v___x_5537_, 2, v___x_5536_);
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 0, v___x_5537_);
v___x_5539_ = v___x_5517_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5537_);
v___x_5539_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
lean_object* v___x_5541_; 
if (v_isShared_5535_ == 0)
{
lean_ctor_set(v___x_5534_, 0, v___x_5539_);
v___x_5541_ = v___x_5534_;
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
lean_object* v_a_5545_; lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5552_; 
lean_del_object(v___x_5517_);
lean_dec(v_val_5509_);
lean_dec(v_us_5477_);
v_a_5545_ = lean_ctor_get(v___x_5531_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5547_ = v___x_5531_;
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_a_5545_);
lean_dec(v___x_5531_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v___x_5550_; 
if (v_isShared_5548_ == 0)
{
v___x_5550_ = v___x_5547_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_a_5545_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
}
else
{
lean_object* v_a_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5560_; 
lean_del_object(v___x_5517_);
lean_dec(v_val_5509_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec(v_us_5477_);
v_a_5553_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5560_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5555_ = v___x_5529_;
v_isShared_5556_ = v_isSharedCheck_5560_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_a_5553_);
lean_dec(v___x_5529_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5560_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5558_; 
if (v_isShared_5556_ == 0)
{
v___x_5558_ = v___x_5555_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_a_5553_);
v___x_5558_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
return v___x_5558_;
}
}
}
}
else
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5568_; 
lean_del_object(v___x_5517_);
lean_dec(v_val_5509_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec(v_us_5477_);
v_a_5561_ = lean_ctor_get(v___x_5526_, 0);
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5526_);
if (v_isSharedCheck_5568_ == 0)
{
v___x_5563_ = v___x_5526_;
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v___x_5526_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5568_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5566_; 
if (v_isShared_5564_ == 0)
{
v___x_5566_ = v___x_5563_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_a_5561_);
v___x_5566_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
return v___x_5566_;
}
}
}
}
else
{
lean_object* v_a_5569_; lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5576_; 
lean_del_object(v___x_5517_);
lean_dec(v_val_5509_);
lean_dec(v_a_5503_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec(v_us_5477_);
v_a_5569_ = lean_ctor_get(v___x_5524_, 0);
v_isSharedCheck_5576_ = !lean_is_exclusive(v___x_5524_);
if (v_isSharedCheck_5576_ == 0)
{
v___x_5571_ = v___x_5524_;
v_isShared_5572_ = v_isSharedCheck_5576_;
goto v_resetjp_5570_;
}
else
{
lean_inc(v_a_5569_);
lean_dec(v___x_5524_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5576_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v___x_5574_; 
if (v_isShared_5572_ == 0)
{
v___x_5574_ = v___x_5571_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_a_5569_);
v___x_5574_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
return v___x_5574_;
}
}
}
}
}
else
{
lean_object* v___x_5578_; lean_object* v___x_5580_; 
lean_dec(v_a_5511_);
lean_dec(v_val_5509_);
lean_dec(v_a_5503_);
lean_dec_ref(v___x_5493_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec_ref(v___x_5481_);
lean_dec(v_us_5477_);
v___x_5578_ = lean_box(0);
if (v_isShared_5514_ == 0)
{
lean_ctor_set(v___x_5513_, 0, v___x_5578_);
v___x_5580_ = v___x_5513_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v___x_5578_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
}
else
{
lean_object* v_a_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5590_; 
lean_dec(v_val_5509_);
lean_dec(v_a_5503_);
lean_dec_ref(v___x_5493_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec_ref(v___x_5481_);
lean_dec(v_us_5477_);
v_a_5583_ = lean_ctor_get(v___x_5510_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v___x_5510_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5585_ = v___x_5510_;
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_a_5583_);
lean_dec(v___x_5510_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v___x_5588_; 
if (v_isShared_5586_ == 0)
{
v___x_5588_ = v___x_5585_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
return v___x_5588_;
}
}
}
}
else
{
lean_object* v___x_5591_; lean_object* v___x_5593_; 
lean_dec(v_a_5505_);
lean_dec(v_a_5503_);
lean_dec_ref(v___x_5493_);
lean_dec_ref(v___x_5490_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec_ref(v___x_5481_);
lean_dec(v_us_5477_);
v___x_5591_ = lean_box(0);
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 0, v___x_5591_);
v___x_5593_ = v___x_5507_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5591_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
}
else
{
lean_object* v_a_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5603_; 
lean_dec(v_a_5503_);
lean_dec_ref(v___x_5493_);
lean_dec_ref(v___x_5490_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec_ref(v___x_5481_);
lean_dec(v_us_5477_);
v_a_5596_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5603_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5603_ == 0)
{
v___x_5598_ = v___x_5504_;
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_a_5596_);
lean_dec(v___x_5504_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v___x_5601_; 
if (v_isShared_5599_ == 0)
{
v___x_5601_ = v___x_5598_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5596_);
v___x_5601_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
return v___x_5601_;
}
}
}
}
else
{
lean_object* v_a_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5611_; 
lean_dec_ref(v___x_5493_);
lean_dec_ref(v___x_5490_);
lean_dec_ref(v___x_5489_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec_ref(v___x_5481_);
lean_dec(v_us_5477_);
v_a_5604_ = lean_ctor_get(v___x_5502_, 0);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5606_ = v___x_5502_;
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_a_5604_);
lean_dec(v___x_5502_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5609_; 
if (v_isShared_5607_ == 0)
{
v___x_5609_ = v___x_5606_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5604_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
else
{
lean_object* v___x_5612_; lean_object* v___x_5614_; 
lean_dec(v___x_5500_);
lean_dec_ref(v___x_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v___x_5490_);
lean_dec_ref(v___x_5489_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec_ref(v___x_5481_);
lean_dec(v_us_5477_);
v___x_5612_ = lean_box(0);
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 0, v___x_5612_);
v___x_5614_ = v___x_5498_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v___x_5612_);
v___x_5614_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
return v___x_5614_;
}
}
}
}
else
{
lean_object* v_a_5617_; lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5624_; 
lean_dec_ref(v___x_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v___x_5490_);
lean_dec_ref(v___x_5489_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec_ref(v___x_5481_);
lean_dec(v_us_5477_);
v_a_5617_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5624_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5624_ == 0)
{
v___x_5619_ = v___x_5495_;
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
else
{
lean_inc(v_a_5617_);
lean_dec(v___x_5495_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v___x_5622_; 
if (v_isShared_5620_ == 0)
{
v___x_5622_ = v___x_5619_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5617_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
else
{
lean_object* v_a_5625_; lean_object* v___x_5627_; uint8_t v_isShared_5628_; uint8_t v_isSharedCheck_5632_; 
lean_dec_ref(v___x_5490_);
lean_dec_ref(v___x_5489_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec_ref(v_args2_5482_);
lean_dec_ref(v___x_5481_);
lean_dec(v_numParams_5480_);
lean_dec(v___x_5479_);
lean_dec(v_us_5477_);
v_a_5625_ = lean_ctor_get(v___x_5491_, 0);
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5491_);
if (v_isSharedCheck_5632_ == 0)
{
v___x_5627_ = v___x_5491_;
v_isShared_5628_ = v_isSharedCheck_5632_;
goto v_resetjp_5626_;
}
else
{
lean_inc(v_a_5625_);
lean_dec(v___x_5491_);
v___x_5627_ = lean_box(0);
v_isShared_5628_ = v_isSharedCheck_5632_;
goto v_resetjp_5626_;
}
v_resetjp_5626_:
{
lean_object* v___x_5630_; 
if (v_isShared_5628_ == 0)
{
v___x_5630_ = v___x_5627_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_a_5625_);
v___x_5630_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
return v___x_5630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5633_, lean_object* v_us_5634_, lean_object* v_args1_5635_, lean_object* v___x_5636_, lean_object* v_numParams_5637_, lean_object* v___x_5638_, lean_object* v_args2_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_){
_start:
{
lean_object* v_res_5645_; 
v_res_5645_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5633_, v_us_5634_, v_args1_5635_, v___x_5636_, v_numParams_5637_, v___x_5638_, v_args2_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_);
lean_dec_ref(v_args1_5635_);
return v_res_5645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5646_, lean_object* v_name_5647_, lean_object* v_us_5648_, lean_object* v_ctorVal_5649_, lean_object* v_a_5650_, lean_object* v_args1_5651_, lean_object* v_x_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_){
_start:
{
lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___f_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; 
v___x_5658_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5646_);
lean_inc_ref(v_args1_5651_);
v___x_5659_ = l_Array_toSubarray___redArg(v_args1_5651_, v___x_5658_, v_numParams_5646_);
lean_inc_ref(v_args1_5651_);
v___f_5660_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5660_, 0, v_name_5647_);
lean_closure_set(v___f_5660_, 1, v_us_5648_);
lean_closure_set(v___f_5660_, 2, v_args1_5651_);
lean_closure_set(v___f_5660_, 3, v___x_5658_);
lean_closure_set(v___f_5660_, 4, v_numParams_5646_);
lean_closure_set(v___f_5660_, 5, v___x_5659_);
v___x_5661_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
lean_inc_ref(v_args1_5651_);
v___x_5662_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5662_, 0, v_ctorVal_5649_);
lean_closure_set(v___x_5662_, 1, v_args1_5651_);
lean_closure_set(v___x_5662_, 2, v___f_5660_);
lean_closure_set(v___x_5662_, 3, v___x_5658_);
lean_closure_set(v___x_5662_, 4, v_a_5650_);
lean_closure_set(v___x_5662_, 5, v___x_5661_);
v___x_5663_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5651_, v___x_5662_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_);
return v___x_5663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5664_, lean_object* v_name_5665_, lean_object* v_us_5666_, lean_object* v_ctorVal_5667_, lean_object* v_a_5668_, lean_object* v_args1_5669_, lean_object* v_x_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_){
_start:
{
lean_object* v_res_5676_; 
v_res_5676_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5664_, v_name_5665_, v_us_5666_, v_ctorVal_5667_, v_a_5668_, v_args1_5669_, v_x_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
lean_dec_ref(v_x_5670_);
return v_res_5676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_){
_start:
{
lean_object* v_toConstantVal_5683_; lean_object* v_numParams_5684_; lean_object* v_name_5685_; lean_object* v_levelParams_5686_; lean_object* v_type_5687_; lean_object* v___x_5688_; 
v_toConstantVal_5683_ = lean_ctor_get(v_ctorVal_5677_, 0);
v_numParams_5684_ = lean_ctor_get(v_ctorVal_5677_, 3);
lean_inc(v_numParams_5684_);
v_name_5685_ = lean_ctor_get(v_toConstantVal_5683_, 0);
lean_inc(v_name_5685_);
v_levelParams_5686_ = lean_ctor_get(v_toConstantVal_5683_, 1);
v_type_5687_ = lean_ctor_get(v_toConstantVal_5683_, 2);
lean_inc(v_a_5681_);
lean_inc_ref(v_a_5680_);
lean_inc_ref(v_type_5687_);
v___x_5688_ = l_Lean_Meta_elimOptParam(v_type_5687_, v_a_5680_, v_a_5681_);
if (lean_obj_tag(v___x_5688_) == 0)
{
lean_object* v_a_5689_; lean_object* v___x_5690_; lean_object* v_us_5691_; lean_object* v___f_5692_; uint8_t v___x_5693_; lean_object* v___x_5694_; 
v_a_5689_ = lean_ctor_get(v___x_5688_, 0);
lean_inc(v_a_5689_);
lean_dec_ref(v___x_5688_);
v___x_5690_ = lean_box(0);
lean_inc(v_levelParams_5686_);
v_us_5691_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5686_, v___x_5690_);
lean_inc(v_a_5689_);
v___f_5692_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5692_, 0, v_numParams_5684_);
lean_closure_set(v___f_5692_, 1, v_name_5685_);
lean_closure_set(v___f_5692_, 2, v_us_5691_);
lean_closure_set(v___f_5692_, 3, v_ctorVal_5677_);
lean_closure_set(v___f_5692_, 4, v_a_5689_);
v___x_5693_ = 0;
v___x_5694_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5689_, v___f_5692_, v___x_5693_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_);
return v___x_5694_;
}
else
{
lean_object* v_a_5695_; lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5702_; 
lean_dec(v_name_5685_);
lean_dec(v_numParams_5684_);
lean_dec(v_a_5681_);
lean_dec_ref(v_a_5680_);
lean_dec(v_a_5679_);
lean_dec_ref(v_a_5678_);
lean_dec_ref(v_ctorVal_5677_);
v_a_5695_ = lean_ctor_get(v___x_5688_, 0);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5697_ = v___x_5688_;
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
else
{
lean_inc(v_a_5695_);
lean_dec(v___x_5688_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v___x_5700_; 
if (v_isShared_5698_ == 0)
{
v___x_5700_ = v___x_5697_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_a_5695_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_){
_start:
{
lean_object* v_res_5709_; 
v_res_5709_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_);
return v_res_5709_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5711_; lean_object* v___x_5712_; 
v___x_5711_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5712_ = l_Lean_stringToMessageData(v___x_5711_);
return v___x_5712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_){
_start:
{
lean_object* v_toConstantVal_5719_; lean_object* v_name_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; 
v_toConstantVal_5719_ = lean_ctor_get(v_ctorVal_5713_, 0);
lean_inc_ref(v_toConstantVal_5719_);
lean_dec_ref(v_ctorVal_5713_);
v_name_5720_ = lean_ctor_get(v_toConstantVal_5719_, 0);
lean_inc(v_name_5720_);
lean_dec_ref(v_toConstantVal_5719_);
v___x_5721_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5722_ = l_Lean_MessageData_ofName(v_name_5720_);
v___x_5723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5721_);
lean_ctor_set(v___x_5723_, 1, v___x_5722_);
v___x_5724_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5725_, 0, v___x_5723_);
lean_ctor_set(v___x_5725_, 1, v___x_5724_);
v___x_5726_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5725_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_);
return v___x_5726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_){
_start:
{
lean_object* v_res_5733_; 
v_res_5733_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5727_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
lean_dec(v_a_5729_);
lean_dec_ref(v_a_5728_);
return v_res_5733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5734_, lean_object* v_ctorVal_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_){
_start:
{
lean_object* v___x_5741_; 
v___x_5741_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_);
return v___x_5741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5742_, lean_object* v_ctorVal_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_){
_start:
{
lean_object* v_res_5749_; 
v_res_5749_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5742_, v_ctorVal_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_);
lean_dec(v_a_5747_);
lean_dec_ref(v_a_5746_);
lean_dec(v_a_5745_);
lean_dec_ref(v_a_5744_);
return v_res_5749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5755_, size_t v_sz_5756_, size_t v_i_5757_, lean_object* v_bs_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_){
_start:
{
uint8_t v___x_5764_; 
v___x_5764_ = lean_usize_dec_lt(v_i_5757_, v_sz_5756_);
if (v___x_5764_ == 0)
{
lean_object* v___x_5765_; 
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec_ref(v_ctorVal_5755_);
v___x_5765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5765_, 0, v_bs_5758_);
return v___x_5765_;
}
else
{
lean_object* v_v_5766_; lean_object* v___x_5767_; 
v_v_5766_ = lean_array_uget_borrowed(v_bs_5758_, v_i_5757_);
lean_inc(v___y_5762_);
lean_inc_ref(v___y_5761_);
lean_inc(v___y_5760_);
lean_inc_ref(v___y_5759_);
lean_inc(v_v_5766_);
v___x_5767_ = lean_infer_type(v_v_5766_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
if (lean_obj_tag(v___x_5767_) == 0)
{
lean_object* v_a_5768_; lean_object* v___x_5769_; 
v_a_5768_ = lean_ctor_get(v___x_5767_, 0);
lean_inc(v_a_5768_);
lean_dec_ref(v___x_5767_);
v___x_5769_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5768_, v___y_5760_);
if (lean_obj_tag(v___x_5769_) == 0)
{
lean_object* v_a_5770_; lean_object* v___x_5771_; lean_object* v_bs_x27_5772_; lean_object* v_a_5774_; lean_object* v___y_5780_; lean_object* v_lhs_5791_; lean_object* v_rhs_5792_; lean_object* v___x_5794_; uint8_t v___x_5795_; 
v_a_5770_ = lean_ctor_get(v___x_5769_, 0);
lean_inc(v_a_5770_);
lean_dec_ref(v___x_5769_);
v___x_5771_ = lean_unsigned_to_nat(0u);
v_bs_x27_5772_ = lean_array_uset(v_bs_5758_, v_i_5757_, v___x_5771_);
v___x_5794_ = l_Lean_Expr_cleanupAnnotations(v_a_5770_);
v___x_5795_ = l_Lean_Expr_isApp(v___x_5794_);
if (v___x_5795_ == 0)
{
lean_object* v___x_5796_; 
lean_dec_ref(v___x_5794_);
lean_inc_ref(v_ctorVal_5755_);
v___x_5796_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5755_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
v___y_5780_ = v___x_5796_;
goto v___jp_5779_;
}
else
{
lean_object* v_arg_5797_; lean_object* v___x_5798_; uint8_t v___x_5799_; 
v_arg_5797_ = lean_ctor_get(v___x_5794_, 1);
lean_inc_ref(v_arg_5797_);
v___x_5798_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5794_);
v___x_5799_ = l_Lean_Expr_isApp(v___x_5798_);
if (v___x_5799_ == 0)
{
lean_object* v___x_5800_; 
lean_dec_ref(v___x_5798_);
lean_dec_ref(v_arg_5797_);
lean_inc_ref(v_ctorVal_5755_);
v___x_5800_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5755_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
v___y_5780_ = v___x_5800_;
goto v___jp_5779_;
}
else
{
lean_object* v_arg_5801_; lean_object* v___x_5802_; uint8_t v___x_5803_; 
v_arg_5801_ = lean_ctor_get(v___x_5798_, 1);
lean_inc_ref(v_arg_5801_);
v___x_5802_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5798_);
v___x_5803_ = l_Lean_Expr_isApp(v___x_5802_);
if (v___x_5803_ == 0)
{
lean_object* v___x_5804_; 
lean_dec_ref(v___x_5802_);
lean_dec_ref(v_arg_5801_);
lean_dec_ref(v_arg_5797_);
lean_inc_ref(v_ctorVal_5755_);
v___x_5804_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5755_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
v___y_5780_ = v___x_5804_;
goto v___jp_5779_;
}
else
{
lean_object* v_arg_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; uint8_t v___x_5808_; 
v_arg_5805_ = lean_ctor_get(v___x_5802_, 1);
lean_inc_ref(v_arg_5805_);
v___x_5806_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5802_);
v___x_5807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5808_ = l_Lean_Expr_isConstOf(v___x_5806_, v___x_5807_);
if (v___x_5808_ == 0)
{
uint8_t v___x_5809_; 
lean_dec_ref(v_arg_5801_);
v___x_5809_ = l_Lean_Expr_isApp(v___x_5806_);
if (v___x_5809_ == 0)
{
lean_object* v___x_5810_; 
lean_dec_ref(v___x_5806_);
lean_dec_ref(v_arg_5805_);
lean_dec_ref(v_arg_5797_);
lean_inc_ref(v_ctorVal_5755_);
v___x_5810_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5755_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
v___y_5780_ = v___x_5810_;
goto v___jp_5779_;
}
else
{
lean_object* v___x_5811_; lean_object* v___x_5812_; uint8_t v___x_5813_; 
v___x_5811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5806_);
v___x_5812_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5813_ = l_Lean_Expr_isConstOf(v___x_5811_, v___x_5812_);
lean_dec_ref(v___x_5811_);
if (v___x_5813_ == 0)
{
lean_object* v___x_5814_; 
lean_dec_ref(v_arg_5805_);
lean_dec_ref(v_arg_5797_);
lean_inc_ref(v_ctorVal_5755_);
v___x_5814_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5755_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
v___y_5780_ = v___x_5814_;
goto v___jp_5779_;
}
else
{
v_lhs_5791_ = v_arg_5805_;
v_rhs_5792_ = v_arg_5797_;
goto v___jp_5790_;
}
}
}
else
{
lean_dec_ref(v___x_5806_);
lean_dec_ref(v_arg_5805_);
v_lhs_5791_ = v_arg_5801_;
v_rhs_5792_ = v_arg_5797_;
goto v___jp_5790_;
}
}
}
}
v___jp_5773_:
{
size_t v___x_5775_; size_t v___x_5776_; lean_object* v___x_5777_; 
v___x_5775_ = ((size_t)1ULL);
v___x_5776_ = lean_usize_add(v_i_5757_, v___x_5775_);
v___x_5777_ = lean_array_uset(v_bs_x27_5772_, v_i_5757_, v_a_5774_);
v_i_5757_ = v___x_5776_;
v_bs_5758_ = v___x_5777_;
goto _start;
}
v___jp_5779_:
{
if (lean_obj_tag(v___y_5780_) == 0)
{
lean_object* v_a_5781_; 
v_a_5781_ = lean_ctor_get(v___y_5780_, 0);
lean_inc(v_a_5781_);
lean_dec_ref(v___y_5780_);
v_a_5774_ = v_a_5781_;
goto v___jp_5773_;
}
else
{
lean_object* v_a_5782_; lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5789_; 
lean_dec_ref(v_bs_x27_5772_);
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec_ref(v_ctorVal_5755_);
v_a_5782_ = lean_ctor_get(v___y_5780_, 0);
v_isSharedCheck_5789_ = !lean_is_exclusive(v___y_5780_);
if (v_isSharedCheck_5789_ == 0)
{
v___x_5784_ = v___y_5780_;
v_isShared_5785_ = v_isSharedCheck_5789_;
goto v_resetjp_5783_;
}
else
{
lean_inc(v_a_5782_);
lean_dec(v___y_5780_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5789_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
lean_object* v___x_5787_; 
if (v_isShared_5785_ == 0)
{
v___x_5787_ = v___x_5784_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_a_5782_);
v___x_5787_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
return v___x_5787_;
}
}
}
}
v___jp_5790_:
{
lean_object* v___x_5793_; 
v___x_5793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5793_, 0, v_lhs_5791_);
lean_ctor_set(v___x_5793_, 1, v_rhs_5792_);
v_a_5774_ = v___x_5793_;
goto v___jp_5773_;
}
}
else
{
lean_object* v_a_5815_; lean_object* v___x_5817_; uint8_t v_isShared_5818_; uint8_t v_isSharedCheck_5822_; 
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec_ref(v_bs_5758_);
lean_dec_ref(v_ctorVal_5755_);
v_a_5815_ = lean_ctor_get(v___x_5769_, 0);
v_isSharedCheck_5822_ = !lean_is_exclusive(v___x_5769_);
if (v_isSharedCheck_5822_ == 0)
{
v___x_5817_ = v___x_5769_;
v_isShared_5818_ = v_isSharedCheck_5822_;
goto v_resetjp_5816_;
}
else
{
lean_inc(v_a_5815_);
lean_dec(v___x_5769_);
v___x_5817_ = lean_box(0);
v_isShared_5818_ = v_isSharedCheck_5822_;
goto v_resetjp_5816_;
}
v_resetjp_5816_:
{
lean_object* v___x_5820_; 
if (v_isShared_5818_ == 0)
{
v___x_5820_ = v___x_5817_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v_a_5815_);
v___x_5820_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
return v___x_5820_;
}
}
}
}
else
{
lean_object* v_a_5823_; lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5830_; 
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec_ref(v_bs_5758_);
lean_dec_ref(v_ctorVal_5755_);
v_a_5823_ = lean_ctor_get(v___x_5767_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v___x_5767_);
if (v_isSharedCheck_5830_ == 0)
{
v___x_5825_ = v___x_5767_;
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_a_5823_);
lean_dec(v___x_5767_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5830_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
lean_object* v___x_5828_; 
if (v_isShared_5826_ == 0)
{
v___x_5828_ = v___x_5825_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_a_5823_);
v___x_5828_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
return v___x_5828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5831_, lean_object* v_sz_5832_, lean_object* v_i_5833_, lean_object* v_bs_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_){
_start:
{
size_t v_sz_boxed_5840_; size_t v_i_boxed_5841_; lean_object* v_res_5842_; 
v_sz_boxed_5840_ = lean_unbox_usize(v_sz_5832_);
lean_dec(v_sz_5832_);
v_i_boxed_5841_ = lean_unbox_usize(v_i_5833_);
lean_dec(v_i_5833_);
v_res_5842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5831_, v_sz_boxed_5840_, v_i_boxed_5841_, v_bs_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
return v_res_5842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5844_ = lean_unsigned_to_nat(0u);
v___x_5845_ = l_Lean_Level_ofNat(v___x_5844_);
return v___x_5845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5846_, lean_object* v_us_5847_, lean_object* v_numIndices_5848_, lean_object* v_xs_5849_, lean_object* v_type_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_){
_start:
{
lean_object* v_toConstantVal_5856_; lean_object* v_induct_5857_; lean_object* v_numParams_5858_; lean_object* v___x_5859_; lean_object* v_noConfusionName_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v_noConfusion_5864_; lean_object* v_noConfusion_5865_; lean_object* v_lower_5867_; lean_object* v_upper_5868_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v_n_5979_; uint8_t v___x_5980_; 
v_toConstantVal_5856_ = lean_ctor_get(v_ctorVal_5846_, 0);
v_induct_5857_ = lean_ctor_get(v_ctorVal_5846_, 1);
v_numParams_5858_ = lean_ctor_get(v_ctorVal_5846_, 3);
v___x_5859_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5857_);
v_noConfusionName_5860_ = l_Lean_Name_str___override(v_induct_5857_, v___x_5859_);
v___x_5861_ = lean_unsigned_to_nat(0u);
v___x_5862_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5863_, 0, v___x_5862_);
lean_ctor_set(v___x_5863_, 1, v_us_5847_);
v_noConfusion_5864_ = l_Lean_mkConst(v_noConfusionName_5860_, v___x_5863_);
v_noConfusion_5865_ = l_Lean_Expr_app___override(v_noConfusion_5864_, v_type_5850_);
v___x_5975_ = lean_array_get_size(v_xs_5849_);
v___x_5976_ = lean_nat_sub(v___x_5975_, v_numParams_5858_);
v___x_5977_ = lean_nat_sub(v___x_5976_, v_numIndices_5848_);
lean_dec(v___x_5976_);
v___x_5978_ = lean_unsigned_to_nat(1u);
v_n_5979_ = lean_nat_sub(v___x_5977_, v___x_5978_);
lean_dec(v___x_5977_);
v___x_5980_ = lean_nat_dec_le(v_n_5979_, v___x_5861_);
if (v___x_5980_ == 0)
{
v_lower_5867_ = v_n_5979_;
v_upper_5868_ = v___x_5975_;
goto v___jp_5866_;
}
else
{
lean_dec(v_n_5979_);
v_lower_5867_ = v___x_5861_;
v_upper_5868_ = v___x_5975_;
goto v___jp_5866_;
}
v___jp_5866_:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v_eqs_5871_; size_t v_sz_5872_; size_t v___x_5873_; lean_object* v___x_5874_; 
lean_inc_ref(v_xs_5849_);
v___x_5869_ = l_Array_toSubarray___redArg(v_xs_5849_, v_lower_5867_, v_upper_5868_);
v___x_5870_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5871_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5869_, v___x_5870_);
v_sz_5872_ = lean_array_size(v_eqs_5871_);
v___x_5873_ = ((size_t)0ULL);
lean_inc(v___y_5854_);
lean_inc_ref(v___y_5853_);
lean_inc(v___y_5852_);
lean_inc_ref(v___y_5851_);
lean_inc_ref(v_eqs_5871_);
lean_inc_ref(v_ctorVal_5846_);
v___x_5874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5846_, v_sz_5872_, v___x_5873_, v_eqs_5871_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
if (lean_obj_tag(v___x_5874_) == 0)
{
lean_object* v_a_5875_; lean_object* v___x_5876_; lean_object* v_fst_5877_; lean_object* v_snd_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; 
v_a_5875_ = lean_ctor_get(v___x_5874_, 0);
lean_inc(v_a_5875_);
lean_dec_ref(v___x_5874_);
v___x_5876_ = l_Array_unzip___redArg(v_a_5875_);
lean_dec(v_a_5875_);
v_fst_5877_ = lean_ctor_get(v___x_5876_, 0);
lean_inc(v_fst_5877_);
v_snd_5878_ = lean_ctor_get(v___x_5876_, 1);
lean_inc(v_snd_5878_);
lean_dec_ref(v___x_5876_);
v___x_5879_ = l_Lean_mkAppN(v_noConfusion_5865_, v_fst_5877_);
lean_dec(v_fst_5877_);
v___x_5880_ = l_Lean_mkAppN(v___x_5879_, v_snd_5878_);
lean_dec(v_snd_5878_);
v___x_5881_ = l_Lean_mkAppN(v___x_5880_, v_eqs_5871_);
lean_dec_ref(v_eqs_5871_);
lean_inc(v___y_5854_);
lean_inc_ref(v___y_5853_);
lean_inc(v___y_5852_);
lean_inc_ref(v___y_5851_);
lean_inc_ref(v___x_5881_);
v___x_5882_ = lean_infer_type(v___x_5881_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
if (lean_obj_tag(v___x_5882_) == 0)
{
lean_object* v_a_5883_; lean_object* v___x_5884_; 
v_a_5883_ = lean_ctor_get(v___x_5882_, 0);
lean_inc(v_a_5883_);
lean_dec_ref(v___x_5882_);
lean_inc(v___y_5854_);
lean_inc_ref(v___y_5853_);
lean_inc(v___y_5852_);
lean_inc_ref(v___y_5851_);
v___x_5884_ = lean_whnf(v_a_5883_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
if (lean_obj_tag(v___x_5884_) == 0)
{
lean_object* v_a_5885_; 
v_a_5885_ = lean_ctor_get(v___x_5884_, 0);
lean_inc(v_a_5885_);
lean_dec_ref(v___x_5884_);
if (lean_obj_tag(v_a_5885_) == 7)
{
lean_object* v_binderType_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; 
lean_inc_ref(v_toConstantVal_5856_);
lean_dec_ref(v_ctorVal_5846_);
v_binderType_5886_ = lean_ctor_get(v_a_5885_, 1);
lean_inc_ref(v_binderType_5886_);
lean_dec_ref(v_a_5885_);
v___x_5887_ = lean_box(0);
lean_inc_ref(v___y_5851_);
v___x_5888_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5886_, v___x_5887_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
if (lean_obj_tag(v___x_5888_) == 0)
{
lean_object* v_a_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
v_a_5889_ = lean_ctor_get(v___x_5888_, 0);
lean_inc(v_a_5889_);
lean_dec_ref(v___x_5888_);
v___x_5890_ = l_Lean_Expr_mvarId_x21(v_a_5889_);
lean_inc(v___y_5854_);
lean_inc_ref(v___y_5853_);
lean_inc(v___y_5852_);
lean_inc_ref(v___y_5851_);
v___x_5891_ = l_Lean_MVarId_intros(v___x_5890_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
if (lean_obj_tag(v___x_5891_) == 0)
{
lean_object* v_a_5892_; lean_object* v_snd_5893_; lean_object* v_name_5894_; lean_object* v___x_5895_; 
v_a_5892_ = lean_ctor_get(v___x_5891_, 0);
lean_inc(v_a_5892_);
lean_dec_ref(v___x_5891_);
v_snd_5893_ = lean_ctor_get(v_a_5892_, 1);
lean_inc(v_snd_5893_);
lean_dec(v_a_5892_);
v_name_5894_ = lean_ctor_get(v_toConstantVal_5856_, 0);
lean_inc(v_name_5894_);
lean_dec_ref(v_toConstantVal_5856_);
lean_inc(v___y_5854_);
lean_inc_ref(v___y_5853_);
lean_inc(v___y_5852_);
lean_inc_ref(v___y_5851_);
v___x_5895_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5893_, v_name_5894_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
if (lean_obj_tag(v___x_5895_) == 0)
{
lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v_a_5898_; lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5925_; 
lean_dec_ref(v___x_5895_);
v___x_5896_ = l_Lean_Expr_app___override(v___x_5881_, v_a_5889_);
v___x_5897_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5896_, v___y_5852_);
v_a_5898_ = lean_ctor_get(v___x_5897_, 0);
v_isSharedCheck_5925_ = !lean_is_exclusive(v___x_5897_);
if (v_isSharedCheck_5925_ == 0)
{
v___x_5900_ = v___x_5897_;
v_isShared_5901_ = v_isSharedCheck_5925_;
goto v_resetjp_5899_;
}
else
{
lean_inc(v_a_5898_);
lean_dec(v___x_5897_);
v___x_5900_ = lean_box(0);
v_isShared_5901_ = v_isSharedCheck_5925_;
goto v_resetjp_5899_;
}
v_resetjp_5899_:
{
uint8_t v___x_5902_; uint8_t v___x_5903_; uint8_t v___x_5904_; lean_object* v___x_5905_; 
v___x_5902_ = 0;
v___x_5903_ = 1;
v___x_5904_ = 1;
v___x_5905_ = l_Lean_Meta_mkLambdaFVars(v_xs_5849_, v_a_5898_, v___x_5902_, v___x_5903_, v___x_5902_, v___x_5903_, v___x_5904_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
lean_dec_ref(v_xs_5849_);
if (lean_obj_tag(v___x_5905_) == 0)
{
lean_object* v_a_5906_; lean_object* v___x_5908_; uint8_t v_isShared_5909_; uint8_t v_isSharedCheck_5916_; 
v_a_5906_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_5916_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_5916_ == 0)
{
v___x_5908_ = v___x_5905_;
v_isShared_5909_ = v_isSharedCheck_5916_;
goto v_resetjp_5907_;
}
else
{
lean_inc(v_a_5906_);
lean_dec(v___x_5905_);
v___x_5908_ = lean_box(0);
v_isShared_5909_ = v_isSharedCheck_5916_;
goto v_resetjp_5907_;
}
v_resetjp_5907_:
{
lean_object* v___x_5911_; 
if (v_isShared_5901_ == 0)
{
lean_ctor_set_tag(v___x_5900_, 1);
lean_ctor_set(v___x_5900_, 0, v_a_5906_);
v___x_5911_ = v___x_5900_;
goto v_reusejp_5910_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_a_5906_);
v___x_5911_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5910_;
}
v_reusejp_5910_:
{
lean_object* v___x_5913_; 
if (v_isShared_5909_ == 0)
{
lean_ctor_set(v___x_5908_, 0, v___x_5911_);
v___x_5913_ = v___x_5908_;
goto v_reusejp_5912_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v___x_5911_);
v___x_5913_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5912_;
}
v_reusejp_5912_:
{
return v___x_5913_;
}
}
}
}
else
{
lean_object* v_a_5917_; lean_object* v___x_5919_; uint8_t v_isShared_5920_; uint8_t v_isSharedCheck_5924_; 
lean_del_object(v___x_5900_);
v_a_5917_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_5924_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_5924_ == 0)
{
v___x_5919_ = v___x_5905_;
v_isShared_5920_ = v_isSharedCheck_5924_;
goto v_resetjp_5918_;
}
else
{
lean_inc(v_a_5917_);
lean_dec(v___x_5905_);
v___x_5919_ = lean_box(0);
v_isShared_5920_ = v_isSharedCheck_5924_;
goto v_resetjp_5918_;
}
v_resetjp_5918_:
{
lean_object* v___x_5922_; 
if (v_isShared_5920_ == 0)
{
v___x_5922_ = v___x_5919_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_a_5917_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
return v___x_5922_;
}
}
}
}
}
else
{
lean_object* v_a_5926_; lean_object* v___x_5928_; uint8_t v_isShared_5929_; uint8_t v_isSharedCheck_5933_; 
lean_dec(v_a_5889_);
lean_dec_ref(v___x_5881_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
lean_dec_ref(v_xs_5849_);
v_a_5926_ = lean_ctor_get(v___x_5895_, 0);
v_isSharedCheck_5933_ = !lean_is_exclusive(v___x_5895_);
if (v_isSharedCheck_5933_ == 0)
{
v___x_5928_ = v___x_5895_;
v_isShared_5929_ = v_isSharedCheck_5933_;
goto v_resetjp_5927_;
}
else
{
lean_inc(v_a_5926_);
lean_dec(v___x_5895_);
v___x_5928_ = lean_box(0);
v_isShared_5929_ = v_isSharedCheck_5933_;
goto v_resetjp_5927_;
}
v_resetjp_5927_:
{
lean_object* v___x_5931_; 
if (v_isShared_5929_ == 0)
{
v___x_5931_ = v___x_5928_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_a_5926_);
v___x_5931_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
return v___x_5931_;
}
}
}
}
else
{
lean_object* v_a_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5941_; 
lean_dec(v_a_5889_);
lean_dec_ref(v___x_5881_);
lean_dec_ref(v_toConstantVal_5856_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
lean_dec_ref(v_xs_5849_);
v_a_5934_ = lean_ctor_get(v___x_5891_, 0);
v_isSharedCheck_5941_ = !lean_is_exclusive(v___x_5891_);
if (v_isSharedCheck_5941_ == 0)
{
v___x_5936_ = v___x_5891_;
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_a_5934_);
lean_dec(v___x_5891_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
lean_object* v___x_5939_; 
if (v_isShared_5937_ == 0)
{
v___x_5939_ = v___x_5936_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_a_5934_);
v___x_5939_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
return v___x_5939_;
}
}
}
}
else
{
lean_object* v_a_5942_; lean_object* v___x_5944_; uint8_t v_isShared_5945_; uint8_t v_isSharedCheck_5949_; 
lean_dec_ref(v___x_5881_);
lean_dec_ref(v_toConstantVal_5856_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
lean_dec_ref(v_xs_5849_);
v_a_5942_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5949_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5949_ == 0)
{
v___x_5944_ = v___x_5888_;
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
else
{
lean_inc(v_a_5942_);
lean_dec(v___x_5888_);
v___x_5944_ = lean_box(0);
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
v_resetjp_5943_:
{
lean_object* v___x_5947_; 
if (v_isShared_5945_ == 0)
{
v___x_5947_ = v___x_5944_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v_a_5942_);
v___x_5947_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
return v___x_5947_;
}
}
}
}
else
{
lean_object* v___x_5950_; 
lean_dec(v_a_5885_);
lean_dec_ref(v___x_5881_);
lean_dec_ref(v_xs_5849_);
v___x_5950_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5846_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
return v___x_5950_;
}
}
else
{
lean_object* v_a_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_5958_; 
lean_dec_ref(v___x_5881_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
lean_dec_ref(v_xs_5849_);
lean_dec_ref(v_ctorVal_5846_);
v_a_5951_ = lean_ctor_get(v___x_5884_, 0);
v_isSharedCheck_5958_ = !lean_is_exclusive(v___x_5884_);
if (v_isSharedCheck_5958_ == 0)
{
v___x_5953_ = v___x_5884_;
v_isShared_5954_ = v_isSharedCheck_5958_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_a_5951_);
lean_dec(v___x_5884_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_5958_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
lean_object* v___x_5956_; 
if (v_isShared_5954_ == 0)
{
v___x_5956_ = v___x_5953_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_a_5951_);
v___x_5956_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
return v___x_5956_;
}
}
}
}
else
{
lean_object* v_a_5959_; lean_object* v___x_5961_; uint8_t v_isShared_5962_; uint8_t v_isSharedCheck_5966_; 
lean_dec_ref(v___x_5881_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
lean_dec_ref(v_xs_5849_);
lean_dec_ref(v_ctorVal_5846_);
v_a_5959_ = lean_ctor_get(v___x_5882_, 0);
v_isSharedCheck_5966_ = !lean_is_exclusive(v___x_5882_);
if (v_isSharedCheck_5966_ == 0)
{
v___x_5961_ = v___x_5882_;
v_isShared_5962_ = v_isSharedCheck_5966_;
goto v_resetjp_5960_;
}
else
{
lean_inc(v_a_5959_);
lean_dec(v___x_5882_);
v___x_5961_ = lean_box(0);
v_isShared_5962_ = v_isSharedCheck_5966_;
goto v_resetjp_5960_;
}
v_resetjp_5960_:
{
lean_object* v___x_5964_; 
if (v_isShared_5962_ == 0)
{
v___x_5964_ = v___x_5961_;
goto v_reusejp_5963_;
}
else
{
lean_object* v_reuseFailAlloc_5965_; 
v_reuseFailAlloc_5965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5965_, 0, v_a_5959_);
v___x_5964_ = v_reuseFailAlloc_5965_;
goto v_reusejp_5963_;
}
v_reusejp_5963_:
{
return v___x_5964_;
}
}
}
}
else
{
lean_object* v_a_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5974_; 
lean_dec_ref(v_eqs_5871_);
lean_dec_ref(v_noConfusion_5865_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
lean_dec_ref(v_xs_5849_);
lean_dec_ref(v_ctorVal_5846_);
v_a_5967_ = lean_ctor_get(v___x_5874_, 0);
v_isSharedCheck_5974_ = !lean_is_exclusive(v___x_5874_);
if (v_isSharedCheck_5974_ == 0)
{
v___x_5969_ = v___x_5874_;
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_a_5967_);
lean_dec(v___x_5874_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5972_; 
if (v_isShared_5970_ == 0)
{
v___x_5972_ = v___x_5969_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_a_5967_);
v___x_5972_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
return v___x_5972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5981_, lean_object* v_us_5982_, lean_object* v_numIndices_5983_, lean_object* v_xs_5984_, lean_object* v_type_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_){
_start:
{
lean_object* v_res_5991_; 
v_res_5991_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5981_, v_us_5982_, v_numIndices_5983_, v_xs_5984_, v_type_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_);
lean_dec(v_numIndices_5983_);
return v_res_5991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5992_, lean_object* v_typeInfo_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_){
_start:
{
lean_object* v_thmType_5999_; lean_object* v_us_6000_; lean_object* v_numIndices_6001_; lean_object* v___f_6002_; uint8_t v___x_6003_; lean_object* v___x_6004_; 
v_thmType_5999_ = lean_ctor_get(v_typeInfo_5993_, 0);
lean_inc_ref(v_thmType_5999_);
v_us_6000_ = lean_ctor_get(v_typeInfo_5993_, 1);
lean_inc(v_us_6000_);
v_numIndices_6001_ = lean_ctor_get(v_typeInfo_5993_, 2);
lean_inc(v_numIndices_6001_);
lean_dec_ref(v_typeInfo_5993_);
v___f_6002_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6002_, 0, v_ctorVal_5992_);
lean_closure_set(v___f_6002_, 1, v_us_6000_);
lean_closure_set(v___f_6002_, 2, v_numIndices_6001_);
v___x_6003_ = 0;
v___x_6004_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5999_, v___f_6002_, v___x_6003_, v___x_6003_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_);
return v___x_6004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_6005_, lean_object* v_typeInfo_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_){
_start:
{
lean_object* v_res_6012_; 
v_res_6012_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_6005_, v_typeInfo_6006_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_);
return v_res_6012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_6015_){
_start:
{
lean_object* v___x_6016_; lean_object* v___x_6017_; 
v___x_6016_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6017_ = l_Lean_Name_str___override(v_ctorName_6015_, v___x_6016_);
return v___x_6017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_6018_, lean_object* v_ctorVal_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_){
_start:
{
lean_object* v___x_6025_; 
lean_inc(v_a_6023_);
lean_inc_ref(v_a_6022_);
lean_inc(v_a_6021_);
lean_inc_ref(v_a_6020_);
lean_inc_ref(v_ctorVal_6019_);
v___x_6025_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_);
if (lean_obj_tag(v___x_6025_) == 0)
{
lean_object* v_a_6026_; lean_object* v___x_6028_; uint8_t v_isShared_6029_; uint8_t v_isSharedCheck_6087_; 
v_a_6026_ = lean_ctor_get(v___x_6025_, 0);
v_isSharedCheck_6087_ = !lean_is_exclusive(v___x_6025_);
if (v_isSharedCheck_6087_ == 0)
{
v___x_6028_ = v___x_6025_;
v_isShared_6029_ = v_isSharedCheck_6087_;
goto v_resetjp_6027_;
}
else
{
lean_inc(v_a_6026_);
lean_dec(v___x_6025_);
v___x_6028_ = lean_box(0);
v_isShared_6029_ = v_isSharedCheck_6087_;
goto v_resetjp_6027_;
}
v_resetjp_6027_:
{
if (lean_obj_tag(v_a_6026_) == 1)
{
lean_object* v_val_6030_; lean_object* v___x_6031_; 
lean_del_object(v___x_6028_);
v_val_6030_ = lean_ctor_get(v_a_6026_, 0);
lean_inc(v_val_6030_);
lean_dec_ref(v_a_6026_);
lean_inc(v_val_6030_);
lean_inc_ref(v_ctorVal_6019_);
v___x_6031_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_6019_, v_val_6030_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_);
if (lean_obj_tag(v___x_6031_) == 0)
{
lean_object* v_a_6032_; lean_object* v___x_6034_; uint8_t v_isShared_6035_; uint8_t v_isSharedCheck_6074_; 
v_a_6032_ = lean_ctor_get(v___x_6031_, 0);
v_isSharedCheck_6074_ = !lean_is_exclusive(v___x_6031_);
if (v_isSharedCheck_6074_ == 0)
{
v___x_6034_ = v___x_6031_;
v_isShared_6035_ = v_isSharedCheck_6074_;
goto v_resetjp_6033_;
}
else
{
lean_inc(v_a_6032_);
lean_dec(v___x_6031_);
v___x_6034_ = lean_box(0);
v_isShared_6035_ = v_isSharedCheck_6074_;
goto v_resetjp_6033_;
}
v_resetjp_6033_:
{
if (lean_obj_tag(v_a_6032_) == 1)
{
lean_object* v_toConstantVal_6036_; lean_object* v_val_6037_; lean_object* v___x_6039_; uint8_t v_isShared_6040_; uint8_t v_isSharedCheck_6069_; 
v_toConstantVal_6036_ = lean_ctor_get(v_ctorVal_6019_, 0);
lean_inc_ref(v_toConstantVal_6036_);
lean_dec_ref(v_ctorVal_6019_);
v_val_6037_ = lean_ctor_get(v_a_6032_, 0);
v_isSharedCheck_6069_ = !lean_is_exclusive(v_a_6032_);
if (v_isSharedCheck_6069_ == 0)
{
v___x_6039_ = v_a_6032_;
v_isShared_6040_ = v_isSharedCheck_6069_;
goto v_resetjp_6038_;
}
else
{
lean_inc(v_val_6037_);
lean_dec(v_a_6032_);
v___x_6039_ = lean_box(0);
v_isShared_6040_ = v_isSharedCheck_6069_;
goto v_resetjp_6038_;
}
v_resetjp_6038_:
{
lean_object* v_levelParams_6041_; lean_object* v___x_6043_; uint8_t v_isShared_6044_; uint8_t v_isSharedCheck_6066_; 
v_levelParams_6041_ = lean_ctor_get(v_toConstantVal_6036_, 1);
v_isSharedCheck_6066_ = !lean_is_exclusive(v_toConstantVal_6036_);
if (v_isSharedCheck_6066_ == 0)
{
lean_object* v_unused_6067_; lean_object* v_unused_6068_; 
v_unused_6067_ = lean_ctor_get(v_toConstantVal_6036_, 2);
lean_dec(v_unused_6067_);
v_unused_6068_ = lean_ctor_get(v_toConstantVal_6036_, 0);
lean_dec(v_unused_6068_);
v___x_6043_ = v_toConstantVal_6036_;
v_isShared_6044_ = v_isSharedCheck_6066_;
goto v_resetjp_6042_;
}
else
{
lean_inc(v_levelParams_6041_);
lean_dec(v_toConstantVal_6036_);
v___x_6043_ = lean_box(0);
v_isShared_6044_ = v_isSharedCheck_6066_;
goto v_resetjp_6042_;
}
v_resetjp_6042_:
{
lean_object* v_thmType_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6063_; 
v_thmType_6045_ = lean_ctor_get(v_val_6030_, 0);
v_isSharedCheck_6063_ = !lean_is_exclusive(v_val_6030_);
if (v_isSharedCheck_6063_ == 0)
{
lean_object* v_unused_6064_; lean_object* v_unused_6065_; 
v_unused_6064_ = lean_ctor_get(v_val_6030_, 2);
lean_dec(v_unused_6064_);
v_unused_6065_ = lean_ctor_get(v_val_6030_, 1);
lean_dec(v_unused_6065_);
v___x_6047_ = v_val_6030_;
v_isShared_6048_ = v_isSharedCheck_6063_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_thmType_6045_);
lean_dec(v_val_6030_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6063_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v___x_6050_; 
lean_inc(v_thmName_6018_);
if (v_isShared_6044_ == 0)
{
lean_ctor_set(v___x_6043_, 2, v_thmType_6045_);
lean_ctor_set(v___x_6043_, 0, v_thmName_6018_);
v___x_6050_ = v___x_6043_;
goto v_reusejp_6049_;
}
else
{
lean_object* v_reuseFailAlloc_6062_; 
v_reuseFailAlloc_6062_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_thmName_6018_);
lean_ctor_set(v_reuseFailAlloc_6062_, 1, v_levelParams_6041_);
lean_ctor_set(v_reuseFailAlloc_6062_, 2, v_thmType_6045_);
v___x_6050_ = v_reuseFailAlloc_6062_;
goto v_reusejp_6049_;
}
v_reusejp_6049_:
{
lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6054_; 
v___x_6051_ = lean_box(0);
v___x_6052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6052_, 0, v_thmName_6018_);
lean_ctor_set(v___x_6052_, 1, v___x_6051_);
if (v_isShared_6048_ == 0)
{
lean_ctor_set(v___x_6047_, 2, v___x_6052_);
lean_ctor_set(v___x_6047_, 1, v_val_6037_);
lean_ctor_set(v___x_6047_, 0, v___x_6050_);
v___x_6054_ = v___x_6047_;
goto v_reusejp_6053_;
}
else
{
lean_object* v_reuseFailAlloc_6061_; 
v_reuseFailAlloc_6061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6061_, 0, v___x_6050_);
lean_ctor_set(v_reuseFailAlloc_6061_, 1, v_val_6037_);
lean_ctor_set(v_reuseFailAlloc_6061_, 2, v___x_6052_);
v___x_6054_ = v_reuseFailAlloc_6061_;
goto v_reusejp_6053_;
}
v_reusejp_6053_:
{
lean_object* v___x_6056_; 
if (v_isShared_6040_ == 0)
{
lean_ctor_set(v___x_6039_, 0, v___x_6054_);
v___x_6056_ = v___x_6039_;
goto v_reusejp_6055_;
}
else
{
lean_object* v_reuseFailAlloc_6060_; 
v_reuseFailAlloc_6060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6060_, 0, v___x_6054_);
v___x_6056_ = v_reuseFailAlloc_6060_;
goto v_reusejp_6055_;
}
v_reusejp_6055_:
{
lean_object* v___x_6058_; 
if (v_isShared_6035_ == 0)
{
lean_ctor_set(v___x_6034_, 0, v___x_6056_);
v___x_6058_ = v___x_6034_;
goto v_reusejp_6057_;
}
else
{
lean_object* v_reuseFailAlloc_6059_; 
v_reuseFailAlloc_6059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6059_, 0, v___x_6056_);
v___x_6058_ = v_reuseFailAlloc_6059_;
goto v_reusejp_6057_;
}
v_reusejp_6057_:
{
return v___x_6058_;
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
lean_object* v___x_6070_; lean_object* v___x_6072_; 
lean_dec(v_a_6032_);
lean_dec(v_val_6030_);
lean_dec_ref(v_ctorVal_6019_);
lean_dec(v_thmName_6018_);
v___x_6070_ = lean_box(0);
if (v_isShared_6035_ == 0)
{
lean_ctor_set(v___x_6034_, 0, v___x_6070_);
v___x_6072_ = v___x_6034_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6073_; 
v_reuseFailAlloc_6073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6073_, 0, v___x_6070_);
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
lean_dec(v_val_6030_);
lean_dec_ref(v_ctorVal_6019_);
lean_dec(v_thmName_6018_);
v_a_6075_ = lean_ctor_get(v___x_6031_, 0);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___x_6031_);
if (v_isSharedCheck_6082_ == 0)
{
v___x_6077_ = v___x_6031_;
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
else
{
lean_inc(v_a_6075_);
lean_dec(v___x_6031_);
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
lean_object* v___x_6083_; lean_object* v___x_6085_; 
lean_dec(v_a_6026_);
lean_dec(v_a_6023_);
lean_dec_ref(v_a_6022_);
lean_dec(v_a_6021_);
lean_dec_ref(v_a_6020_);
lean_dec_ref(v_ctorVal_6019_);
lean_dec(v_thmName_6018_);
v___x_6083_ = lean_box(0);
if (v_isShared_6029_ == 0)
{
lean_ctor_set(v___x_6028_, 0, v___x_6083_);
v___x_6085_ = v___x_6028_;
goto v_reusejp_6084_;
}
else
{
lean_object* v_reuseFailAlloc_6086_; 
v_reuseFailAlloc_6086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6086_, 0, v___x_6083_);
v___x_6085_ = v_reuseFailAlloc_6086_;
goto v_reusejp_6084_;
}
v_reusejp_6084_:
{
return v___x_6085_;
}
}
}
}
else
{
lean_object* v_a_6088_; lean_object* v___x_6090_; uint8_t v_isShared_6091_; uint8_t v_isSharedCheck_6095_; 
lean_dec(v_a_6023_);
lean_dec_ref(v_a_6022_);
lean_dec(v_a_6021_);
lean_dec_ref(v_a_6020_);
lean_dec_ref(v_ctorVal_6019_);
lean_dec(v_thmName_6018_);
v_a_6088_ = lean_ctor_get(v___x_6025_, 0);
v_isSharedCheck_6095_ = !lean_is_exclusive(v___x_6025_);
if (v_isSharedCheck_6095_ == 0)
{
v___x_6090_ = v___x_6025_;
v_isShared_6091_ = v_isSharedCheck_6095_;
goto v_resetjp_6089_;
}
else
{
lean_inc(v_a_6088_);
lean_dec(v___x_6025_);
v___x_6090_ = lean_box(0);
v_isShared_6091_ = v_isSharedCheck_6095_;
goto v_resetjp_6089_;
}
v_resetjp_6089_:
{
lean_object* v___x_6093_; 
if (v_isShared_6091_ == 0)
{
v___x_6093_ = v___x_6090_;
goto v_reusejp_6092_;
}
else
{
lean_object* v_reuseFailAlloc_6094_; 
v_reuseFailAlloc_6094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6094_, 0, v_a_6088_);
v___x_6093_ = v_reuseFailAlloc_6094_;
goto v_reusejp_6092_;
}
v_reusejp_6092_:
{
return v___x_6093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6096_, lean_object* v_ctorVal_6097_, lean_object* v_a_6098_, lean_object* v_a_6099_, lean_object* v_a_6100_, lean_object* v_a_6101_, lean_object* v_a_6102_){
_start:
{
lean_object* v_res_6103_; 
v_res_6103_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6096_, v_ctorVal_6097_, v_a_6098_, v_a_6099_, v_a_6100_, v_a_6101_);
return v_res_6103_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6104_, lean_object* v_n_6105_){
_start:
{
if (lean_obj_tag(v_n_6105_) == 1)
{
lean_object* v_pre_6106_; lean_object* v_str_6107_; lean_object* v___x_6108_; uint8_t v___x_6109_; 
v_pre_6106_ = lean_ctor_get(v_n_6105_, 0);
lean_inc(v_pre_6106_);
v_str_6107_ = lean_ctor_get(v_n_6105_, 1);
lean_inc_ref(v_str_6107_);
lean_dec_ref(v_n_6105_);
v___x_6108_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6109_ = lean_string_dec_eq(v_str_6107_, v___x_6108_);
lean_dec_ref(v_str_6107_);
if (v___x_6109_ == 0)
{
lean_dec(v_pre_6106_);
lean_dec_ref(v_env_6104_);
return v___x_6109_;
}
else
{
uint8_t v___x_6110_; lean_object* v___x_6111_; 
v___x_6110_ = 0;
v___x_6111_ = l_Lean_Environment_find_x3f(v_env_6104_, v_pre_6106_, v___x_6110_);
if (lean_obj_tag(v___x_6111_) == 1)
{
lean_object* v_val_6112_; 
v_val_6112_ = lean_ctor_get(v___x_6111_, 0);
lean_inc(v_val_6112_);
lean_dec_ref(v___x_6111_);
if (lean_obj_tag(v_val_6112_) == 6)
{
lean_dec_ref(v_val_6112_);
return v___x_6109_;
}
else
{
lean_dec(v_val_6112_);
return v___x_6110_;
}
}
else
{
lean_dec(v___x_6111_);
return v___x_6110_;
}
}
}
else
{
uint8_t v___x_6113_; 
lean_dec(v_n_6105_);
lean_dec_ref(v_env_6104_);
v___x_6113_ = 0;
return v___x_6113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6114_, lean_object* v_n_6115_){
_start:
{
uint8_t v_res_6116_; lean_object* v_r_6117_; 
v_res_6116_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6114_, v_n_6115_);
v_r_6117_ = lean_box(v_res_6116_);
return v_r_6117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6120_; lean_object* v___x_6121_; 
v___f_6120_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6121_ = l_Lean_registerReservedNamePredicate(v___f_6120_);
return v___x_6121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6122_){
_start:
{
lean_object* v_res_6123_; 
v_res_6123_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6123_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6124_, lean_object* v___y_6125_){
_start:
{
lean_object* v___x_6127_; lean_object* v_env_6128_; lean_object* v_toConstantVal_6129_; lean_object* v_value_6130_; lean_object* v_all_6131_; uint8_t v___y_6133_; lean_object* v_type_6141_; uint8_t v___x_6142_; 
v___x_6127_ = lean_st_ref_get(v___y_6125_);
v_env_6128_ = lean_ctor_get(v___x_6127_, 0);
lean_inc_ref(v_env_6128_);
lean_dec(v___x_6127_);
v_toConstantVal_6129_ = lean_ctor_get(v_thm_6124_, 0);
v_value_6130_ = lean_ctor_get(v_thm_6124_, 1);
v_all_6131_ = lean_ctor_get(v_thm_6124_, 2);
v_type_6141_ = lean_ctor_get(v_toConstantVal_6129_, 2);
lean_inc_ref(v_env_6128_);
v___x_6142_ = l_Lean_Environment_hasUnsafe(v_env_6128_, v_type_6141_);
if (v___x_6142_ == 0)
{
uint8_t v___x_6143_; 
v___x_6143_ = l_Lean_Environment_hasUnsafe(v_env_6128_, v_value_6130_);
v___y_6133_ = v___x_6143_;
goto v___jp_6132_;
}
else
{
lean_dec_ref(v_env_6128_);
v___y_6133_ = v___x_6142_;
goto v___jp_6132_;
}
v___jp_6132_:
{
if (v___y_6133_ == 0)
{
lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6134_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6134_, 0, v_thm_6124_);
v___x_6135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
return v___x_6135_;
}
else
{
lean_object* v___x_6136_; uint8_t v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; 
lean_inc(v_all_6131_);
lean_inc_ref(v_value_6130_);
lean_inc_ref(v_toConstantVal_6129_);
lean_dec_ref(v_thm_6124_);
v___x_6136_ = lean_box(0);
v___x_6137_ = 0;
v___x_6138_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6138_, 0, v_toConstantVal_6129_);
lean_ctor_set(v___x_6138_, 1, v_value_6130_);
lean_ctor_set(v___x_6138_, 2, v___x_6136_);
lean_ctor_set(v___x_6138_, 3, v_all_6131_);
lean_ctor_set_uint8(v___x_6138_, sizeof(void*)*4, v___x_6137_);
v___x_6139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6138_);
v___x_6140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6139_);
return v___x_6140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_){
_start:
{
lean_object* v_res_6147_; 
v_res_6147_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6144_, v___y_6145_);
lean_dec(v___y_6145_);
return v_res_6147_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_){
_start:
{
lean_object* v___x_6154_; 
v___x_6154_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6148_, v___y_6152_);
return v___x_6154_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_){
_start:
{
lean_object* v_res_6161_; 
v_res_6161_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_);
lean_dec(v___y_6159_);
lean_dec_ref(v___y_6158_);
lean_dec(v___y_6157_);
lean_dec_ref(v___y_6156_);
return v_res_6161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6162_, uint8_t v___x_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_){
_start:
{
lean_object* v___x_6169_; lean_object* v_a_6170_; lean_object* v___x_6171_; 
v___x_6169_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6162_, v___y_6167_);
v_a_6170_ = lean_ctor_get(v___x_6169_, 0);
lean_inc(v_a_6170_);
lean_dec_ref(v___x_6169_);
v___x_6171_ = l_Lean_addDecl(v_a_6170_, v___x_6163_, v___y_6166_, v___y_6167_);
return v___x_6171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6172_, lean_object* v___x_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_){
_start:
{
uint8_t v___x_2361__boxed_6179_; lean_object* v_res_6180_; 
v___x_2361__boxed_6179_ = lean_unbox(v___x_6173_);
v_res_6180_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6172_, v___x_2361__boxed_6179_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
return v_res_6180_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; 
v___x_6183_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6184_ = lean_unsigned_to_nat(0u);
v___x_6185_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_6185_, 0, v___x_6184_);
lean_ctor_set(v___x_6185_, 1, v___x_6184_);
lean_ctor_set(v___x_6185_, 2, v___x_6184_);
lean_ctor_set(v___x_6185_, 3, v___x_6183_);
lean_ctor_set(v___x_6185_, 4, v___x_6183_);
lean_ctor_set(v___x_6185_, 5, v___x_6183_);
lean_ctor_set(v___x_6185_, 6, v___x_6183_);
lean_ctor_set(v___x_6185_, 7, v___x_6183_);
lean_ctor_set(v___x_6185_, 8, v___x_6183_);
return v___x_6185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6186_; lean_object* v___x_6187_; 
v___x_6186_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6187_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6186_);
lean_ctor_set(v___x_6187_, 1, v___x_6186_);
lean_ctor_set(v___x_6187_, 2, v___x_6186_);
lean_ctor_set(v___x_6187_, 3, v___x_6186_);
lean_ctor_set(v___x_6187_, 4, v___x_6186_);
lean_ctor_set(v___x_6187_, 5, v___x_6186_);
return v___x_6187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6188_; lean_object* v___x_6189_; 
v___x_6188_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6188_);
lean_ctor_set(v___x_6189_, 1, v___x_6188_);
lean_ctor_set(v___x_6189_, 2, v___x_6188_);
lean_ctor_set(v___x_6189_, 3, v___x_6188_);
lean_ctor_set(v___x_6189_, 4, v___x_6188_);
return v___x_6189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6190_, lean_object* v_name_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_){
_start:
{
if (lean_obj_tag(v_name_6191_) == 1)
{
lean_object* v_pre_6203_; lean_object* v_str_6204_; lean_object* v___x_6205_; uint8_t v___x_6206_; 
v_pre_6203_ = lean_ctor_get(v_name_6191_, 0);
lean_inc(v_pre_6203_);
v_str_6204_ = lean_ctor_get(v_name_6191_, 1);
v___x_6205_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6206_ = lean_string_dec_eq(v_str_6204_, v___x_6205_);
if (v___x_6206_ == 0)
{
lean_dec_ref(v_name_6191_);
lean_dec(v_pre_6203_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v___x_6190_);
goto v___jp_6199_;
}
else
{
lean_object* v___x_6207_; lean_object* v_env_6208_; uint8_t v___x_6209_; lean_object* v___x_6210_; 
v___x_6207_ = lean_st_ref_get(v___y_6193_);
v_env_6208_ = lean_ctor_get(v___x_6207_, 0);
lean_inc_ref(v_env_6208_);
lean_dec(v___x_6207_);
v___x_6209_ = 0;
lean_inc(v_pre_6203_);
v___x_6210_ = l_Lean_Environment_find_x3f(v_env_6208_, v_pre_6203_, v___x_6209_);
if (lean_obj_tag(v___x_6210_) == 1)
{
lean_object* v_val_6211_; 
v_val_6211_ = lean_ctor_get(v___x_6210_, 0);
lean_inc(v_val_6211_);
lean_dec_ref(v___x_6210_);
if (lean_obj_tag(v_val_6211_) == 6)
{
lean_object* v_val_6212_; lean_object* v___x_6214_; uint8_t v_isShared_6215_; uint8_t v_isSharedCheck_6257_; 
v_val_6212_ = lean_ctor_get(v_val_6211_, 0);
v_isSharedCheck_6257_ = !lean_is_exclusive(v_val_6211_);
if (v_isSharedCheck_6257_ == 0)
{
v___x_6214_ = v_val_6211_;
v_isShared_6215_ = v_isSharedCheck_6257_;
goto v_resetjp_6213_;
}
else
{
lean_inc(v_val_6212_);
lean_dec(v_val_6211_);
v___x_6214_ = lean_box(0);
v_isShared_6215_ = v_isSharedCheck_6257_;
goto v_resetjp_6213_;
}
v_resetjp_6213_:
{
lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; uint8_t v_a_6229_; lean_object* v___x_6235_; 
v___x_6216_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_6217_ = lean_unsigned_to_nat(0u);
v___x_6218_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6219_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6220_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6221_ = lean_box(0);
lean_inc(v___x_6190_);
v___x_6222_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6222_, 0, v___x_6216_);
lean_ctor_set(v___x_6222_, 1, v___x_6190_);
lean_ctor_set(v___x_6222_, 2, v___x_6219_);
lean_ctor_set(v___x_6222_, 3, v___x_6220_);
lean_ctor_set(v___x_6222_, 4, v___x_6221_);
lean_ctor_set(v___x_6222_, 5, v___x_6217_);
lean_ctor_set(v___x_6222_, 6, v___x_6221_);
lean_ctor_set_uint8(v___x_6222_, sizeof(void*)*7, v___x_6209_);
lean_ctor_set_uint8(v___x_6222_, sizeof(void*)*7 + 1, v___x_6209_);
lean_ctor_set_uint8(v___x_6222_, sizeof(void*)*7 + 2, v___x_6209_);
lean_ctor_set_uint8(v___x_6222_, sizeof(void*)*7 + 3, v___x_6206_);
v___x_6223_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6224_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6225_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6226_, 0, v___x_6223_);
lean_ctor_set(v___x_6226_, 1, v___x_6224_);
lean_ctor_set(v___x_6226_, 2, v___x_6190_);
lean_ctor_set(v___x_6226_, 3, v___x_6218_);
lean_ctor_set(v___x_6226_, 4, v___x_6225_);
v___x_6227_ = lean_st_mk_ref(v___x_6226_);
lean_inc(v___y_6193_);
lean_inc_ref(v___y_6192_);
lean_inc(v___x_6227_);
lean_inc_ref(v___x_6222_);
lean_inc_ref(v_name_6191_);
v___x_6235_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6191_, v_val_6212_, v___x_6222_, v___x_6227_, v___y_6192_, v___y_6193_);
if (lean_obj_tag(v___x_6235_) == 0)
{
lean_object* v_a_6236_; 
v_a_6236_ = lean_ctor_get(v___x_6235_, 0);
lean_inc(v_a_6236_);
lean_dec_ref(v___x_6235_);
if (lean_obj_tag(v_a_6236_) == 1)
{
lean_object* v_val_6237_; lean_object* v___x_6238_; lean_object* v___f_6239_; lean_object* v___x_6240_; 
v_val_6237_ = lean_ctor_get(v_a_6236_, 0);
lean_inc(v_val_6237_);
lean_dec_ref(v_a_6236_);
v___x_6238_ = lean_box(v___x_6209_);
v___f_6239_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6239_, 0, v_val_6237_);
lean_closure_set(v___f_6239_, 1, v___x_6238_);
lean_inc(v___x_6227_);
v___x_6240_ = l_Lean_Meta_realizeConst(v_pre_6203_, v_name_6191_, v___f_6239_, v___x_6222_, v___x_6227_, v___y_6192_, v___y_6193_);
if (lean_obj_tag(v___x_6240_) == 0)
{
lean_dec_ref(v___x_6240_);
v_a_6229_ = v___x_6206_;
goto v___jp_6228_;
}
else
{
lean_object* v_a_6241_; lean_object* v___x_6243_; uint8_t v_isShared_6244_; uint8_t v_isSharedCheck_6248_; 
lean_dec(v___x_6227_);
lean_del_object(v___x_6214_);
v_a_6241_ = lean_ctor_get(v___x_6240_, 0);
v_isSharedCheck_6248_ = !lean_is_exclusive(v___x_6240_);
if (v_isSharedCheck_6248_ == 0)
{
v___x_6243_ = v___x_6240_;
v_isShared_6244_ = v_isSharedCheck_6248_;
goto v_resetjp_6242_;
}
else
{
lean_inc(v_a_6241_);
lean_dec(v___x_6240_);
v___x_6243_ = lean_box(0);
v_isShared_6244_ = v_isSharedCheck_6248_;
goto v_resetjp_6242_;
}
v_resetjp_6242_:
{
lean_object* v___x_6246_; 
if (v_isShared_6244_ == 0)
{
v___x_6246_ = v___x_6243_;
goto v_reusejp_6245_;
}
else
{
lean_object* v_reuseFailAlloc_6247_; 
v_reuseFailAlloc_6247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6247_, 0, v_a_6241_);
v___x_6246_ = v_reuseFailAlloc_6247_;
goto v_reusejp_6245_;
}
v_reusejp_6245_:
{
return v___x_6246_;
}
}
}
}
else
{
lean_dec(v_a_6236_);
lean_dec_ref(v___x_6222_);
lean_dec(v_pre_6203_);
lean_dec_ref(v_name_6191_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
v_a_6229_ = v___x_6209_;
goto v___jp_6228_;
}
}
else
{
lean_object* v_a_6249_; lean_object* v___x_6251_; uint8_t v_isShared_6252_; uint8_t v_isSharedCheck_6256_; 
lean_dec(v___x_6227_);
lean_dec_ref(v___x_6222_);
lean_del_object(v___x_6214_);
lean_dec(v_pre_6203_);
lean_dec_ref(v_name_6191_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
v_a_6249_ = lean_ctor_get(v___x_6235_, 0);
v_isSharedCheck_6256_ = !lean_is_exclusive(v___x_6235_);
if (v_isSharedCheck_6256_ == 0)
{
v___x_6251_ = v___x_6235_;
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
else
{
lean_inc(v_a_6249_);
lean_dec(v___x_6235_);
v___x_6251_ = lean_box(0);
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
v_resetjp_6250_:
{
lean_object* v___x_6254_; 
if (v_isShared_6252_ == 0)
{
v___x_6254_ = v___x_6251_;
goto v_reusejp_6253_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_a_6249_);
v___x_6254_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6253_;
}
v_reusejp_6253_:
{
return v___x_6254_;
}
}
}
v___jp_6228_:
{
lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6233_; 
v___x_6230_ = lean_st_ref_get(v___x_6227_);
lean_dec(v___x_6227_);
lean_dec(v___x_6230_);
v___x_6231_ = lean_box(v_a_6229_);
if (v_isShared_6215_ == 0)
{
lean_ctor_set_tag(v___x_6214_, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6231_);
v___x_6233_ = v___x_6214_;
goto v_reusejp_6232_;
}
else
{
lean_object* v_reuseFailAlloc_6234_; 
v_reuseFailAlloc_6234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6234_, 0, v___x_6231_);
v___x_6233_ = v_reuseFailAlloc_6234_;
goto v_reusejp_6232_;
}
v_reusejp_6232_:
{
return v___x_6233_;
}
}
}
}
else
{
lean_dec(v_val_6211_);
lean_dec_ref(v_name_6191_);
lean_dec(v_pre_6203_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v___x_6190_);
goto v___jp_6195_;
}
}
else
{
lean_dec(v___x_6210_);
lean_dec_ref(v_name_6191_);
lean_dec(v_pre_6203_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v___x_6190_);
goto v___jp_6195_;
}
}
}
else
{
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v_name_6191_);
lean_dec(v___x_6190_);
goto v___jp_6199_;
}
v___jp_6195_:
{
uint8_t v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; 
v___x_6196_ = 0;
v___x_6197_ = lean_box(v___x_6196_);
v___x_6198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6197_);
return v___x_6198_;
}
v___jp_6199_:
{
uint8_t v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6200_ = 0;
v___x_6201_ = lean_box(v___x_6200_);
v___x_6202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6202_, 0, v___x_6201_);
return v___x_6202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6258_, lean_object* v_name_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_){
_start:
{
lean_object* v_res_6263_; 
v_res_6263_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6258_, v_name_6259_, v___y_6260_, v___y_6261_);
return v_res_6263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6267_; lean_object* v___x_6268_; 
v___f_6267_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6268_ = l_Lean_registerReservedNameAction(v___f_6267_);
return v___x_6268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6269_){
_start:
{
lean_object* v_res_6270_; 
v_res_6270_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6270_;
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
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
